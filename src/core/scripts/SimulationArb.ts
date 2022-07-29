import { ethers, waffle, network } from 'hardhat'
import { BigNumber, Wallet } from 'ethers'
import { TestERC20 } from '../typechain/TestERC20'
import { SimulationTimeAlgebraPool } from '../typechain/SimulationTimeAlgebraPool'
import { SimulationTimePoolDeployer } from "../typechain/SimulationTimePoolDeployer"
import { SimulationTimeFactory } from '../typechain/SimulationTimeFactory'
import { Quoter } from '../../periphery/typechain/Quoter'
import {
  createPoolFunctions,
  SwapFunction,
  MintFunction,
  FlashFunction,
  SwapToPriceFunction,
} from '../test/shared/utilities'
import { TestAlgebraCallee } from '../typechain/TestAlgebraCallee'

import * as fs from "fs"
import * as path from "path"
import { MockTimeAlgebraPool } from '../typechain/MockTimeAlgebraPool'

import quoterArtifact from '../../periphery/artifacts/contracts/lens/Quoter.sol/Quoter.json';

const DAY = 60*60*24;

let wallet: Wallet
let other: Wallet

let token0: TestERC20
let token1: TestERC20

let pool: SimulationTimeAlgebraPool
let poolUni: SimulationTimeAlgebraPool

let swapTarget: TestAlgebraCallee

const MIN_ALLOWED_SQRT_RATIO = BigNumber.from('4295128739').add(1);
const MAX_ALLOWED_SQRT_RATIO = BigNumber.from('1461446703485210103287273052203988822378723970342').sub(1);

const GAS_PRICE = 40000000000;
const GAS_LIMIT = 1000000;

let swapToLowerPrice: SwapToPriceFunction
let swapToHigherPrice: SwapToPriceFunction
let swapExact0For1: SwapFunction
let swapExact1For0: SwapFunction

let speed: number
let timePassed: number
let currentBlock: number
let numOfBlocks: number
let factory: SimulationTimeFactory

let mint: MintFunction
let flash: FlashFunction

const vaultAddress = '0x1d8b6fA722230153BE08C4Fa4Aa4B4c7cd01A95a'

// ##########  CONFIG SECTION  ##############

const MAX_BLOCKS = 1000; // ignored if 0

const PACK_SIZE = 20000; // how many blocks should be in one pack

const SIMULATE_VIA_PRICES = true; // always try to move price to historically known. If false, just use amounts from events.

const FEE_CONFIGURATION = { // can be changed for different fee behavior
  alpha1: 2900,
  alpha2: 15000 - 3000,
  beta1: 360,
  beta2: 60000,
  gamma1: 59,
  gamma2: 8500,
  volumeBeta: 0,
  volumeGamma: 10,
  baseFee: 100
}

const FEE_UNI_CONFIGURATION = { // can be changed for different fee behavior
  alpha1: 0,
  alpha2: 0,
  beta1: 360,
  beta2: 60000,
  gamma1: 59,
  gamma2: 8500,
  volumeBeta: 0,
  volumeGamma: 10,
  baseFee: 3000
}

// ##########  END OF CONFIG SECTION  ##############

const quoters: Quoter[] = [];

let createPool = async (firstToken: any, secondToken:any, feeConfig: any, signer: any): Promise<SimulationTimeAlgebraPool> => {
    const poolDeployerFactory = await ethers.getContractFactory('SimulationTimePoolDeployer')
    const poolDeployer = (await poolDeployerFactory.deploy()) as SimulationTimePoolDeployer
    const factoryFactory = await ethers.getContractFactory('SimulationTimeFactory')
    factory = (await factoryFactory.deploy(poolDeployer.address, vaultAddress)) as SimulationTimeFactory
    await poolDeployer.setFactory(factory.address);

    const quoterFactory = new ethers.ContractFactory(quoterArtifact.abi, quoterArtifact.bytecode, signer);
    let quoter = (await quoterFactory.deploy(factory.address,  vaultAddress, poolDeployer.address)) as Quoter;
    quoters.push(quoter);
    await factory.setBaseFeeConfiguration(
      feeConfig.alpha1,
      feeConfig.alpha2,
      feeConfig.beta1,
      feeConfig.beta2,
      feeConfig.gamma1,
      feeConfig.gamma2,
      feeConfig.volumeBeta,
      feeConfig.volumeGamma,
      feeConfig.baseFee
    )
  
    const poolFactory = await ethers.getContractFactory('SimulationTimeAlgebraPool')
  
    const tx = await factory.createPool(
      firstToken.address,
      secondToken.address
    )
  
    const receipt = await tx.wait()
    const poolAddress = receipt.events?.[1].args?.pool as string
    return poolFactory.attach(poolAddress) as SimulationTimeAlgebraPool
  }

async function deployTokens() {

  const tokenFactory = await ethers.getContractFactory('TestERC20')
  const tokenA = (await tokenFactory.deploy(BigNumber.from(2).pow(255))) as TestERC20
  const tokenB = (await tokenFactory.deploy(BigNumber.from(2).pow(255))) as TestERC20

  [token0, token1] = [tokenA, tokenB].sort((tokenA, tokenB) =>
    tokenA.address.toLowerCase() < tokenB.address.toLowerCase() ? -1 : 1
  )
}

const Q96 = BigNumber.from(2).pow('96');
const Q96BI = BigInt(Q96.toString());

function _getVirtReserves(price: bigint, liquidity: bigint) {
  let y = price * liquidity / Q96BI;
  let x = liquidity * Q96BI / price;
  return {x, y};
}

const calcArb = (A:any, B:any, C:any, D:any, F0:any, F1:any) => {
  A = Number(A)
  B = Number(B)
  C = Number(C)
  D = Number(D)

  let G_1 = Number(1) - Number(1) * F0 / Number(1000000)
  let G_2 = Number(1) - Number(1) * F1 / Number(1000000)

  let GBD = G_1*(B + D);
  let denom = 2 * GBD**2

  let part1 = 2*A*D*GBD
  let part2 = 2 * denom * (A*B*C*D*G_1*G_2)
  part2 = part2 ** 0.5

  if ( part2 <= part1)
      return 0
  let result = -(part1 - part2) / denom
  let int_result = Math.floor(result)
  return int_result
}

async function doArb(pool1: SimulationTimeAlgebraPool, pool2: SimulationTimeAlgebraPool) {
  let state1 = await pool1.globalState();
  let L1 = (await pool1.liquidity()).toBigInt();
  let state2 = await pool2.globalState();
  let L2 = (await pool2.liquidity()).toBigInt();

  let rA, rB, feeA, feeB, tagA, tagB;
  let uta = state2.price.lt(state1.price);

  if (uta) {
      rA = _getVirtReserves(state2.price.toBigInt(), L2);
      rB = _getVirtReserves(state1.price.toBigInt(), L1);
      feeA = 3000;
      feeB = Number(state1.fee.toString());
  } else {
      rA = _getVirtReserves(state1.price.toBigInt(), L1);
      rB = _getVirtReserves(state2.price.toBigInt(), L2);
      feeA = Number(state1.fee.toString());
      feeB = 3000;
  }

  let maxProfitableAmount;

  uta = !uta;
  maxProfitableAmount = calcArb(rB.x, rB.y, rA.x, rA.y, feeA, feeB);
  console.log('ARB AMOUNT', maxProfitableAmount);
}

async function getOptimalDistribution(amountIn: any, pool1: SimulationTimeAlgebraPool, pool2: SimulationTimeAlgebraPool, zto: boolean) {
  let state1 = await pool1.globalState();
  let L1 = (await pool1.liquidity()).toBigInt();
  let state2 = await pool2.globalState();
  let L2 = (await pool2.liquidity()).toBigInt();


  console.log('L1', L1.toString());
  console.log('L2', L2.toString());
  
  let vR1 = _getVirtReserves(state1.price.toBigInt(), L1);
  let vR2 = _getVirtReserves(state2.price.toBigInt(), L2);

  let gamma1 = Number(1) - Number(state1.fee.toString()) / 1000000;
  let gamma2 = Number(1) - Number(state2.fee.toString()) / 1000000;

  console.log('Gamma1 ', gamma1)
  console.log('Gamma2 ', gamma2)

  let K1, K2;
  if (zto) {
    K1 = (Number(vR1.x) * gamma1);
    K2 = (Number(vR2.x) * gamma2);
  } else {
    K1 = (Number(vR1.y) * gamma1);
    K2 = (Number(vR2.y) * gamma2);
  }


  let omega1 = 1 / gamma1;
  let omega2 = 1 / gamma2;

  let P1sqrt = Number(state1.price.toBigInt()) / Number(Q96BI)
  let P2sqrt = Number(state2.price.toBigInt()) / Number(Q96BI)

  console.log('P1', 1 / (P1sqrt**2 / 10**12))
  console.log('P2', 1 / (P2sqrt**2 / 10**12))

  console.log('dP', 100 * (1 / (P1sqrt**2 / 10**12) -  1 / (P2sqrt**2 / 10**12)) / (1 / (P2sqrt**2 / 10**12)), '%')


  if (!zto) {
    P1sqrt = 1/P1sqrt;
    P2sqrt = 1/P2sqrt;
  }

  let S1 = P1sqrt * (omega1 ** 0.5) * K1 + P2sqrt * (omega2 ** 0.5) * K2;
  let S2 = Number(amountIn.toString()) + omega1 * K1 + omega2 * K2;

  let dx1, dx2;
  if (S2 *  P1sqrt * (omega1 ** 0.5) < S1 * omega1) {
    dx1 = 0;
    dx2 = Number(amountIn.toString());
  } else {
    if (S2 *  P2sqrt * (omega2 ** 0.5) < S1 * omega2) {
      dx1 = Number(amountIn.toString());
      dx2 = 0;
    } else {
      dx1 = (S2*P1sqrt*(omega1 ** 0.5) - S1*omega1) * K1 / (S1);
      dx2 = (S2*P2sqrt*(omega2 ** 0.5) - S1*omega2) * K2 / (S1);
    }
  }

  console.log('AmountIn: ', zto ? (amountIn / 10**6).toFixed(4) + '$': (amountIn / 10**18).toFixed(4) + ' ETH');
  console.log('dx1: ', (100*dx1/(Number(amountIn.toString()))).toFixed(2) );
  console.log('dx2: ', (100*dx2/(Number(amountIn.toString()))).toFixed(2) );

  let dx1_bn, dx2_bn;
  dx1_bn = BigNumber.from(Math.floor(dx1).toString());
  dx2_bn = BigNumber.from(amountIn.toString()).sub(dx1_bn);

  const quoteDistr = async (tokenIn: string, tokenOut: string, x1: BigNumber, x2: BigNumber): Promise<BigNumber> => {
    let out1, out2;
    if (x1.gt(0)) 
     out1 = (await quoters[0].callStatic.quoteExactInputSingle(tokenIn, tokenOut, x1, 0))[0];
    else out1 = BigNumber.from(0);
    if (x2.gt(0)) 
     out2 = (await quoters[1].callStatic.quoteExactInputSingle(tokenIn, tokenOut, x2, 0))[0];
    else out2 = BigNumber.from(0);
    return out1.add(out2);
  }

  let out;
  if (zto) {
    out = await quoteDistr(token0.address, token1.address, dx1_bn, dx2_bn);
    console.log('AmountOut:', Number(out.toString()) / 10**18, 'ETH')
  } else {
    out = await quoteDistr(token1.address, token0.address, dx1_bn, dx2_bn);
    console.log('AmountOut:', Number(out.toString()) / 10**6, '$')
  }

  let perc1, perc2;
  perc1 = 100 * dx1 / amountIn;
  perc2 = 100 * dx2 / amountIn;
  
  let out_lower = BigNumber.from(0);
  if (perc1 < 100) {
    let perc1_low = Math.min(perc1 + 2, 100);

    let dx1_bn_low = BigNumber.from(Math.floor((amountIn / 100) * perc1_low).toString());
    let dx2_bn_low = BigNumber.from(amountIn.toString()).sub(dx1_bn_low);

    if (zto) {
      out_lower = await quoteDistr(token0.address, token1.address, dx1_bn_low, dx2_bn_low);
      console.log('AmountOut lower:', Number(out_lower.toString()) / 10**18, 'ETH')
    } else {
      out_lower = await quoteDistr(token1.address, token0.address, dx1_bn_low, dx2_bn_low);
      console.log('AmountOut lower:', Number(out_lower.toString()) / 10**6, '$')
    }
  }

  let out_upper = BigNumber.from(0);
  if (perc1 > 0) {
    let perc1_low = Math.max(perc1 - 2, 0);

    let dx1_bn_low = BigNumber.from(Math.floor((amountIn / 100) * perc1_low).toString());
    let dx2_bn_low = BigNumber.from(amountIn.toString()).sub(dx1_bn_low);

    if (zto) {
      out_upper = await quoteDistr(token0.address, token1.address, dx1_bn_low, dx2_bn_low);
      console.log('AmountOut upper:', Number(out_upper.toString()) / 10**18, 'ETH')
    } else {
      out_upper = await quoteDistr(token1.address, token0.address, dx1_bn_low, dx2_bn_low);
      console.log('AmountOut upper:', Number(out_upper.toString()) / 10**6, '$')
    }
  }

  //console.log('Am > am_low', out.gt(out_lower));
  //console.log('Am > am_up', out.gt(out_upper));

  if (out.lt(out_lower)) {
    let perc1_low = Math.min(perc1 + 2, 100);

    dx1 = Math.floor((amountIn / 100) * perc1_low);
    dx2 = amountIn - dx1;
  }

  if (out.lt(out_upper)) {
    let perc1_low = Math.max(perc1 - 2, 0);

    dx1 = Math.floor((amountIn / 100) * perc1_low);
    dx2 = amountIn - dx1;
  }

  return( { dx1, dx2 } )
}


async function main() {
  const [wallet2, other2] = await (ethers as any).getSigners()
  wallet = wallet2;
  other = other2;
  if (network.name == "hardhat") {
    await network.provider.send("hardhat_setBalance", [
      "0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266",
      "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0000000000000000",
    ]);
  }
  await deployTokens();
  const blocks = JSON.parse(fs.readFileSync(path.resolve(__dirname, 'AllBlocks_timestamped.json')).toString());

  let fees: any[] = [];
  let volats: any[] = [];
  let volumesPerLiq: any[] = [];
  let ticks: any[] = [];
  let uniTicks: any[] = [];
  let timestamps: any[] = [];
  let globalFeeGrowth0: any[] = [];
  let globalFeeGrowth1: any[] = [];

  pool = await createPool(token0, token1, FEE_CONFIGURATION, wallet);
  poolUni = await createPool(token0, token1, FEE_UNI_CONFIGURATION, wallet);

  const calleeContractFactory = await ethers.getContractFactory('TestAlgebraCallee')
  swapTarget = (await calleeContractFactory.deploy()) as TestAlgebraCallee

  ({
    swapToLowerPrice,
    swapToHigherPrice,
    swapExact0For1,
    swapExact1For0,
    mint,
    flash,
  } = createPoolFunctions({
    token0,
    token1,
    swapTarget,
    pool: pool as MockTimeAlgebraPool,
  }))

  await token0.approve(swapTarget.address, BigNumber.from(2).pow(256).sub(1))
  await token1.approve(swapTarget.address, BigNumber.from(2).pow(256).sub(1))

  await pool.advanceTime(86400000);
  await poolUni.advanceTime(86400000);
  let initialized = false;
  let lastTimestamp = 0;
  timePassed = 0;
  let interval = setInterval(() => {
    timePassed += 15
    speed = currentBlock / timePassed;
  }, 15000)

  let lastTick = (await pool.globalState()).tick;
  console.log('Used wallet: ', wallet.address);
  
  //await network.provider.send("evm_setAutomine", [false]);

  //let nonce = await wallet.getTransactionCount();

  if (MAX_BLOCKS > 0) numOfBlocks = Math.min(MAX_BLOCKS, blocks.length);
  else numOfBlocks =  blocks.length;
  console.log('Number of blocks: ', blocks.length)
  let currentPack = 0;
  
  for (let blockNum = 0; blockNum < numOfBlocks; blockNum++) {
    let block = blocks.shift();
    if (!block[0].timestamp) {
      continue;
    }
    if (lastTimestamp == 0) {
      lastTimestamp = block[0].timestamp
    } else {
      if (lastTimestamp !== block[0].timestamp) {
        await pool.advanceTime(BigNumber.from(block[0].timestamp).sub(BigNumber.from(lastTimestamp)), {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE})
        await poolUni.advanceTime(BigNumber.from(block[0].timestamp).sub(BigNumber.from(lastTimestamp)), {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE})
        lastTimestamp = block[0].timestamp
      }
    }
    for (let evNum = 0; evNum < block.length; evNum++) {
        let event = block[evNum]
        let values = event.returnValues
        switch(event.event) {
          case "Initialize":
            if (!initialized) {
              await pool.initialize(BigNumber.from(values.price), {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              await poolUni.initialize(BigNumber.from(values.price), {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              initialized = true;
            }
            break;
          case "Mint":
            if (values.amount < 0) console.log('ERR: MINT', values.amount);
            await swapTarget.mint(pool.address, wallet.address, values.bottomTick, values.topTick, values.amount, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
            await swapTarget.mint(poolUni.address, wallet.address, values.bottomTick, values.topTick, values.amount, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
            break;
          case "Burn":
            if (values.amount < 0) console.log('ERR: BURN', values.amount);
            await pool.burn(values.bottomTick, values.topTick, values.amount, { maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
            await poolUni.burn(values.bottomTick, values.topTick, values.amount, { maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
            break;
          case "Swap":
            let ZtO = values.amount0 > 0;
            if (values.amount0 == 0 && values.amount1 == 0) {
              console.log('INVALID INPUT DATA: ZERO SWAP');
              continue;
            }
            if (ZtO) {
              if (values.amount1 > 0) {
                console.log('ERR: SWAP 0 -> 1', values.amount0, values.amount1);
                continue;
              }
            } else {
              if (values.amount1 < 0) console.log('ERR: SWAP 1 -> 0', values.amount1, values.amount0);
              if (values.amount1 == 0)  {
                console.error('INVALID INPUT DATA: SWAP 1 -> 0, ZERO INPUT AMOUNT')
                continue;
              }
            }
            
            console.log('Swap')
            if (ZtO) {
              let origInput = BigInt(values.amount0) * BigInt(2);
              console.log('ZtO');
              console.log('Hist price: ', 1 / ((Number(values.price.toString()) / Number(Q96BI))**2 / 10**12))
              let prop = await getOptimalDistribution(Number(origInput), pool, poolUni, true);
              
              if (prop.dx1 > 0) await swapTarget.swapExact0For1(pool.address, Math.floor(prop.dx1).toString(), wallet.address, MIN_ALLOWED_SQRT_RATIO, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              if (prop.dx2 > 0) {
                let amount = Number(origInput) - Math.floor(prop.dx1);
                await swapTarget.swapExact0For1(poolUni.address, amount.toString(), wallet.address, MIN_ALLOWED_SQRT_RATIO, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              }

              //  await swapTarget.swapToLowerSqrtPrice(pool.address, values.price, wallet.address, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              //else await swapTarget.swapExact0For1(pool.address, values.amount0, wallet.address, MIN_ALLOWED_SQRT_RATIO, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
            } else {
              console.log('OtZ');
              console.log('Hist price: ', 1 / ((Number(values.price.toString()) / Number(Q96BI))**2 / 10**12))
              let origInput = BigInt(values.amount1) * BigInt(2);
              let prop = await getOptimalDistribution(Number(origInput), pool, poolUni, false);

              if (prop.dx1 > 0) await swapTarget.swapExact1For0(pool.address, Math.floor(prop.dx1).toString(), wallet.address, MAX_ALLOWED_SQRT_RATIO, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              if (prop.dx2 > 0) {
                let amount = Number(origInput) - Math.floor(prop.dx1);
                await swapTarget.swapExact1For0(poolUni.address, amount.toString(), wallet.address, MAX_ALLOWED_SQRT_RATIO, {maxFeePerGas: GAS_PRICE, maxPriorityFeePerGas: GAS_PRICE});
              } 
            }
            lastTick = values.tick;
            break;
        }
    }
    //await network.provider.send("evm_mine", []);
    await doArb(pool, poolUni);
    let stats;
    try {
      stats = await getStatistics(DAY);
    } catch(e) {
      let now = await pool.getTimepoints([BigNumber.from(0)]);
      stats = [now.volatilityCumulatives[0].div(BigNumber.from(DAY)), 
      now.volumePerAvgLiquiditys[0],
      now.secondsPerLiquidityCumulatives[0]]
    }

    let packNumber = Math.floor(blockNum / PACK_SIZE);
    if (packNumber !== currentPack) {
      let res = {
        fees,
        volats,
        volumesPerLiq,
        ticks,
        timestamps,
        uniTicks,
        globalFeeGrowth0,
        globalFeeGrowth1
      }
      fs.writeFileSync(path.resolve(__dirname, `results_${currentPack}.json`), JSON.stringify(res));
      currentPack = packNumber;
      fees = [];
      volats = [];
      volumesPerLiq = [];
      ticks = [];
      uniTicks = [];
      timestamps = [];
      globalFeeGrowth0 = [];
      globalFeeGrowth1 = [];
    }

    let state = await pool.globalState();
    let fee = state.fee;
    fees.push(fee)
    volats.push(stats[0].toString())
    volumesPerLiq.push(stats[1].toString())
    let tick = state.tick
    ticks.push(tick)
    timestamps.push(block[0].timestamp)
    uniTicks.push(lastTick)
    globalFeeGrowth0.push(Number(await pool.totalFeeGrowth0Token()));
    globalFeeGrowth1.push(Number(await pool.totalFeeGrowth1Token()));
    //console.log('===========================================');
    //console.log('\n');
    currentBlock = blockNum;
    printProgress((100*(blockNum/numOfBlocks)).toFixed(2), timeConverter(block[0].timestamp), fee, stats[0].toString())
  }

  if (currentPack != Math.ceil(numOfBlocks/PACK_SIZE)) {
    let res = {
      fees,
      volats,
      volumesPerLiq,
      ticks,
      timestamps,
      uniTicks,
      globalFeeGrowth0,
      globalFeeGrowth1
    }
    fs.writeFileSync(path.resolve(__dirname, `results_${currentPack}.json`), JSON.stringify(res));
  }
  clearInterval(interval);
}


async function getStatistics(time: number) {
  let points = await pool.getTimepoints([BigNumber.from(0), BigNumber.from(time)]);
  return [(points.volatilityCumulatives[0].sub(points.volatilityCumulatives[1]).div(BigNumber.from(DAY))).toString(), 
  (points.volumePerAvgLiquiditys[0].sub(points.volumePerAvgLiquiditys[1])).toString(),
  (points.secondsPerLiquidityCumulatives[0].sub(points.secondsPerLiquidityCumulatives[1])).toString(),
  time]
  
}

function timeConverter(UNIX_timestamp: number){
  var a = new Date(UNIX_timestamp * 1000);
  var months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
  var year = a.getFullYear();
  var month = months[a.getMonth()];
  var date = a.getDate().toString();
  if (date.length == 1) date = '0' + date;
  var hour = a.getHours().toString();
  if (hour.length == 1) hour = '0' + hour;
  var min = a.getMinutes().toString();
  if (min.length == 1) min = '0' + min;
  var sec = (a.getSeconds()).toString();
  if (sec.length == 1) sec = '0' + sec;
  var time = date + ' ' + month + ' ' + year + ' ' + hour + ':' + min + ':' + sec ;
  return time;
}

function printProgress(progress: any, date: any, fee: any, volat: any){
  let time = ((numOfBlocks - currentBlock)/speed);
  let hours = Math.floor(time / (60*60)).toString();
  if (hours.length == 1) hours = '0' + hours;
  let minutes = Math.floor((time % (60*60))/60).toString();
  if (minutes.length == 1) minutes = '0' + minutes;
  let secs = Math.floor((time % (60*60))%60).toString();
  if (secs.length == 1) secs = '0' + secs;

  process.stdout.clearLine(0);
  process.stdout.cursorTo(0);
  process.stdout.write(progress + '%       '+ date  + '         Fee: ' + fee + '        Time remaining: ' + hours + ':'+minutes+':'+secs  + '     Volat: ' + (volat / 15).toFixed(0) );
}

main().then()