import { ethers } from 'hardhat'
import { BigNumber, Wallet } from 'ethers'
import { loadFixture } from '@nomicfoundation/hardhat-network-helpers'
import { TestERC20 } from '../../typechain'
import { algebraFixture, mintPosition, AlgebraFixtureType } from '../shared/fixtures'
import {
  expect,
  getMaxTick,
  getMinTick,
  FeeAmount,
  TICK_SPACINGS,
  blockTimestamp,
  BN,
  BNe,
  BNe18,
  snapshotGasCost,
  ActorFixture,
  makeTimestamps,
  maxGas,
  days
} from '../shared'
import { provider } from '../shared/provider'
import { HelperCommands, ERC20Helper, incentiveResultToFarmAdapter } from '../helpers'
import { ContractParams } from '../../types/contractParams'
import { createTimeMachine } from '../shared/time'
import { HelperTypes } from '../helpers/types'

const LIMIT_FARMING = true;
const ETERNAL_FARMING = false;

describe('unit/Farms', () => {
  let actors: ActorFixture;
  let lpUser0: Wallet
  let incentiveCreator: Wallet
  const amountDesired = BNe18(10)
  const totalReward = BNe18(100)
  const bonusReward = BNe18(100)
  const erc20Helper = new ERC20Helper()
  const Time = createTimeMachine(provider)
  let helpers: HelperCommands
  let context: AlgebraFixtureType
  let timestamps: ContractParams.Timestamps
  let tokenId: string
  let L2tokenId: string

  before(async () => {
    const wallets = (await ethers.getSigners() as any) as Wallet[];
    actors = new ActorFixture(wallets, provider)
    lpUser0 = actors.lpUser0();
    incentiveCreator = actors.incentiveCreator();
  })

  beforeEach('create fixture loader', async () => {
    context = await loadFixture(algebraFixture)
    helpers = HelperCommands.fromTestContext(context, actors, provider)
  })

  describe('#enterFarming', () => {
    let incentiveId: string
    let incentiveArgs: HelperTypes.CreateIncentive.Args
    let subject: (L2TokenId: string, _actor: Wallet) => Promise<any>

    beforeEach(async () => {
      
      context = await loadFixture(algebraFixture)
      helpers = HelperCommands.fromTestContext(context, actors, provider)
      /** We will be doing a lot of time-testing here, so leave some room between
        and when the incentive starts */
      timestamps = makeTimestamps(1_000 + (await blockTimestamp()))
      await erc20Helper.ensureBalancesAndApprovals(
        lpUser0,
        [context.token0, context.token1],
        amountDesired,
        context.nft.address
      )

      tokenId = await mintPosition(context.nft.connect(lpUser0), {
        token0: context.token0.address,
        token1: context.token1.address,
        fee: FeeAmount.MEDIUM,
        tickLower: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
        tickUpper: getMaxTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
        recipient: lpUser0.address,
        amount0Desired: amountDesired,
        amount1Desired: amountDesired,
        amount0Min: 0,
        amount1Min: 0,
        deadline: (await blockTimestamp()) + 1000,
      })

      await context.farmingCenter.connect(lpUser0).lockToken(tokenId)

      incentiveArgs = {
        rewardToken: context.rewardToken,
        bonusRewardToken: context.bonusRewardToken,
        totalReward,
        bonusReward,
        poolAddress: context.poolObj.address,
        ...timestamps,
      }

      incentiveId = await helpers.getIncentiveId(await helpers.createIncentiveFlow(incentiveArgs))

      subject = (L2TokenId: string, _actor: Wallet) =>
        context.farmingCenter.connect(_actor).enterFarming(
          {
            
            pool: context.pool01,
            rewardToken: context.rewardToken.address,
            bonusRewardToken: context.bonusRewardToken.address,
            ...timestamps,
          },
          L2TokenId,
          0,
          LIMIT_FARMING
        )
    })

    describe('works and', () => {
      // Make sure the incentive has started
      // beforeEach(async () => {
      //   await Time.set(timestamps.startTime + 100)
      // })

      it('emits the farm event', async () => {
        const { liquidity } = await context.nft.positions(tokenId)
        await expect(subject(tokenId, lpUser0))
          .to.emit(context.farming, 'FarmEntered')
          .withArgs(tokenId, incentiveId, liquidity, 0)
      })

      it('sets the farm struct properly', async () => {
        const liquidity = (await context.nft.positions(tokenId)).liquidity

        const farmBefore = await context.farming.farms(tokenId, incentiveId)
        const depositFarmsBefore = (await context.farmingCenter.deposits(tokenId)).numberOfFarms
        await subject(tokenId, lpUser0)
        const farmAfter = await context.farming.farms(tokenId, incentiveId)
        const depositFarmsAfter = (await context.farmingCenter.deposits(tokenId)).numberOfFarms

        expect(farmBefore.liquidity).to.eq(0)
        expect(depositFarmsBefore).to.eq(0)
        expect(farmAfter.liquidity).to.eq(liquidity)
        expect(depositFarmsAfter).to.eq(1)
      })

      it('increments the number of farms on the deposit', async () => {
        const nFarmsBefore: number = (await context.farmingCenter.deposits(tokenId)).numberOfFarms
        await subject(tokenId, lpUser0)

        expect((await context.farmingCenter.deposits(tokenId)).numberOfFarms).to.eq(nFarmsBefore + 1)
      })

      xit('has gas cost [ @skip-on-coverage ]', async () => await snapshotGasCost(subject(tokenId, lpUser0)))
    })

    describe('fails when', () => {
      it('deposit is already farmed in the incentive', async () => {
        //await Time.set(timestamps.startTime + 500)
        await subject(tokenId, lpUser0)
        await expect(subject(tokenId, lpUser0)).to.be.revertedWith('token already farmed')
      })

      it('you are not the owner of the deposit', async () => {
        //await Time.set(timestamps.startTime + 500)
        // lpUser2 calls, we're using lpUser0 elsewhere.
        await expect(subject(tokenId, actors.lpUser2())).to.be.revertedWith(
          'not owner'
        )
      })

      it('has 0 liquidity in the position', async () => {
        //await Time.set(timestamps.startTime + 500)
        await erc20Helper.ensureBalancesAndApprovals(
          lpUser0,
          [context.token0, context.token1],
          amountDesired,
          context.nft.address
        )

        const tokenId2 = await mintPosition(context.nft.connect(lpUser0), {
          token0: context.token0.address,
          token1: context.token1.address,
          fee: FeeAmount.MEDIUM,
          tickLower: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
          tickUpper: getMaxTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
          recipient: lpUser0.address,
          amount0Desired: amountDesired,
          amount1Desired: amountDesired,
          amount0Min: 0,
          amount1Min: 0,
          deadline: (await blockTimestamp()) + 1000,
        })

        await context.nft.connect(lpUser0).decreaseLiquidity({
          tokenId: tokenId2,
          liquidity: (await context.nft.positions(tokenId2)).liquidity,
          amount0Min: 0,
          amount1Min: 0,
          deadline: (await blockTimestamp()) + 1_000,
        })

        await context.farmingCenter.connect(lpUser0).lockToken(tokenId2)

        await expect(subject(tokenId2, lpUser0)).to.be.revertedWith(
          'cannot farm token with 0 liquidity'
        )
      })

      it('token id is for a different pool than the incentive', async () => {
        const incentive2 = await helpers.createIncentiveFlow({
          ...incentiveArgs,
          poolAddress: context.pool12,
        })
        const { tokenId: otherTokenId } = await helpers.mintFlow({
          lp: lpUser0,
          tokens: [context.token1, context.rewardToken],
        })

        // await Time.setAndMine(incentive2.startTime + 1)

        await helpers.depositFlow({
          lp: lpUser0,
          tokenId: otherTokenId,
        })

        await expect(
          context.farmingCenter.connect(lpUser0).enterFarming(
            {
              
              pool: context.pool01,
              rewardToken: context.rewardToken.address,
              bonusRewardToken: context.bonusRewardToken.address,
              ...timestamps,
            },
            otherTokenId,
            0,
            LIMIT_FARMING
          )
        ).to.be.revertedWith('invalid pool for token')
      })

      it('incentive key does not exist', async () => {
        // await Time.setAndMine(timestamps.startTime + 20)

        await expect(
          context.farmingCenter.connect(lpUser0).enterFarming(
            {
              
              pool: context.pool01,
              rewardToken: context.rewardToken.address,
              bonusRewardToken: context.bonusRewardToken.address,
              ...timestamps,
              startTime: timestamps.startTime + 10,
            },
            tokenId,
            0,
            LIMIT_FARMING
          )
        ).to.be.revertedWith('non-existent incentive')
      })

      it('is past the end time', async () => {
        await Time.set(timestamps.endTime + 100)
        await expect(subject(tokenId, lpUser0)).to.be.revertedWith('incentive has already started')
      })

      it('is after the start time', async () => {
        if (timestamps.startTime < (await blockTimestamp())) {
          throw new Error('no good')
        }
        await Time.set(timestamps.startTime + 2)
        await expect(subject(tokenId, lpUser0)).to.be.revertedWith('incentive has already started')
      })
    })
  })

  xdescribe('swap gas [ @skip-on-coverage ]', async () => {
    it('3 swaps', async () => {
      timestamps = makeTimestamps((await blockTimestamp()) + 1_000)

      const mintResult = await helpers.mintFlow({
        lp: lpUser0,
        tokens: [context.token0, context.token1],
      })
      tokenId = mintResult.tokenId

      await context.farmingCenter.connect(lpUser0).lockToken(tokenId)

      let farmIncentiveKey = {
        
        rewardToken: context.rewardToken.address,
        bonusRewardToken: context.bonusRewardToken.address,
        pool: context.pool01,
        ...timestamps,
      }

      let incentiveId = await helpers.getIncentiveId(
        await helpers.createIncentiveFlow({
          rewardToken: context.rewardToken,
          bonusRewardToken: context.bonusRewardToken,
          totalReward,
          bonusReward,
          poolAddress: context.poolObj.address,
          ...timestamps,
        })
      )

      // await Time.set(timestamps.startTime)
      await context.farmingCenter.connect(lpUser0).enterFarming(farmIncentiveKey, tokenId, 0, LIMIT_FARMING)
      await context.farming.farms(tokenId, incentiveId)

      const pool = context.poolObj.connect(actors.lpUser0())

      Time.set(timestamps.startTime + 10)
      //await provider.send('evm_mine', [timestamps.startTime + 100])
      const trader = actors.traderUser0()
      await snapshotGasCost(helpers.makeSwapGasCHeckFlow({
          trader,
          direction: 'up',
          desiredValue: 10,
      }))
      await snapshotGasCost(helpers.makeSwapGasCHeckFlow({
        trader,
        direction: 'up',
        desiredValue: 10,
      }))
      await snapshotGasCost(helpers.makeSwapGasCHeckFlow({
        trader,
        direction: 'up',
        desiredValue: 10,
      }))
    })
  })

  describe('permissioned actions', () => {
    it('#setIncentiveMaker', async() => {
      await expect(context.farming.connect(actors.farmingDeployer()).setIncentiveMaker(actors.lpUser1().address))
      .to.emit(context.farming, 'IncentiveMaker')
      .withArgs(actors.lpUser1().address)

      await expect(context.farming.connect(actors.farmingDeployer()).setIncentiveMaker(actors.lpUser1().address)).to.be.reverted;
    })

    it('#setFarmingCenterAddress', async() => {
      await expect(context.farming.connect(actors.farmingDeployer()).setFarmingCenterAddress(actors.lpUser1().address))
      .to.emit(context.farming, 'FarmingCenter')
      .withArgs(actors.lpUser1().address)

      await expect(context.farming.connect(actors.farmingDeployer()).setFarmingCenterAddress(actors.lpUser1().address)).to.be.reverted;
    })

    it('onlyOwner fails if not owner', async() => {
      await expect(context.farming.connect(actors.lpUser1()).setIncentiveMaker(actors.lpUser1().address)).to.be.reverted;
      await expect(context.farming.connect(actors.lpUser1()).setFarmingCenterAddress(actors.lpUser1().address)).to.be.reverted;
    })

    it('onlyIncentiveMaker fails if not incentive maker', async() => {
      let timestamps = makeTimestamps((await blockTimestamp()) + 1_000);
      let farmIncentiveKey = {
        
        rewardToken: context.rewardToken.address,
        bonusRewardToken: context.bonusRewardToken.address,
        pool: context.pool01,
        ...timestamps,
      }
      let tiers = {
        tokenAmountForTier1: 0,
        tokenAmountForTier2: 0,
        tokenAmountForTier3: 0,
        tier1Multiplier: 10000,
        tier2Multiplier: 10000,
        tier3Multiplier: 10000,
      }
      let params = {
        reward: 10000,
        bonusReward: 10000,
        minimalPositionWidth: 0,
        multiplierToken: context.rewardToken.address,
        enterStartTime: timestamps.startTime,
      }

      await expect(context.farming.connect(actors.lpUser1()).createLimitFarming(
        farmIncentiveKey,
        tiers,
        params)
      ).to.be.reverted;

      let incentiveId = await helpers.getIncentiveId(
        await helpers.createIncentiveFlow({
          rewardToken: context.rewardToken,
          bonusRewardToken: context.bonusRewardToken,
          totalReward,
          bonusReward,
          poolAddress: context.poolObj.address,
          ...timestamps,
        })
      )

      await expect(context.farming.connect(actors.lpUser1()).addRewards(
        farmIncentiveKey,
        20000,
        20000)
      ).to.be.reverted;

      await expect(context.farming.connect(actors.lpUser1()).decreaseRewardsAmount(
        farmIncentiveKey,
        20000,
        20000)
      ).to.be.reverted;
    })

    it('onlyFarmingCenter fails if not fc', async() => {
      let timestamps = makeTimestamps((await blockTimestamp()) + 1_000);
      let farmIncentiveKey = {
        
        rewardToken: context.rewardToken.address,
        bonusRewardToken: context.bonusRewardToken.address,
        pool: context.pool01,
        ...timestamps,
      }

      let incentiveId = await helpers.getIncentiveId(
        await helpers.createIncentiveFlow({
          rewardToken: context.rewardToken,
          bonusRewardToken: context.bonusRewardToken,
          totalReward,
          bonusReward,
          poolAddress: context.poolObj.address,
          ...timestamps,
        })
      )

      await expect(context.farming.connect(actors.lpUser1()).enterFarming(
        farmIncentiveKey,
        0,
        20000)
      ).to.be.reverted;

      await expect(context.farming.connect(actors.lpUser1()).exitFarming(
        farmIncentiveKey,
        0,
        actors.lpUser1().address)
      ).to.be.reverted;
    })
  })

  describe('#getRewardInfo', () => {
    let incentiveId: string
    let farmIncentiveKey: ContractParams.IncentiveKey

    beforeEach('set up incentive and farm', async () => {
      timestamps = makeTimestamps((await blockTimestamp()) + 1_000)

      const mintResult = await helpers.mintFlow({
        lp: lpUser0,
        tokens: [context.token0, context.token1],
      })
      tokenId = mintResult.tokenId

      await context.farmingCenter.connect(lpUser0).lockToken(tokenId)

      farmIncentiveKey = {
        
        rewardToken: context.rewardToken.address,
        bonusRewardToken: context.bonusRewardToken.address,
        pool: context.pool01,
        ...timestamps,
      }

      incentiveId = await helpers.getIncentiveId(
        await helpers.createIncentiveFlow({
          rewardToken: context.rewardToken,
          bonusRewardToken: context.bonusRewardToken,
          totalReward,
          bonusReward,
          poolAddress: context.poolObj.address,
          ...timestamps,
        })
      )

      // await Time.set(timestamps.startTime)
      await context.farmingCenter.connect(lpUser0).enterFarming(farmIncentiveKey, tokenId, 0, LIMIT_FARMING)
      await context.farming.farms(tokenId, incentiveId)
    })

    it('returns correct rewardAmount and secondsInsideX128 for the position', async () => {
      const pool = context.poolObj.connect(actors.lpUser0())

      Time.set(timestamps.startTime + 10)
      //await provider.send('evm_mine', [timestamps.startTime + 100])
      const trader = actors.traderUser0()
      await helpers.makeTickGoFlow({
          trader,
          direction: 'up',
          desiredValue: 10,
      })

      Time.set(timestamps.endTime - 10)

      await helpers.makeTickGoFlow({
          trader,
          direction: 'up',
          desiredValue: 100,
      })

      Time.set(timestamps.endTime + 10)

      const rewardInfo = await context.farming.connect(lpUser0).getRewardInfo(farmIncentiveKey, tokenId)

      const { tickLower, tickUpper } = await context.nft.positions(tokenId)
      const { innerSecondsSpentPerLiquidity } = await pool.getInnerCumulatives(tickLower, tickUpper)
      const farm = await context.farming.farms(tokenId, incentiveId)

      const expectedSecondsInPeriod = innerSecondsSpentPerLiquidity
        .mul(farm.liquidity)

      // @ts-ignore
      expect(rewardInfo.reward).to.be.closeTo(BNe(1, 20),  BN('809939148073022313'))
      //expect(rewardInfo.secondsInsideX128).to.equal(expectedSecondsInPeriod)
    })

    it('reverts if farm does not exist', async () => {
      // await Time.setAndMine(timestamps.endTime + 1)

      await expect(context.farming.connect(lpUser0).getRewardInfo(farmIncentiveKey, '100')).to.be.revertedWith(
        'farm does not exist'
      )
    })
  })

  describe('#claimReward', () => {
    let createIncentiveResult: HelperTypes.CreateIncentive.Result
    let subject: (token: string, to: string, amount: BigNumber) => Promise<any>
    // The amount the user should be able to claim
    let claimable: BigNumber

    beforeEach('setup', async () => {
      timestamps = makeTimestamps(await blockTimestamp())
      const tokensToFarm = [context.token0, context.token1] as [TestERC20, TestERC20]

      await erc20Helper.ensureBalancesAndApprovals(lpUser0, tokensToFarm, amountDesired, context.nft.address)

      createIncentiveResult = await helpers.createIncentiveFlow({
        rewardToken: context.rewardToken,
        bonusRewardToken: context.bonusRewardToken,
        totalReward,
        bonusReward,
        poolAddress: context.poolObj.address,
        ...timestamps,
      })
      //
      // await Time.setAndMine(timestamps.startTime + 1)

      const mintResult = await helpers.mintDepositFarmFlow({
        lp: lpUser0,
        tokensToFarm,
        ticks: [getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]), getMaxTick(TICK_SPACINGS[FeeAmount.MEDIUM])],
        amountsToFarm: [amountDesired, amountDesired],
        createIncentiveResult,
      })
      tokenId = mintResult.tokenId

      await Time.setAndMine(timestamps.endTime + 10)
      await context.farmingCenter.connect(lpUser0).exitFarming(
        {
          
          rewardToken: context.rewardToken.address,
          bonusRewardToken: context.bonusRewardToken.address,
          pool: context.pool01,
          ...timestamps,
        },
        tokenId,
        LIMIT_FARMING
      )

      claimable = await context.farming.rewards(lpUser0.address, context.rewardToken.address)

      subject = (_token: string, _to: string, _amount: BigNumber) =>
        context.farming.connect(lpUser0).claimReward(_token, _to, _amount)
    })

    describe('when requesting the full amount', () => {
      it('emits RewardClaimed event', async () => {
        const { rewardToken } = context
        claimable = await context.farming.rewards(lpUser0.address, rewardToken.address)
        await expect(subject(rewardToken.address, lpUser0.address, BN('0')))
          .to.emit(context.farming, 'RewardClaimed')
          .withArgs(lpUser0.address, claimable, context.rewardToken.address, lpUser0.address)
      })

      it('transfers the correct reward amount to destination address', async () => {
        const { rewardToken } = context
        claimable = await context.farming.rewards(lpUser0.address, rewardToken.address)
        const balance = await rewardToken.balanceOf(lpUser0.address)
        await subject(rewardToken.address, lpUser0.address, BN('0'))
        expect(await rewardToken.balanceOf(lpUser0.address)).to.equal(balance.add(claimable))
      })

      it('sets the claimed reward amount to zero', async () => {
        const { rewardToken } = context
        expect(await context.farming.rewards(lpUser0.address, rewardToken.address)).to.not.equal(0)

        await subject(rewardToken.address, lpUser0.address, BN('0'))

        expect(await context.farming.rewards(lpUser0.address, rewardToken.address)).to.equal(0)
      })

      xit('has gas cost [ @skip-on-coverage ]', async () =>
        await snapshotGasCost(subject(context.rewardToken.address, lpUser0.address, BN('0'))))

      it('returns their claimable amount', async () => {
        const { rewardToken, farming } = context
        const amountBefore = await rewardToken.balanceOf(lpUser0.address)
        await subject(rewardToken.address, lpUser0.address, BN('0'))
        expect(await farming.rewards(lpUser0.address, rewardToken.address)).to.eq(BN('0'))
        expect(await rewardToken.balanceOf(lpUser0.address)).to.eq(amountBefore.add(claimable))
      })
    })

    describe('when requesting a nonzero amount', () => {
      it('emits RewardClaimed event', async () => {
        const { rewardToken } = context
        await expect(subject(rewardToken.address, lpUser0.address, claimable))
          .to.emit(context.farming, 'RewardClaimed')
          .withArgs(lpUser0.address, claimable, context.rewardToken.address, lpUser0.address)
      })

      it('transfers the correct reward amount to destination address', async () => {
        const { rewardToken } = context
        claimable = await context.farming.rewards(lpUser0.address, rewardToken.address)
        const balance = await rewardToken.balanceOf(lpUser0.address)
        await subject(rewardToken.address, lpUser0.address, claimable)
        expect(await rewardToken.balanceOf(lpUser0.address)).to.equal(balance.add(claimable))
      })

      it('sets the claimed reward amount to the correct amount', async () => {
        const { rewardToken, farming } = context
        const initialRewardBalance = await farming.rewards(lpUser0.address, rewardToken.address)
        expect(initialRewardBalance).to.not.equal(BN('0'))

        const partialClaim = initialRewardBalance.div(BN('3'))
        await subject(rewardToken.address, lpUser0.address, partialClaim)

        expect(await farming.rewards(lpUser0.address, rewardToken.address)).to.eq(initialRewardBalance.sub(partialClaim))
      })

      describe('when user claims more than they have', () => {
        it('only transfers what they have', async () => {
          const { rewardToken, farming } = context
          const amountBefore = await rewardToken.balanceOf(lpUser0.address)
          await subject(rewardToken.address, lpUser0.address, claimable.mul(BN('3')))
          expect(await farming.rewards(lpUser0.address, rewardToken.address)).to.eq(BN('0'))
          expect(await rewardToken.balanceOf(lpUser0.address)).to.eq(amountBefore.add(claimable))
        })
      })
    })
  })

  describe('#exitFarming', () => {
    let tokenIdOut: string;
    let incentiveId: string
    let subject: (actor: Wallet) => Promise<any>
    let createIncentiveResult: HelperTypes.CreateIncentive.Result
    describe('before end time', () => {
    
      
      xit('cannot exitFarming', async() => {
        timestamps = makeTimestamps(await blockTimestamp())
        createIncentiveResult = await helpers.createIncentiveFlow({
          rewardToken: context.rewardToken,
          bonusRewardToken: context.bonusRewardToken,
          totalReward,
          bonusReward,
          poolAddress: context.poolObj.address,
          ...timestamps,
        })
        await erc20Helper.ensureBalancesAndApprovals(
          lpUser0,
          [context.token0, context.token1],
          amountDesired,
          context.nft.address
        )
        tokenId = await mintPosition(context.nft.connect(lpUser0), {
          token0: context.token0.address,
          token1: context.token1.address,
          fee: FeeAmount.MEDIUM,
          tickLower: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
          tickUpper: getMaxTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
          recipient: lpUser0.address,
          amount0Desired: amountDesired,
          amount1Desired: amountDesired,
          amount0Min: 0,
          amount1Min: 0,
          deadline: (await blockTimestamp()) + 1000,
        })

        await context.farmingCenter.connect(lpUser0).lockToken(tokenId)

        // await Time.setAndMine(timestamps.startTime + 1)

        await context.farmingCenter.connect(lpUser0).enterFarming(
          {
            
            rewardToken: context.rewardToken.address,
            bonusRewardToken: context.bonusRewardToken.address,
            pool: context.pool01,
            ...timestamps,
          },
          tokenId,
          0,
          LIMIT_FARMING
        )

        incentiveId = await helpers.getIncentiveId(createIncentiveResult)

        await expect(context.farmingCenter.connect(actors.lpUser0()).exitFarming(
          {
            
            pool: context.pool01,
            rewardToken: context.rewardToken.address,
            bonusRewardToken: context.bonusRewardToken.address,
            ...timestamps,
          },
          tokenId,
          LIMIT_FARMING
        )).to.be.emit(context.farming, 'FarmEnded')
      })
    })

    beforeEach('create the incentive and nft and farm it', async () => {
      timestamps = makeTimestamps(await blockTimestamp())
      createIncentiveResult = await helpers.createIncentiveFlow({
        rewardToken: context.rewardToken,
        bonusRewardToken: context.bonusRewardToken,
        totalReward,
        bonusReward,
        poolAddress: context.poolObj.address,
        ...timestamps,
      })
      await erc20Helper.ensureBalancesAndApprovals(
        lpUser0,
        [context.token0, context.token1],
        amountDesired.mul(3),
        context.nft.address
      )

      tokenId = await mintPosition(context.nft.connect(lpUser0), {
        token0: context.token0.address,
        token1: context.token1.address,
        fee: FeeAmount.MEDIUM,
        tickLower: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
        tickUpper: getMaxTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
        recipient: lpUser0.address,
        amount0Desired: amountDesired,
        amount1Desired: amountDesired,
        amount0Min: 0,
        amount1Min: 0,
        deadline: (await blockTimestamp()) + 1000,
      })
      tokenIdOut = await mintPosition(context.nft.connect(lpUser0), {
        token0: context.token0.address,
        token1: context.token1.address,
        fee: FeeAmount.MEDIUM,
        tickLower: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]),
        tickUpper: getMinTick(TICK_SPACINGS[FeeAmount.MEDIUM]) + TICK_SPACINGS[FeeAmount.MEDIUM],
        recipient: lpUser0.address,
        amount0Desired: 0,
        amount1Desired: 100,
        amount0Min: 0,
        amount1Min: 0,
        deadline: (await blockTimestamp()) + 10000,
      })

      await context.farmingCenter.connect(lpUser0).lockToken(tokenId)

      await context.farmingCenter.connect(lpUser0).lockToken(tokenIdOut)

      // await Time.setAndMine(timestamps.startTime + 1)

      await context.farmingCenter.connect(lpUser0).enterFarming(
        {
          
          rewardToken: context.rewardToken.address,
          bonusRewardToken: context.bonusRewardToken.address,
          pool: context.pool01,
          ...timestamps,
        },
        tokenId,
        0,
        LIMIT_FARMING
      )
      await context.farmingCenter.connect(lpUser0).enterFarming(
        {
          
          rewardToken: context.rewardToken.address,
          bonusRewardToken: context.bonusRewardToken.address,
          pool: context.pool01,
          ...timestamps,
        },
        tokenIdOut,
        0,
        LIMIT_FARMING
      )

      await Time.setAndMine(timestamps.endTime + 10)

      incentiveId = await helpers.getIncentiveId(createIncentiveResult)

      subject = (_actor: Wallet) =>
        context.farmingCenter.connect(_actor).exitFarming(
          {
            
            pool: context.pool01,
            rewardToken: context.rewardToken.address,
            bonusRewardToken: context.bonusRewardToken.address,
            ...timestamps,
          },
          tokenId,
          LIMIT_FARMING
        )
    })

    describe('works and', () => {
      it('decrements deposit numberOfFarms by 1', async () => {
        const { numberOfFarms: farmsPre } = await context.farmingCenter.deposits(tokenId)
        await subject(lpUser0)
        const { numberOfFarms: farmsPost } = await context.farmingCenter.deposits(tokenId)
        expect(farmsPre).to.not.equal(farmsPost - 1)
      })

      it('emits an exitFarmingd event', async () => {
        await expect(subject(lpUser0)).to.emit(context.farming, 'FarmEnded').withArgs(
            tokenId,
            incentiveId,
            context.rewardToken.address,
            context.bonusRewardToken.address,
            lpUser0.address,
            BN('99999999999999999999'),
            BN('99999999999999999999')
        )
      })

      it('allow exit without rewards', async () => {
        await expect(context.farmingCenter.connect(lpUser0).exitFarming(
          {
            
            pool: context.pool01,
            rewardToken: context.rewardToken.address,
            bonusRewardToken: context.bonusRewardToken.address,
            ...timestamps,
          },
          tokenIdOut,
          LIMIT_FARMING
        )).to.emit(context.farming, 'FarmEnded').withArgs(
            tokenIdOut,
            incentiveId,
            context.rewardToken.address,
            context.bonusRewardToken.address,
            lpUser0.address,
            BN('0'),
            BN('0')
        )
      })

      xit('has gas cost [ @skip-on-coverage ]', async () => {
        await snapshotGasCost(subject(lpUser0))
      })

      it('updates the reward available for the context.tokenomics', async () => {
        const rewardsAccured = await context.farming.rewards(lpUser0.address, context.rewardToken.address)
        await subject(lpUser0)
        expect(await context.farming.rewards(lpUser0.address, context.rewardToken.address)).to.be.gt(rewardsAccured)
      })

      it('updates the farm struct', async () => {
        const farmBefore = await context.farming.farms(tokenId, incentiveId)
        await subject(lpUser0)
        const farmAfter = await context.farming.farms(tokenId, incentiveId)

        expect(farmBefore.liquidity).to.gt(0)
        expect(farmAfter.liquidity).to.eq(0)
      })

      describe('after the end time', () => {
        beforeEach(async () => {
          // Fast-forward to after the end time
          // await Time.setAndMine(timestamps.endTime + 1)
        })

        // it('anyone cant exitFarming', async () => {
        //   await subject(actors.lpUser1())
        // })

        it('owner can exitFarming', async () => {
          await subject(lpUser0)
        })
      })

       it('calculates the right secondsPerLiquidity')
    })

    describe('fails if', () => {
      it('farm has already been exitFarming', async () => {
        // await Time.setAndMine(timestamps.endTime + 1)
        await subject(lpUser0)
        await expect(subject(lpUser0)).to.revertedWith('farm does not exist')
      })
    })
  })

  describe('liquidityIfOverflow', () => {
    const MAX_UINT_96 = BN('2').pow(BN('96')).sub(1)

    let incentive: HelperTypes.CreateIncentive.Result
    let incentiveId: string

    beforeEach(async () => {
      timestamps = makeTimestamps(1_000 + (await blockTimestamp()))
      incentive = await helpers.createIncentiveFlow({
        rewardToken: context.rewardToken,
        bonusRewardToken: context.bonusRewardToken,
        totalReward,
        bonusReward,
        poolAddress: context.poolObj.address,
        ...timestamps,
      })
      incentiveId = await helpers.getIncentiveId(incentive)
      // await Time.setAndMine(timestamps.startTime + 1)
    })

    it('works when no overflow', async () => {
      // With this `amount`, liquidity ends up less than MAX_UINT96
      const amount = MAX_UINT_96.div(1000)

      const { tokenId } = await helpers.mintFlow({
        lp: lpUser0,
        tokens: [context.token0, context.token1],
        amounts: [amount, amount],
        tickLower: 0,
        tickUpper: 10 * TICK_SPACINGS[FeeAmount.MEDIUM],
      })

      await helpers.depositFlow({
        lp: lpUser0,
        tokenId,
      })

      await context.farmingCenter.connect(lpUser0).enterFarming(incentiveResultToFarmAdapter(incentive), tokenId, 0, LIMIT_FARMING)
      const farm = await context.farming.farms(tokenId, incentiveId)
      expect(farm.liquidity).to.be.lt(MAX_UINT_96)
    })

    it('works when overflow', async () => {
      // With this `amount`, liquidity ends up more than MAX_UINT96
      const amount = MAX_UINT_96.sub(100)
      const { tokenId } = await helpers.mintFlow({
        lp: lpUser0,
        tokens: [context.token0, context.token1],
        amounts: [amount, amount],
        tickLower: 0,
        tickUpper: 10 * TICK_SPACINGS[FeeAmount.MEDIUM],
      })

      await helpers.depositFlow({
        lp: lpUser0,
        tokenId,
      })

      await context.farmingCenter.connect(lpUser0).enterFarming(incentiveResultToFarmAdapter(incentive), tokenId, 0, LIMIT_FARMING)
      const farm = await context.farming.farms(tokenId, incentiveId)
      expect(farm.liquidity).to.be.gt(MAX_UINT_96)
    })
  })
})
