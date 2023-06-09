// SPDX-License-Identifier: BUSL-1.1
pragma solidity =0.7.6;
pragma abicoder v2;
import './interfaces/IFarmingCenter.sol';
import './interfaces/IFarmingCenterVault.sol';

import '@cryptoalgebra/core/contracts/interfaces/IAlgebraPool.sol';
import '@cryptoalgebra/core/contracts/interfaces/IERC20Minimal.sol';

import './interfaces/INonfungiblePositionManager.sol';

import './base/Multicall.sol';
import './base/PeripheryPayments.sol';
import './libraries/IncentiveId.sol';

/// @title Algebra main farming contract
/// @dev Manages farmings and performs entry, exit and other actions.
contract FarmingCenter is IFarmingCenter, Multicall, PeripheryPayments {
    IAlgebraLimitFarming public immutable override limitFarming;
    IAlgebraEternalFarming public immutable override eternalFarming;
    INonfungiblePositionManager public immutable override nonfungiblePositionManager;
    IFarmingCenterVault public immutable override farmingCenterVault;

    /// @dev saves addresses of virtual pools for pool
    mapping(address => VirtualPoolAddresses) private _virtualPoolAddresses;

    /// @dev deposits[tokenId] => Deposit
    mapping(uint256 => Deposit) public override deposits;

    /// @notice Represents the deposit of a liquidity NFT
    struct Deposit {
        uint32 numberOfFarms;
        bool inLimitFarming;
    }

    constructor(
        IAlgebraLimitFarming _limitFarming,
        IAlgebraEternalFarming _eternalFarming,
        INonfungiblePositionManager _nonfungiblePositionManager,
        IFarmingCenterVault _farmingCenterVault
    ) PeripheryPayments(INonfungiblePositionManager(_nonfungiblePositionManager).WNativeToken()) {
        limitFarming = _limitFarming;
        eternalFarming = _eternalFarming;
        nonfungiblePositionManager = _nonfungiblePositionManager;
        farmingCenterVault = _farmingCenterVault;
    }

    modifier isOwner(uint256 tokenId) {
        require(nonfungiblePositionManager.ownerOf(tokenId) == msg.sender, 'not owner');
        _;
    }

    function lockToken(uint256 tokenId) external override isOwner(tokenId) {
        Deposit storage newDeposit = deposits[tokenId];
        require(newDeposit.numberOfFarms == 0, 'already locked');

        nonfungiblePositionManager.changeTokenLock(tokenId, true);
        emit Lock(tokenId, true);
    }

    function _getTokenBalanceOfVault(address token) private view returns (uint256 balance) {
        return IERC20Minimal(token).balanceOf(address(farmingCenterVault));
    }

    /// @inheritdoc IFarmingCenter
    function enterFarming(
        IncentiveKey memory key,
        uint256 tokenId,
        uint256 tokensLocked,
        bool isLimit
    ) external override isOwner(tokenId) {
        Deposit storage _deposit = deposits[tokenId];
        (uint32 numberOfFarms, bool inLimitFarming) = (_deposit.numberOfFarms, _deposit.inLimitFarming);
        numberOfFarms++;
        IAlgebraFarming _farming;
        if (isLimit) {
            require(!inLimitFarming, 'token already farmed');
            inLimitFarming = true;
            _farming = IAlgebraFarming(limitFarming);
        } else _farming = IAlgebraFarming(eternalFarming);

        (_deposit.numberOfFarms, _deposit.inLimitFarming) = (numberOfFarms, inLimitFarming);
        bytes32 incentiveId = IncentiveId.compute(key);
        (, , , , , address multiplierToken, ) = _farming.incentives(incentiveId);
        if (tokensLocked > 0) {
            uint256 balanceBefore = _getTokenBalanceOfVault(multiplierToken);
            TransferHelper.safeTransferFrom(multiplierToken, msg.sender, address(farmingCenterVault), tokensLocked);
            uint256 balanceAfter = _getTokenBalanceOfVault(multiplierToken);
            require(balanceAfter > balanceBefore, 'Insufficient tokens locked');
            tokensLocked = balanceAfter - balanceBefore;
            farmingCenterVault.lockTokens(tokenId, incentiveId, tokensLocked);
        }

        _farming.enterFarming(key, tokenId, tokensLocked);
    }

    /// @inheritdoc IFarmingCenter
    function exitFarming(IncentiveKey memory key, uint256 tokenId, bool isLimit) external override isOwner(tokenId) {
        Deposit storage deposit = deposits[tokenId];
        IAlgebraFarming _farming;

        deposit.numberOfFarms -= 1;
        if (isLimit) {
            deposit.inLimitFarming = false;
            _farming = IAlgebraFarming(limitFarming);
        } else _farming = IAlgebraFarming(eternalFarming);

        _farming.exitFarming(key, tokenId, msg.sender);

        bytes32 incentiveId = IncentiveId.compute(key);
        (, , , , , address multiplierToken, ) = _farming.incentives(incentiveId);
        if (multiplierToken != address(0)) {
            farmingCenterVault.claimTokens(multiplierToken, msg.sender, tokenId, incentiveId);
        }
    }

    /// @inheritdoc IFarmingCenter
    function increaseLiquidity(
        IncentiveKey memory key,
        INonfungiblePositionManager.IncreaseLiquidityParams memory params
    ) external payable override returns (uint128 liquidity, uint256 amount0, uint256 amount1) {
        (, , , address token0, address token1, , , , , , , ) = nonfungiblePositionManager.positions(params.tokenId);
        if (params.amount0Desired > 0) {
            pay(token0, msg.sender, address(this), params.amount0Desired);
            TransferHelper.safeApprove(token0, address(nonfungiblePositionManager), params.amount0Desired);
        }
        if (params.amount1Desired > 0) {
            pay(token1, msg.sender, address(this), params.amount1Desired);
            TransferHelper.safeApprove(token1, address(nonfungiblePositionManager), params.amount1Desired);
        }

        (liquidity, amount0, amount1) = nonfungiblePositionManager.increaseLiquidity(params);

        // refund
        if (params.amount0Desired > amount0) {
            if (token0 == WNativeToken) {
                unwrapWNativeToken(params.amount0Desired - amount0, msg.sender);
            } else {
                pay(token0, address(this), msg.sender, params.amount0Desired - amount0);
            }
        }
        if (params.amount1Desired > amount1) {
            if (token1 == WNativeToken) {
                unwrapWNativeToken(params.amount1Desired - amount1, msg.sender);
            } else {
                pay(token1, address(this), msg.sender, params.amount1Desired - amount1);
            }
        }

        // get locked token amount
        bytes32 incentiveId = IncentiveId.compute(key);
        uint256 lockedAmount = farmingCenterVault.balances(params.tokenId, incentiveId);

        // exit & enter
        eternalFarming.exitFarming(key, params.tokenId, nonfungiblePositionManager.ownerOf(params.tokenId));
        eternalFarming.enterFarming(key, params.tokenId, lockedAmount);
    }

    function decreaseLiquidity(
        IncentiveKey memory key,
        DecreaseLiquidityParams memory params
    ) external payable override isOwner(params.tokenId) returns (uint256 amount0, uint256 amount1) {
        nonfungiblePositionManager.decreaseLiquidity(
            INonfungiblePositionManager.DecreaseLiquidityParams(
                params.tokenId,
                params.liquidity,
                params.amount0Min,
                params.amount1Min,
                params.deadline
            )
        );
        address recipient = params.recipient == address(0) ? address(this) : params.recipient;
        (amount0, amount1) = nonfungiblePositionManager.collect(
            INonfungiblePositionManager.CollectParams(params.tokenId, recipient, params.amount0Max, params.amount1Max)
        );

        // get locked token amount
        bytes32 incentiveId = IncentiveId.compute(key);
        uint256 lockedAmount = farmingCenterVault.balances(params.tokenId, incentiveId);

        // exit & enter
        (, , , , , , , uint128 liquidity, , , , ) = nonfungiblePositionManager.positions(params.tokenId);
        if (liquidity != 0) {
            eternalFarming.exitFarming(key, params.tokenId, nonfungiblePositionManager.ownerOf(params.tokenId));
            eternalFarming.enterFarming(key, params.tokenId, lockedAmount);
        } else {
            Deposit storage deposit = deposits[params.tokenId];
            deposit.numberOfFarms -= 1;

            eternalFarming.exitFarming(key, params.tokenId, nonfungiblePositionManager.ownerOf(params.tokenId));

            (, , , , , address multiplierToken, ) = eternalFarming.incentives(incentiveId);
            if (multiplierToken != address(0)) {
                farmingCenterVault.claimTokens(multiplierToken, msg.sender, params.tokenId, incentiveId);
            }
        }
    }

    /// @inheritdoc IFarmingCenter
    function collectRewards(
        IncentiveKey memory key,
        uint256 tokenId
    ) external override isOwner(tokenId) returns (uint256 reward, uint256 bonusReward) {
        (reward, bonusReward) = eternalFarming.collectRewards(key, tokenId, msg.sender);
    }

    function _claimRewardFromFarming(
        IAlgebraFarming _farming,
        IERC20Minimal rewardToken,
        address to,
        uint256 amountRequested
    ) internal returns (uint256 reward) {
        return _farming.claimRewardFrom(rewardToken, msg.sender, to, amountRequested);
    }

    /// @inheritdoc IFarmingCenter
    function claimReward(
        IERC20Minimal rewardToken,
        address to,
        uint256 amountRequestedIncentive,
        uint256 amountRequestedEternal
    ) external override returns (uint256 reward) {
        if (amountRequestedIncentive != 0) {
            reward = _claimRewardFromFarming(limitFarming, rewardToken, to, amountRequestedIncentive);
        }
        if (amountRequestedEternal != 0) {
            reward += _claimRewardFromFarming(eternalFarming, rewardToken, to, amountRequestedEternal);
        }
    }

    /// @inheritdoc IFarmingCenter
    function connectVirtualPool(IAlgebraPool pool, address newVirtualPool) external override {
        bool isLimitFarming = msg.sender == address(limitFarming);
        require(isLimitFarming || msg.sender == address(eternalFarming), 'only farming can call this');

        VirtualPoolAddresses storage virtualPools = _virtualPoolAddresses[address(pool)];
        address newIncentive;
        if (pool.activeIncentive() == address(0)) {
            newIncentive = newVirtualPool; // turn on pool directly
        } else {
            if (newVirtualPool == address(0)) {
                // turn on directly another pool if it exists
                newIncentive = isLimitFarming ? virtualPools.eternalVirtualPool : virtualPools.limitVirtualPool;
            } else {
                newIncentive = address(this); // turn on via "proxy"
            }
        }

        pool.setIncentive(newIncentive);

        if (isLimitFarming) {
            virtualPools.limitVirtualPool = newVirtualPool;
        } else {
            virtualPools.eternalVirtualPool = newVirtualPool;
        }
    }

    /// @inheritdoc IFarmingCenter
    function unlockToken(uint256 tokenId) external override isOwner(tokenId) {
        Deposit storage deposit = deposits[tokenId];
        require(deposit.numberOfFarms == 0, 'cannot unlock token while farmed');

        nonfungiblePositionManager.changeTokenLock(tokenId, false);
        emit Lock(tokenId, false);
    }

    /**
     * @dev This function is called by the main pool when an initialized tick is crossed and two farmings are active at same time.
     * @param nextTick The crossed tick
     * @param zeroToOne The direction
     */
    function cross(int24 nextTick, bool zeroToOne) external override returns (bool) {
        VirtualPoolAddresses storage _virtualPoolAddressesForPool = _virtualPoolAddresses[msg.sender];

        IAlgebraVirtualPool(_virtualPoolAddressesForPool.eternalVirtualPool).cross(nextTick, zeroToOne);
        IAlgebraVirtualPool(_virtualPoolAddressesForPool.limitVirtualPool).cross(nextTick, zeroToOne);
        // TODO handle "false" from virtual pool?
        return true;
    }

    function virtualPoolAddresses(address pool) external view override returns (address limitVP, address eternalVP) {
        (limitVP, eternalVP) = (
            _virtualPoolAddresses[pool].limitVirtualPool,
            _virtualPoolAddresses[pool].eternalVirtualPool
        );
    }
}
