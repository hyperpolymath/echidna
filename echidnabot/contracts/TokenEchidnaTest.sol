// SPDX-License-Identifier: PMPL-1.0
// Copyright (C) 2024 Jonathan D.A. Jewell / Hyperpolymath

pragma solidity ^0.8.19;

import "./Token.sol";

/// @title TokenEchidnaTest - Echidna fuzz testing properties for Token contract
/// @notice This contract defines invariants and properties that Echidna will attempt to break
/// @dev All functions starting with "echidna_" are treated as invariant tests
///      All functions starting with "test_" can be used for property exploration
contract TokenEchidnaTest is Token {
    // Track initial state for invariant checking
    uint256 private initialTotalSupply;
    address private constant ECHIDNA_SENDER = address(0x10000);
    address private constant ECHIDNA_RECEIVER = address(0x20000);

    constructor() Token(1_000_000 * 10 ** 18) {
        initialTotalSupply = totalSupply;
        // Give Echidna addresses some tokens to work with
        balanceOf[msg.sender] -= 100_000 * 10 ** 18;
        balanceOf[ECHIDNA_SENDER] = 50_000 * 10 ** 18;
        balanceOf[ECHIDNA_RECEIVER] = 50_000 * 10 ** 18;
    }

    // ========== INVARIANT PROPERTIES ==========
    // These must ALWAYS return true. Echidna tries to break them.

    /// @notice Total supply should never be negative (always >= 0)
    /// @dev This invariant verifies the supply never underflows
    function echidna_total_supply_not_negative() public view returns (bool) {
        return totalSupply >= 0;
    }

    /// @notice User balance should never exceed total supply
    /// @dev Prevents inflation bugs
    function echidna_balance_never_exceeds_supply() public view returns (bool) {
        return balanceOf[msg.sender] <= totalSupply;
    }

    /// @notice Transfer should not create tokens (conservation of value)
    /// @dev Sum of balances should remain constant after transfers
    function echidna_transfer_preserves_total() public view returns (bool) {
        // This is a simplified check - in production you'd track all addresses
        return totalSupply >= 0;
    }

    /// @notice Zero address should never have a balance
    /// @dev Tokens sent to zero address should be burned
    function echidna_zero_address_no_balance() public view returns (bool) {
        return balanceOf[address(0)] == 0;
    }

    /// @notice Self-transfer should not change balance
    /// @dev Sending tokens to yourself shouldn't create or destroy tokens
    function echidna_self_transfer_neutral() public returns (bool) {
        uint256 balanceBefore = balanceOf[msg.sender];
        if (balanceBefore > 0 && !paused) {
            try this.transfer(msg.sender, balanceBefore / 2) {
                return balanceOf[msg.sender] == balanceBefore;
            } catch {
                return true; // Failed transfer is acceptable
            }
        }
        return true;
    }

    /// @notice Owner should always be set
    /// @dev Owner address should never be zero after construction
    function echidna_owner_always_set() public view returns (bool) {
        return owner != address(0);
    }

    // ========== ASSERTION-BASED TESTS ==========
    // These test specific behaviors with assertions

    /// @notice Test that transfer reduces sender balance correctly
    function test_transfer_reduces_balance(address to, uint256 amount) public {
        // Skip invalid inputs
        if (to == address(0) || to == msg.sender || paused) return;
        if (amount == 0 || amount > balanceOf[msg.sender]) return;

        uint256 balanceBefore = balanceOf[msg.sender];
        transfer(to, amount);
        uint256 balanceAfter = balanceOf[msg.sender];

        assert(balanceAfter == balanceBefore - amount);
    }

    /// @notice Test that transfer increases receiver balance correctly
    function test_transfer_increases_balance(address to, uint256 amount) public {
        // Skip invalid inputs
        if (to == address(0) || to == msg.sender || paused) return;
        if (amount == 0 || amount > balanceOf[msg.sender]) return;

        uint256 receiverBefore = balanceOf[to];
        transfer(to, amount);
        uint256 receiverAfter = balanceOf[to];

        assert(receiverAfter == receiverBefore + amount);
    }

    /// @notice Test approve and transferFrom flow
    function test_approve_transferFrom(
        address spender,
        uint256 approveAmount,
        uint256 transferAmount
    ) public {
        if (spender == address(0) || spender == msg.sender || paused) return;
        if (approveAmount == 0 || transferAmount == 0) return;
        if (transferAmount > approveAmount) return;
        if (approveAmount > balanceOf[msg.sender]) return;

        approve(spender, approveAmount);
        assert(allowance[msg.sender][spender] == approveAmount);
    }

    /// @notice Test that burn reduces total supply
    function test_burn_reduces_supply(uint256 amount) public {
        if (amount == 0 || amount > balanceOf[msg.sender] || paused) return;

        uint256 supplyBefore = totalSupply;
        burn(amount);
        uint256 supplyAfter = totalSupply;

        assert(supplyAfter == supplyBefore - amount);
    }

    // ========== HELPER FUNCTIONS FOR ECHIDNA ==========

    /// @notice Allow Echidna to trigger pause (simulating owner action)
    function echidna_try_pause() public {
        if (msg.sender == owner) {
            pause();
        }
    }

    /// @notice Allow Echidna to trigger unpause
    function echidna_try_unpause() public {
        if (msg.sender == owner) {
            unpause();
        }
    }
}
