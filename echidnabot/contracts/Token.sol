// SPDX-License-Identifier: PMPL-1.0
// Copyright (C) 2024 Jonathan D.A. Jewell / Hyperpolymath

pragma solidity ^0.8.19;

/// @title Token - A simple ERC20-like token for Echidna testing demonstration
/// @notice This contract demonstrates common patterns that Echidna can fuzz test
contract Token {
    string public name = "TestToken";
    string public symbol = "TST";
    uint8 public constant decimals = 18;
    uint256 public totalSupply;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    address public owner;
    bool public paused;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Paused(address account);
    event Unpaused(address account);

    modifier onlyOwner() {
        require(msg.sender == owner, "Token: caller is not the owner");
        _;
    }

    modifier whenNotPaused() {
        require(!paused, "Token: paused");
        _;
    }

    constructor(uint256 initialSupply) {
        owner = msg.sender;
        totalSupply = initialSupply;
        balanceOf[msg.sender] = initialSupply;
    }

    function transfer(address to, uint256 amount) public whenNotPaused returns (bool) {
        require(to != address(0), "Token: transfer to zero address");
        require(balanceOf[msg.sender] >= amount, "Token: insufficient balance");

        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;

        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function approve(address spender, uint256 amount) public whenNotPaused returns (bool) {
        require(spender != address(0), "Token: approve to zero address");

        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public whenNotPaused returns (bool) {
        require(from != address(0), "Token: transfer from zero address");
        require(to != address(0), "Token: transfer to zero address");
        require(balanceOf[from] >= amount, "Token: insufficient balance");
        require(allowance[from][msg.sender] >= amount, "Token: insufficient allowance");

        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;

        emit Transfer(from, to, amount);
        return true;
    }

    function mint(address to, uint256 amount) public onlyOwner whenNotPaused {
        require(to != address(0), "Token: mint to zero address");

        totalSupply += amount;
        balanceOf[to] += amount;

        emit Transfer(address(0), to, amount);
    }

    function burn(uint256 amount) public whenNotPaused {
        require(balanceOf[msg.sender] >= amount, "Token: burn exceeds balance");

        balanceOf[msg.sender] -= amount;
        totalSupply -= amount;

        emit Transfer(msg.sender, address(0), amount);
    }

    function pause() public onlyOwner {
        paused = true;
        emit Paused(msg.sender);
    }

    function unpause() public onlyOwner {
        paused = false;
        emit Unpaused(msg.sender);
    }
}
