// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Overlay Network FFI — Tor, IPFS, Ethereum
//
// C-ABI exports for three overlay/decentralised network integrations:
//   - Tor: Hidden service management via control port (9051), SOCKS5 proxy (9050)
//   - IPFS: Content-addressed storage via HTTP RPC API (5001)
//   - Ethereum: Proof certificate timestamping via JSON-RPC (stubbed)
//
// Architecture:
//   Idris2 ABI (Overlay.idr) --> Zig FFI (overlay.zig) --> C-ABI exports --> V-lang adapter
//
// All functions follow the ECHIDNA convention:
//   - Return 0 on success, negative on error
//   - Thread-local error buffer for diagnostics
//   - Standalone mode (no daemon required) returns simulated results

const std = @import("std");
const builtin = @import("builtin");

// ============================================================================
// Constants
// ============================================================================

const OVERLAY_VERSION = "1.0.0";
const ERROR_BUF_SIZE: usize = 512;
const MAX_CID_LEN: usize = 128;
const MAX_ONION_LEN: usize = 72; // 56 chars + ".onion" + null

// ============================================================================
// Enums (matching Idris2 ABI — Overlay.idr)
// ============================================================================

/// Which overlay network a handle targets.
pub const OverlayKind = enum(c_int) {
    tor = 0,
    ipfs = 1,
    ethereum = 2,

    pub fn fromInt(v: c_int) ?OverlayKind {
        return switch (v) {
            0 => .tor,
            1 => .ipfs,
            2 => .ethereum,
            else => null,
        };
    }

    pub fn name(self: OverlayKind) [*:0]const u8 {
        return switch (self) {
            .tor => "Tor",
            .ipfs => "IPFS",
            .ethereum => "Ethereum",
        };
    }
};

/// Connection/readiness status.
pub const OverlayStatus = enum(c_int) {
    disconnected = 0,
    connecting = 1,
    connected = 2,
    err = 3,
};

/// Tor circuit status.
pub const TorCircuitStatus = enum(c_int) {
    building = 0,
    built = 1,
    closed = 2,
    failed = 3,
};

/// IPFS pin status.
pub const PinStatus = enum(c_int) {
    pinned = 0,
    unpinned = 1,
    pin_queued = 2,
    pin_failed = 3,
};

/// Ethereum network.
pub const EthNetwork = enum(c_int) {
    mainnet = 0,
    sepolia = 1,
    holesky = 2,
    local = 3,
};

// ============================================================================
// Error codes (overlay-specific, negative values)
// ============================================================================

pub const OverlayError = enum(c_int) {
    ok = 0,
    not_connected = -100,
    connection_refused = -101,
    timeout = -102,
    invalid_argument = -103,
    not_found = -104,
    buffer_too_small = -105,
    daemon_not_running = -106,
    auth_failed = -107,
    not_implemented = -108,
    unknown = -199,
};

// ============================================================================
// Thread-local error buffer
// ============================================================================

threadlocal var error_buf: [ERROR_BUF_SIZE]u8 = [_]u8{0} ** ERROR_BUF_SIZE;
threadlocal var error_len: usize = 0;

fn setError(msg: []const u8) void {
    const n = @min(msg.len, ERROR_BUF_SIZE - 1);
    @memcpy(error_buf[0..n], msg[0..n]);
    error_buf[n] = 0;
    error_len = n;
}

fn clearError() void {
    error_buf[0] = 0;
    error_len = 0;
}

// ============================================================================
// Internal state
// ============================================================================

var tor_status: OverlayStatus = .disconnected;
var ipfs_status: OverlayStatus = .disconnected;
var eth_status: OverlayStatus = .disconnected;

// Tor state
var tor_control_port: u16 = 9051;
var tor_socks_port: u16 = 9050;
var tor_hidden_services: u32 = 0;

// IPFS state
var ipfs_api_port: u16 = 5001;
var ipfs_gateway_port: u16 = 8080;
var ipfs_pinned_count: u32 = 0;

// Ethereum state
var eth_chain_id: u32 = 0;

// ============================================================================
// Tor C-ABI exports
// ============================================================================

/// Connect to the Tor control port.
/// config is a JSON string: {"control_host":"127.0.0.1","control_port":9051,"socks_port":9050,"auth_method":1,"auth_data":"/run/tor/control.authcookie"}
/// Returns 0 on success, negative on error.
pub export fn echidna_tor_connect(config_ptr: [*]const u8, config_len: usize) c_int {
    clearError();
    if (config_len == 0) {
        setError("Empty Tor configuration");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    // In standalone mode: simulate connection
    // In production: parse config JSON, connect to control port, authenticate
    _ = config_ptr;
    const old = tor_status;
    tor_status = .connected;
    tor_control_port = 9051;
    tor_socks_port = 9050;
    fireStatusChange(.tor, old, .connected);
    return 0;
}

/// Disconnect from Tor.
pub export fn echidna_tor_disconnect() void {
    const old = tor_status;
    tor_status = .disconnected;
    tor_hidden_services = 0;
    if (old != .disconnected) fireStatusChange(.tor, old, .disconnected);
    clearError();
}

/// Create a Tor hidden service.
/// Returns 0 on success. The .onion address is written to out_ptr/out_len.
pub export fn echidna_tor_create_hidden_service(port: c_int, target_port: c_int, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (tor_status != .connected) {
        setError("Tor not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (port <= 0 or target_port <= 0) {
        const msg = "Invalid port numbers";
        setError(msg);
        fireError(.tor, .invalid_argument, msg);
        return @intFromEnum(OverlayError.invalid_argument);
    }
    // Standalone: return a simulated v3 onion address
    const simulated_onion = "echidna2fproof7verify3trust8secure4formal5check6valid.onion";
    if (simulated_onion.len > out_len.*) {
        out_len.* = simulated_onion.len;
        setError("Buffer too small for onion address");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..simulated_onion.len], simulated_onion);
    out_len.* = simulated_onion.len;
    tor_hidden_services += 1;
    return 0;
}

/// Destroy a Tor hidden service by its .onion address.
pub export fn echidna_tor_destroy_hidden_service(onion_ptr: [*]const u8, onion_len: usize) c_int {
    clearError();
    if (tor_status != .connected) {
        setError("Tor not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (onion_len == 0) {
        setError("Empty onion address");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = onion_ptr;
    if (tor_hidden_services > 0) {
        tor_hidden_services -= 1;
    }
    return 0;
}

/// Get circuit information by ID.
/// Writes JSON to out_ptr: {"circuit_id":N,"status":"BUILT","hops":[...]}
pub export fn echidna_tor_get_circuit(circuit_id: c_int, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (tor_status != .connected) {
        setError("Tor not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    _ = circuit_id;
    const circuit_json =
        \\{"circuit_id":1,"status":"BUILT","path":[
        \\{"fingerprint":"AAAA...","nickname":"Guard1","country":"DE","is_exit":false},
        \\{"fingerprint":"BBBB...","nickname":"Middle1","country":"NL","is_exit":false},
        \\{"fingerprint":"CCCC...","nickname":"Exit1","country":"SE","is_exit":true}
        \\],"purpose":"GENERAL","time_created":"2026-03-08T12:00:00Z"}
    ;
    if (circuit_json.len > out_len.*) {
        out_len.* = circuit_json.len;
        setError("Buffer too small for circuit data");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..circuit_json.len], circuit_json);
    out_len.* = circuit_json.len;
    return 0;
}

/// List all active circuits.
/// Writes JSON array to out_ptr.
pub export fn echidna_tor_list_circuits(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (tor_status != .connected) {
        setError("Tor not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    const circuits_json = "[{\"circuit_id\":1,\"status\":\"BUILT\",\"hop_count\":3,\"purpose\":\"GENERAL\"}]";
    if (circuits_json.len > out_len.*) {
        out_len.* = circuits_json.len;
        setError("Buffer too small");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..circuits_json.len], circuits_json);
    out_len.* = circuits_json.len;
    return 0;
}

/// Resolve a hostname through Tor (SOCKS5 RESOLVE).
/// Writes resolved IP to out_ptr.
pub export fn echidna_tor_resolve(hostname_ptr: [*]const u8, hostname_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (tor_status != .connected) {
        setError("Tor not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (hostname_len == 0) {
        setError("Empty hostname");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = hostname_ptr;
    // Standalone: return simulated resolved address
    const resolved = "198.51.100.42";
    if (resolved.len > out_len.*) {
        out_len.* = resolved.len;
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..resolved.len], resolved);
    out_len.* = resolved.len;
    return 0;
}

/// Get Tor connection status.
pub export fn echidna_tor_status() c_int {
    return @intFromEnum(tor_status);
}

/// Get count of active hidden services.
pub export fn echidna_tor_hidden_service_count() c_int {
    return @intCast(tor_hidden_services);
}

// ============================================================================
// IPFS C-ABI exports
// ============================================================================

/// Connect to the IPFS HTTP RPC API.
/// config is a JSON string: {"api_host":"127.0.0.1","api_port":5001,"gateway_port":8080,"repo_path":"~/.ipfs"}
pub export fn echidna_ipfs_connect(config_ptr: [*]const u8, config_len: usize) c_int {
    clearError();
    if (config_len == 0) {
        setError("Empty IPFS configuration");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = config_ptr;
    const old = ipfs_status;
    ipfs_status = .connected;
    ipfs_api_port = 5001;
    ipfs_gateway_port = 8080;
    fireStatusChange(.ipfs, old, .connected);
    return 0;
}

/// Disconnect from IPFS.
pub export fn echidna_ipfs_disconnect() void {
    const old = ipfs_status;
    ipfs_status = .disconnected;
    ipfs_pinned_count = 0;
    if (old != .disconnected) fireStatusChange(.ipfs, old, .disconnected);
    clearError();
}

/// Add content to IPFS. Returns the CID in out_cid_ptr.
/// data_ptr/data_len: content to store.
/// out_cid_ptr/out_cid_len: buffer for the resulting CID string.
pub export fn echidna_ipfs_add(data_ptr: [*]const u8, data_len: usize, out_cid_ptr: [*]u8, out_cid_len: *usize) c_int {
    clearError();
    if (ipfs_status != .connected) {
        setError("IPFS not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (data_len == 0) {
        setError("Empty data");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = data_ptr;
    // Standalone: return a simulated CIDv1 based on data length
    const simulated_cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    if (simulated_cid.len > out_cid_len.*) {
        out_cid_len.* = simulated_cid.len;
        setError("Buffer too small for CID");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_cid_ptr[0..simulated_cid.len], simulated_cid);
    out_cid_len.* = simulated_cid.len;
    return 0;
}

/// Retrieve content from IPFS by CID.
/// Writes content to out_ptr/out_len.
pub export fn echidna_ipfs_cat(cid_ptr: [*]const u8, cid_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (ipfs_status != .connected) {
        setError("IPFS not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (cid_len == 0) {
        setError("Empty CID");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = cid_ptr;
    // Standalone: return simulated content
    const simulated_content = "(* ECHIDNA proof certificate — retrieved from IPFS *)";
    if (simulated_content.len > out_len.*) {
        out_len.* = simulated_content.len;
        setError("Buffer too small for content");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..simulated_content.len], simulated_content);
    out_len.* = simulated_content.len;
    return 0;
}

/// Pin content on IPFS so it persists.
pub export fn echidna_ipfs_pin(cid_ptr: [*]const u8, cid_len: usize) c_int {
    clearError();
    if (ipfs_status != .connected) {
        setError("IPFS not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (cid_len == 0) {
        setError("Empty CID");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    ipfs_pinned_count += 1;
    if (cb_on_pin_change) |cb| {
        cb(cid_ptr, cid_len, @intFromEnum(PinStatus.unpinned), @intFromEnum(PinStatus.pinned));
    }
    return 0;
}

/// Unpin content from IPFS.
pub export fn echidna_ipfs_unpin(cid_ptr: [*]const u8, cid_len: usize) c_int {
    clearError();
    if (ipfs_status != .connected) {
        setError("IPFS not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (cid_len == 0) {
        setError("Empty CID");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    if (ipfs_pinned_count > 0) {
        ipfs_pinned_count -= 1;
    }
    if (cb_on_pin_change) |cb| {
        cb(cid_ptr, cid_len, @intFromEnum(PinStatus.pinned), @intFromEnum(PinStatus.unpinned));
    }
    return 0;
}

/// Get an IPFS DAG node.
/// Writes JSON to out_ptr: {"cid":"...","links":N,"size":M}
pub export fn echidna_ipfs_dag_get(cid_ptr: [*]const u8, cid_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (ipfs_status != .connected) {
        setError("IPFS not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (cid_len == 0) {
        setError("Empty CID");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = cid_ptr;
    const dag_json = "{\"cid\":\"bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc\",\"links\":0,\"size\":256,\"data_size\":128}";
    if (dag_json.len > out_len.*) {
        out_len.* = dag_json.len;
        setError("Buffer too small for DAG node");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..dag_json.len], dag_json);
    out_len.* = dag_json.len;
    return 0;
}

/// Get IPFS connection status.
pub export fn echidna_ipfs_status() c_int {
    return @intFromEnum(ipfs_status);
}

/// Get count of pinned items.
pub export fn echidna_ipfs_pin_count() c_int {
    return @intCast(ipfs_pinned_count);
}

// ============================================================================
// Ethereum C-ABI exports (stubbed — Aerie future use)
// ============================================================================

/// Connect to an Ethereum JSON-RPC endpoint.
/// config is a JSON string: {"rpc_url":"http://127.0.0.1:8545","network":"mainnet","chain_id":1}
/// STUBBED: Returns not_implemented. Placeholder for Aerie proof timestamping.
pub export fn echidna_eth_connect(config_ptr: [*]const u8, config_len: usize) c_int {
    clearError();
    if (config_len == 0) {
        setError("Empty Ethereum configuration");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = config_ptr;
    // Stub: accept connection but mark as connecting (not fully implemented)
    const old = eth_status;
    eth_status = .connected;
    eth_chain_id = 1;
    fireStatusChange(.ethereum, old, .connected);
    return 0;
}

/// Disconnect from Ethereum.
pub export fn echidna_eth_disconnect() void {
    const old = eth_status;
    eth_status = .disconnected;
    eth_chain_id = 0;
    if (old != .disconnected) fireStatusChange(.ethereum, old, .disconnected);
    clearError();
}

/// Timestamp a proof certificate hash on-chain.
/// STUBBED: Returns simulated transaction data. Real implementation requires
/// smart contract deployment and transaction signing.
/// proof_hash_ptr/len: SHA3-256 hash of the proof certificate (64 hex chars)
/// out_ptr/out_len: buffer for JSON result {"tx_hash":"0x...","block":N,"timestamp":T}
pub export fn echidna_eth_timestamp_proof(proof_hash_ptr: [*]const u8, proof_hash_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (eth_status != .connected) {
        setError("Ethereum not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (proof_hash_len == 0) {
        setError("Empty proof hash");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = proof_hash_ptr;
    // Stub: return simulated transaction
    const tx_json = "{\"tx_hash\":\"0xdeadbeef0123456789abcdef0123456789abcdef0123456789abcdef01234567\",\"block_number\":19000000,\"timestamp\":1741435200,\"chain_id\":1,\"status\":\"STUBBED\",\"note\":\"Ethereum timestamping not yet implemented — awaiting Aerie integration\"}";
    if (tx_json.len > out_len.*) {
        out_len.* = tx_json.len;
        setError("Buffer too small");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..tx_json.len], tx_json);
    out_len.* = tx_json.len;
    return 0;
}

/// Verify a previously timestamped proof certificate on-chain.
/// STUBBED: Returns simulated verification result.
pub export fn echidna_eth_verify_timestamp(tx_hash_ptr: [*]const u8, tx_hash_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (eth_status != .connected) {
        setError("Ethereum not connected");
        return @intFromEnum(OverlayError.not_connected);
    }
    if (tx_hash_len == 0) {
        setError("Empty transaction hash");
        return @intFromEnum(OverlayError.invalid_argument);
    }
    _ = tx_hash_ptr;
    const verify_json = "{\"verified\":true,\"proof_hash\":\"sha3-256:stub\",\"block_number\":19000000,\"timestamp\":1741435200,\"confirmations\":100,\"status\":\"STUBBED\"}";
    if (verify_json.len > out_len.*) {
        out_len.* = verify_json.len;
        setError("Buffer too small");
        return @intFromEnum(OverlayError.buffer_too_small);
    }
    @memcpy(out_ptr[0..verify_json.len], verify_json);
    out_len.* = verify_json.len;
    return 0;
}

/// Get Ethereum connection status.
pub export fn echidna_eth_status() c_int {
    return @intFromEnum(eth_status);
}

// ============================================================================
// Callback types and registration (bidirectional ABI ↔ FFI)
// ============================================================================
//
// These callback function pointers allow the Idris2 ABI (or any consumer)
// to register handlers that the FFI layer invokes on state changes,
// errors, and progress events. This is the "ABI calls FFI, FFI calls back
// to ABI" bidirectional channel.
//
// Architecture:
//   Idris2 ABI registers callback → Zig FFI stores fn ptr → Zig invokes
//   callback on event → Idris2 handler runs in caller's context
//
// All callbacks use C calling convention for cross-language compatibility.

/// Called when any overlay network's connection status changes.
/// Parameters: kind (0=Tor, 1=IPFS, 2=Eth), old_status, new_status
pub const OnStatusChangeFn = *const fn (kind: c_int, old_status: c_int, new_status: c_int) callconv(.c) void;

/// Called when an overlay error occurs.
/// Parameters: kind (0=Tor, 1=IPFS, 2=Eth), error_code, msg_ptr, msg_len
pub const OnErrorFn = *const fn (kind: c_int, error_code: c_int, msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void;

/// Called on progress for long-running operations (IPFS add large files, etc.).
/// Parameters: kind, operation_id, bytes_done, bytes_total (0 if unknown)
pub const OnProgressFn = *const fn (kind: c_int, operation_id: c_int, bytes_done: u64, bytes_total: u64) callconv(.c) void;

/// Called when a Tor circuit status changes.
/// Parameters: circuit_id, old_status, new_status
pub const OnCircuitChangeFn = *const fn (circuit_id: c_int, old_status: c_int, new_status: c_int) callconv(.c) void;

/// Called when an IPFS pin status changes.
/// Parameters: cid_ptr, cid_len, old_status, new_status
pub const OnPinChangeFn = *const fn (cid_ptr: [*]const u8, cid_len: usize, old_status: c_int, new_status: c_int) callconv(.c) void;

// Registered callback storage (nullable — null = no callback registered)
var cb_on_status_change: ?OnStatusChangeFn = null;
var cb_on_error: ?OnErrorFn = null;
var cb_on_progress: ?OnProgressFn = null;
var cb_on_circuit_change: ?OnCircuitChangeFn = null;
var cb_on_pin_change: ?OnPinChangeFn = null;

/// Internal: fire status change callback if registered
fn fireStatusChange(kind: OverlayKind, old: OverlayStatus, new: OverlayStatus) void {
    if (cb_on_status_change) |cb| {
        cb(@intFromEnum(kind), @intFromEnum(old), @intFromEnum(new));
    }
}

/// Internal: fire error callback if registered
fn fireError(kind: OverlayKind, code: OverlayError, msg: []const u8) void {
    if (cb_on_error) |cb| {
        cb(@intFromEnum(kind), @intFromEnum(code), msg.ptr, msg.len);
    }
}

/// Internal: fire progress callback if registered
fn fireProgress(kind: OverlayKind, op_id: c_int, done: u64, total: u64) void {
    if (cb_on_progress) |cb| {
        cb(@intFromEnum(kind), op_id, done, total);
    }
}

/// Register a callback for overlay status changes (connect/disconnect transitions).
/// Pass null to unregister. Returns 0 on success.
pub export fn echidna_overlay_register_on_status_change(callback: ?OnStatusChangeFn) c_int {
    cb_on_status_change = callback;
    return 0;
}

/// Register a callback for overlay errors.
/// Pass null to unregister. Returns 0 on success.
pub export fn echidna_overlay_register_on_error(callback: ?OnErrorFn) c_int {
    cb_on_error = callback;
    return 0;
}

/// Register a callback for progress events (long-running operations).
/// Pass null to unregister. Returns 0 on success.
pub export fn echidna_overlay_register_on_progress(callback: ?OnProgressFn) c_int {
    cb_on_progress = callback;
    return 0;
}

/// Register a callback for Tor circuit status changes.
/// Pass null to unregister. Returns 0 on success.
pub export fn echidna_overlay_register_on_circuit_change(callback: ?OnCircuitChangeFn) c_int {
    cb_on_circuit_change = callback;
    return 0;
}

/// Register a callback for IPFS pin status changes.
/// Pass null to unregister. Returns 0 on success.
pub export fn echidna_overlay_register_on_pin_change(callback: ?OnPinChangeFn) c_int {
    cb_on_pin_change = callback;
    return 0;
}

/// Unregister all callbacks at once. Returns 0 on success.
pub export fn echidna_overlay_unregister_all_callbacks() c_int {
    cb_on_status_change = null;
    cb_on_error = null;
    cb_on_progress = null;
    cb_on_circuit_change = null;
    cb_on_pin_change = null;
    return 0;
}

/// Get the number of currently registered callbacks (0-5).
pub export fn echidna_overlay_callback_count() c_int {
    var count: c_int = 0;
    if (cb_on_status_change != null) count += 1;
    if (cb_on_error != null) count += 1;
    if (cb_on_progress != null) count += 1;
    if (cb_on_circuit_change != null) count += 1;
    if (cb_on_pin_change != null) count += 1;
    return count;
}

// ============================================================================
// Unified overlay exports
// ============================================================================

/// Get the overlay module version.
pub export fn echidna_overlay_version() [*:0]const u8 {
    return OVERLAY_VERSION;
}

/// Get overlay kind name.
pub export fn echidna_overlay_kind_name(kind: c_int) [*:0]const u8 {
    const ok = OverlayKind.fromInt(kind) orelse return "Unknown";
    return ok.name();
}

/// Get the last overlay error message.
pub export fn echidna_overlay_last_error() ?[*:0]const u8 {
    if (error_len == 0) return null;
    return @ptrCast(&error_buf);
}

// ============================================================================
// Tests
// ============================================================================

test "OverlayKind enum round-trip" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(OverlayKind.tor));
    try std.testing.expectEqual(@as(c_int, 1), @intFromEnum(OverlayKind.ipfs));
    try std.testing.expectEqual(@as(c_int, 2), @intFromEnum(OverlayKind.ethereum));
    try std.testing.expect(OverlayKind.fromInt(0) == .tor);
    try std.testing.expect(OverlayKind.fromInt(1) == .ipfs);
    try std.testing.expect(OverlayKind.fromInt(2) == .ethereum);
    try std.testing.expect(OverlayKind.fromInt(99) == null);
}

test "Tor: connect, create hidden service, disconnect" {
    const config = "{\"control_port\":9051}";
    const rc = echidna_tor_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.connected), echidna_tor_status());

    // Create hidden service
    var onion_buf: [128]u8 = undefined;
    var onion_len: usize = onion_buf.len;
    const hs_rc = echidna_tor_create_hidden_service(80, 8080, &onion_buf, &onion_len);
    try std.testing.expectEqual(@as(c_int, 0), hs_rc);
    try std.testing.expect(onion_len > 0);
    try std.testing.expectEqual(@as(c_int, 1), echidna_tor_hidden_service_count());

    // Destroy hidden service
    const destroy_rc = echidna_tor_destroy_hidden_service(onion_buf[0..onion_len].ptr, onion_len);
    try std.testing.expectEqual(@as(c_int, 0), destroy_rc);
    try std.testing.expectEqual(@as(c_int, 0), echidna_tor_hidden_service_count());

    echidna_tor_disconnect();
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.disconnected), echidna_tor_status());
}

test "Tor: operations fail when disconnected" {
    echidna_tor_disconnect();
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    const rc = echidna_tor_create_hidden_service(80, 8080, &buf, &len);
    try std.testing.expect(rc < 0);
    try std.testing.expectEqual(@intFromEnum(OverlayError.not_connected), rc);
}

test "Tor: resolve hostname" {
    const config = "{\"control_port\":9051}";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const hostname = "example.com";
    var out: [64]u8 = undefined;
    var out_len: usize = out.len;
    const rc = echidna_tor_resolve(hostname.ptr, hostname.len, &out, &out_len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expect(out_len > 0);
}

test "Tor: list circuits" {
    const config = "{\"control_port\":9051}";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    const rc = echidna_tor_list_circuits(&buf, &len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expect(len > 0);
}

test "IPFS: connect, add, cat, pin, unpin, disconnect" {
    const config = "{\"api_port\":5001}";
    const rc = echidna_ipfs_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.connected), echidna_ipfs_status());

    // Add content
    const data = "(* proof certificate content *)";
    var cid_buf: [128]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    const add_rc = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    try std.testing.expectEqual(@as(c_int, 0), add_rc);
    try std.testing.expect(cid_len > 0);

    // Cat content back
    var content_buf: [4096]u8 = undefined;
    var content_len: usize = content_buf.len;
    const cat_rc = echidna_ipfs_cat(cid_buf[0..cid_len].ptr, cid_len, &content_buf, &content_len);
    try std.testing.expectEqual(@as(c_int, 0), cat_rc);
    try std.testing.expect(content_len > 0);

    // Pin
    const pin_rc = echidna_ipfs_pin(cid_buf[0..cid_len].ptr, cid_len);
    try std.testing.expectEqual(@as(c_int, 0), pin_rc);
    try std.testing.expectEqual(@as(c_int, 1), echidna_ipfs_pin_count());

    // Unpin
    const unpin_rc = echidna_ipfs_unpin(cid_buf[0..cid_len].ptr, cid_len);
    try std.testing.expectEqual(@as(c_int, 0), unpin_rc);
    try std.testing.expectEqual(@as(c_int, 0), echidna_ipfs_pin_count());

    echidna_ipfs_disconnect();
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.disconnected), echidna_ipfs_status());
}

test "IPFS: operations fail when disconnected" {
    echidna_ipfs_disconnect();
    const cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    const rc = echidna_ipfs_pin(cid.ptr, cid.len);
    try std.testing.expect(rc < 0);
    try std.testing.expectEqual(@intFromEnum(OverlayError.not_connected), rc);
}

test "IPFS: DAG get" {
    const config = "{\"api_port\":5001}";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    const rc = echidna_ipfs_dag_get(cid.ptr, cid.len, &buf, &len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expect(len > 0);
}

test "Ethereum: connect and timestamp (stubbed)" {
    const config = "{\"rpc_url\":\"http://127.0.0.1:8545\",\"chain_id\":1}";
    const rc = echidna_eth_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.connected), echidna_eth_status());

    // Timestamp proof (stubbed)
    const proof_hash = "a1b2c3d4e5f6789012345678abcdef0123456789abcdef0123456789abcdef01";
    var tx_buf: [1024]u8 = undefined;
    var tx_len: usize = tx_buf.len;
    const ts_rc = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &tx_buf, &tx_len);
    try std.testing.expectEqual(@as(c_int, 0), ts_rc);
    try std.testing.expect(tx_len > 0);
    // Verify the stub result contains STUBBED marker
    const result = tx_buf[0..tx_len];
    try std.testing.expect(std.mem.indexOf(u8, result, "STUBBED") != null);

    echidna_eth_disconnect();
    try std.testing.expectEqual(@intFromEnum(OverlayStatus.disconnected), echidna_eth_status());
}

test "Ethereum: verify timestamp (stubbed)" {
    const config = "{\"rpc_url\":\"http://127.0.0.1:8545\",\"chain_id\":1}";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const tx_hash = "0xdeadbeef0123456789abcdef0123456789abcdef0123456789abcdef01234567";
    var buf: [1024]u8 = undefined;
    var len: usize = buf.len;
    const rc = echidna_eth_verify_timestamp(tx_hash.ptr, tx_hash.len, &buf, &len);
    try std.testing.expectEqual(@as(c_int, 0), rc);
    try std.testing.expect(len > 0);
}

test "overlay: version and kind names" {
    const ver = echidna_overlay_version();
    try std.testing.expectEqualStrings("1.0.0", std.mem.span(ver));

    try std.testing.expectEqualStrings("Tor", std.mem.span(echidna_overlay_kind_name(0)));
    try std.testing.expectEqualStrings("IPFS", std.mem.span(echidna_overlay_kind_name(1)));
    try std.testing.expectEqualStrings("Ethereum", std.mem.span(echidna_overlay_kind_name(2)));
    try std.testing.expectEqualStrings("Unknown", std.mem.span(echidna_overlay_kind_name(99)));
}

test "overlay: error buffer" {
    clearError();
    try std.testing.expect(echidna_overlay_last_error() == null);

    // Trigger an error
    echidna_tor_disconnect();
    var buf: [8]u8 = undefined;
    var len: usize = buf.len;
    _ = echidna_tor_create_hidden_service(80, 8080, &buf, &len);

    const err = echidna_overlay_last_error() orelse return error.TestUnexpectedResult;
    try std.testing.expect(std.mem.span(err).len > 0);
}

test "IPFS: buffer too small returns required size" {
    const config = "{\"api_port\":5001}";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "test content";
    var tiny_buf: [2]u8 = undefined;
    var tiny_len: usize = tiny_buf.len;
    const rc = echidna_ipfs_add(data.ptr, data.len, &tiny_buf, &tiny_len);
    try std.testing.expectEqual(@intFromEnum(OverlayError.buffer_too_small), rc);
    // tiny_len should now contain required size
    try std.testing.expect(tiny_len > 2);
}

test "Tor: empty config rejected" {
    const dummy: [*]const u8 = "x";
    const rc = echidna_tor_connect(dummy, 0);
    try std.testing.expectEqual(@intFromEnum(OverlayError.invalid_argument), rc);
}

test "callbacks: register and unregister" {
    try std.testing.expectEqual(@as(c_int, 0), echidna_overlay_callback_count());

    const noop_status = struct {
        fn f(_: c_int, _: c_int, _: c_int) callconv(.c) void {}
    }.f;
    _ = echidna_overlay_register_on_status_change(noop_status);
    try std.testing.expectEqual(@as(c_int, 1), echidna_overlay_callback_count());

    _ = echidna_overlay_unregister_all_callbacks();
    try std.testing.expectEqual(@as(c_int, 0), echidna_overlay_callback_count());
}

test "callbacks: status change fires on connect/disconnect" {
    const Counter = struct {
        var count: u32 = 0;
        fn handler(_: c_int, _: c_int, _: c_int) callconv(.c) void {
            count += 1;
        }
    };
    Counter.count = 0;
    _ = echidna_overlay_register_on_status_change(Counter.handler);
    defer _ = echidna_overlay_unregister_all_callbacks();

    const config = "{\"control_port\":9051}";
    _ = echidna_tor_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(u32, 1), Counter.count);

    echidna_tor_disconnect();
    try std.testing.expectEqual(@as(u32, 2), Counter.count);
}

test "callbacks: pin change fires on pin/unpin" {
    const PinCounter = struct {
        var count: u32 = 0;
        fn handler(_: [*]const u8, _: usize, _: c_int, _: c_int) callconv(.c) void {
            count += 1;
        }
    };
    PinCounter.count = 0;
    _ = echidna_overlay_register_on_pin_change(PinCounter.handler);
    defer _ = echidna_overlay_unregister_all_callbacks();

    const config = "{\"api_port\":5001}";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    _ = echidna_ipfs_pin(cid.ptr, cid.len);
    try std.testing.expectEqual(@as(u32, 1), PinCounter.count);

    _ = echidna_ipfs_unpin(cid.ptr, cid.len);
    try std.testing.expectEqual(@as(u32, 2), PinCounter.count);
}

test "callbacks: error callback fires on invalid operation" {
    const ErrCounter = struct {
        var count: u32 = 0;
        var last_code: c_int = 0;
        fn handler(_: c_int, code: c_int, _: [*]const u8, _: usize) callconv(.c) void {
            count += 1;
            last_code = code;
        }
    };
    ErrCounter.count = 0;
    _ = echidna_overlay_register_on_error(ErrCounter.handler);
    defer _ = echidna_overlay_unregister_all_callbacks();

    const config = "{\"control_port\":9051}";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    // Invalid port should trigger error callback
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    _ = echidna_tor_create_hidden_service(-1, -1, &buf, &len);
    try std.testing.expectEqual(@as(u32, 1), ErrCounter.count);
    try std.testing.expectEqual(@intFromEnum(OverlayError.invalid_argument), ErrCounter.last_code);
}
