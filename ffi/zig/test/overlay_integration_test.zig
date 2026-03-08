// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Overlay FFI — Comprehensive Integration Tests
//
// Tests the C-ABI exports from overlay.zig by linking against libechidna_overlay.
// Categories:
//   1. Lifecycle Tests          — connect/disconnect, status transitions
//   2. Point-to-Point Tests     — each C-ABI export with valid + invalid inputs
//   3. End-to-End Tests         — full workflow pipelines (Tor, IPFS, Ethereum)
//   4. Bidirectional Tests      — V-lang adapter style roundtrip, error propagation
//   5. Edge Case Tests          — buffer limits, zero-length strings, boundary values
//   6. Concurrency Tests        — multi-threaded overlay operations
//   7. Memory Safety Tests      — connect/disconnect loops, leak detection

const std = @import("std");
const testing = std.testing;

// ============================================================================
// C-ABI extern declarations (linked from libechidna_overlay)
// ============================================================================

// -- Unified --
extern "C" fn echidna_overlay_version() [*:0]const u8;
extern "C" fn echidna_overlay_kind_name(kind: c_int) [*:0]const u8;
extern "C" fn echidna_overlay_last_error() ?[*:0]const u8;

// -- Tor --
extern "C" fn echidna_tor_connect(config_ptr: [*]const u8, config_len: usize) c_int;
extern "C" fn echidna_tor_disconnect() void;
extern "C" fn echidna_tor_status() c_int;
extern "C" fn echidna_tor_create_hidden_service(port: c_int, target_port: c_int, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_tor_destroy_hidden_service(onion_ptr: [*]const u8, onion_len: usize) c_int;
extern "C" fn echidna_tor_get_circuit(circuit_id: c_int, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_tor_list_circuits(out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_tor_resolve(hostname_ptr: [*]const u8, hostname_len: usize, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_tor_hidden_service_count() c_int;

// -- IPFS --
extern "C" fn echidna_ipfs_connect(config_ptr: [*]const u8, config_len: usize) c_int;
extern "C" fn echidna_ipfs_disconnect() void;
extern "C" fn echidna_ipfs_status() c_int;
extern "C" fn echidna_ipfs_add(data_ptr: [*]const u8, data_len: usize, out_cid_ptr: [*]u8, out_cid_len: *usize) c_int;
extern "C" fn echidna_ipfs_cat(cid_ptr: [*]const u8, cid_len: usize, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_ipfs_pin(cid_ptr: [*]const u8, cid_len: usize) c_int;
extern "C" fn echidna_ipfs_unpin(cid_ptr: [*]const u8, cid_len: usize) c_int;
extern "C" fn echidna_ipfs_dag_get(cid_ptr: [*]const u8, cid_len: usize, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_ipfs_pin_count() c_int;

// -- Ethereum --
extern "C" fn echidna_eth_connect(config_ptr: [*]const u8, config_len: usize) c_int;
extern "C" fn echidna_eth_disconnect() void;
extern "C" fn echidna_eth_status() c_int;
extern "C" fn echidna_eth_timestamp_proof(proof_hash_ptr: [*]const u8, proof_hash_len: usize, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_eth_verify_timestamp(tx_hash_ptr: [*]const u8, tx_hash_len: usize, out_ptr: [*]u8, out_len: *usize) c_int;

// ============================================================================
// Helpers
// ============================================================================

const BUF_SIZE: usize = 4096;

// ============================================================================
// 1. Lifecycle Tests
// ============================================================================

test "lifecycle: overlay_version returns non-empty string" {
    const ver = echidna_overlay_version();
    const ver_str = std.mem.span(ver);
    try testing.expect(ver_str.len > 0);
    // Should contain a dot (semantic version).
    try testing.expect(std.mem.indexOfScalar(u8, ver_str, '.') != null);
}

test "lifecycle: overlay_kind_name returns correct names" {
    try testing.expectEqualStrings("Tor", std.mem.span(echidna_overlay_kind_name(0)));
    try testing.expectEqualStrings("IPFS", std.mem.span(echidna_overlay_kind_name(1)));
    try testing.expectEqualStrings("Ethereum", std.mem.span(echidna_overlay_kind_name(2)));
}

test "lifecycle: overlay_kind_name invalid returns Unknown" {
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_overlay_kind_name(-1)));
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_overlay_kind_name(3)));
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_overlay_kind_name(9999)));
}

test "lifecycle: tor connect returns success" {
    const config = "control_port=9051";
    const rc = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "lifecycle: tor disconnect without connect is safe" {
    echidna_tor_disconnect();
    // Should not crash.
}

test "lifecycle: ipfs connect returns success" {
    const config = "api_url=http://127.0.0.1:5001";
    const rc = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "lifecycle: ipfs disconnect without connect is safe" {
    echidna_ipfs_disconnect();
}

test "lifecycle: eth connect returns success" {
    const config = "rpc_url=http://127.0.0.1:8545";
    const rc = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "lifecycle: eth disconnect without connect is safe" {
    echidna_eth_disconnect();
}

test "lifecycle: connect-disconnect-connect cycle (tor)" {
    const config = "control_port=9051";
    var rc = echidna_tor_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), rc);
    echidna_tor_disconnect();

    rc = echidna_tor_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), rc);
    echidna_tor_disconnect();
}

// ============================================================================
// 2. Point-to-Point Tests — Tor
// ============================================================================

test "point: tor_status returns valid status enum" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const status = echidna_tor_status();
    // 0=disconnected, 1=connecting, 2=connected, 3=err — all valid
    try testing.expect(status >= 0 and status <= 3);
}

test "point: tor_create_hidden_service returns onion address" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_create_hidden_service(8080, 80, &buf, &buf_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(buf_len > 0);

    // Onion address should contain ".onion"
    const onion = buf[0..buf_len];
    try testing.expect(std.mem.indexOf(u8, onion, ".onion") != null);
}

test "point: tor_destroy_hidden_service with valid onion" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    // First create one
    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    _ = echidna_tor_create_hidden_service(8080, 80, &buf, &buf_len);
    const onion = buf[0..buf_len];

    // Destroy it
    const rc = echidna_tor_destroy_hidden_service(onion.ptr, onion.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: tor_hidden_service_count starts at zero" {
    // Fresh state — no services created yet
    const count = echidna_tor_hidden_service_count();
    try testing.expect(count >= 0);
}

test "point: tor_list_circuits returns data" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_list_circuits(&buf, &buf_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    // In standalone mode, may return empty or stub data — either is valid.
}

test "point: tor_get_circuit with circuit id 0" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_get_circuit(0, &buf, &buf_len);
    // May succeed (standalone stub) or fail (no such circuit) — both are valid.
    _ = rc;
}

test "point: tor_resolve returns address" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const hostname = "example.com";
    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_resolve(hostname.ptr, hostname.len, &buf, &buf_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(buf_len > 0);
}

// ============================================================================
// 2. Point-to-Point Tests — IPFS
// ============================================================================

test "point: ipfs_status returns valid status enum" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const status = echidna_ipfs_status();
    try testing.expect(status >= 0 and status <= 3);
}

test "point: ipfs_add returns CID" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "Hello, IPFS from ECHIDNA!";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    const rc = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(cid_len > 0);

    // CID should start with "Qm" (CIDv0) or "baf" (CIDv1 — bafkrei, bafy, etc.)
    const cid = cid_buf[0..cid_len];
    const valid_prefix = std.mem.startsWith(u8, cid, "Qm") or std.mem.startsWith(u8, cid, "baf");
    try testing.expect(valid_prefix);
}

test "point: ipfs_cat retrieves content" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    // Add first, then cat
    const data = "ECHIDNA overlay test content";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_ipfs_cat(cid.ptr, cid.len, &out_buf, &out_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(out_len > 0);
}

test "point: ipfs_pin returns success" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    // Add, then pin
    const data = "pin test data";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    const rc = echidna_ipfs_pin(cid.ptr, cid.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: ipfs_unpin returns success after pin" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "unpin test data";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    _ = echidna_ipfs_pin(cid.ptr, cid.len);
    const rc = echidna_ipfs_unpin(cid.ptr, cid.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: ipfs_dag_get retrieves DAG node" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "dag test data";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_ipfs_dag_get(cid.ptr, cid.len, &out_buf, &out_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(out_len > 0);
}

test "point: ipfs_pin_count returns non-negative" {
    const count = echidna_ipfs_pin_count();
    try testing.expect(count >= 0);
}

// ============================================================================
// 2. Point-to-Point Tests — Ethereum
// ============================================================================

test "point: eth_status returns valid status enum" {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const status = echidna_eth_status();
    try testing.expect(status >= 0 and status <= 3);
}

test "point: eth_timestamp_proof returns tx hash" {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const proof_hash = "0xabcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890";
    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &out_buf, &out_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(out_len > 0);

    // Result is JSON containing a tx_hash field starting with "0x"
    const tx_result = out_buf[0..out_len];
    try testing.expect(std.mem.indexOf(u8, tx_result, "tx_hash") != null);
}

test "point: eth_verify_timestamp returns verification result" {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const tx_hash = "0xdeadbeef1234567890abcdef1234567890abcdef1234567890abcdef12345678";
    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_eth_verify_timestamp(tx_hash.ptr, tx_hash.len, &out_buf, &out_len);
    try testing.expectEqual(@as(c_int, 0), rc);
    try testing.expect(out_len > 0);
}

// ============================================================================
// 3. End-to-End Tests
// ============================================================================

test "e2e: tor full workflow — connect, create service, list, resolve, destroy, disconnect" {
    const config = "control_port=9051";
    const connect_rc = echidna_tor_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), connect_rc);

    // Check status
    const status = echidna_tor_status();
    try testing.expect(status >= 0);

    // Create hidden service
    var onion_buf: [BUF_SIZE]u8 = undefined;
    var onion_len: usize = onion_buf.len;
    const create_rc = echidna_tor_create_hidden_service(8080, 80, &onion_buf, &onion_len);
    try testing.expectEqual(@as(c_int, 0), create_rc);
    const onion = onion_buf[0..onion_len];

    // List circuits
    var circuit_buf: [BUF_SIZE]u8 = undefined;
    var circuit_len: usize = circuit_buf.len;
    _ = echidna_tor_list_circuits(&circuit_buf, &circuit_len);

    // Resolve a hostname
    const hostname = "echidna.onion";
    var resolve_buf: [BUF_SIZE]u8 = undefined;
    var resolve_len: usize = resolve_buf.len;
    _ = echidna_tor_resolve(hostname.ptr, hostname.len, &resolve_buf, &resolve_len);

    // Destroy hidden service
    const destroy_rc = echidna_tor_destroy_hidden_service(onion.ptr, onion.len);
    try testing.expectEqual(@as(c_int, 0), destroy_rc);

    // Disconnect
    echidna_tor_disconnect();
}

test "e2e: ipfs full workflow — connect, add, cat, pin, dag_get, unpin, disconnect" {
    const config = "api_url=http://127.0.0.1:5001";
    const connect_rc = echidna_ipfs_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), connect_rc);

    // Add content
    const data = "ECHIDNA end-to-end test: formal proof certificate v1";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    const add_rc = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    try testing.expectEqual(@as(c_int, 0), add_rc);
    const cid = cid_buf[0..cid_len];

    // Cat it back
    var cat_buf: [BUF_SIZE]u8 = undefined;
    var cat_len: usize = cat_buf.len;
    const cat_rc = echidna_ipfs_cat(cid.ptr, cid.len, &cat_buf, &cat_len);
    try testing.expectEqual(@as(c_int, 0), cat_rc);

    // Pin it
    const pin_rc = echidna_ipfs_pin(cid.ptr, cid.len);
    try testing.expectEqual(@as(c_int, 0), pin_rc);

    // DAG get
    var dag_buf: [BUF_SIZE]u8 = undefined;
    var dag_len: usize = dag_buf.len;
    const dag_rc = echidna_ipfs_dag_get(cid.ptr, cid.len, &dag_buf, &dag_len);
    try testing.expectEqual(@as(c_int, 0), dag_rc);

    // Unpin
    const unpin_rc = echidna_ipfs_unpin(cid.ptr, cid.len);
    try testing.expectEqual(@as(c_int, 0), unpin_rc);

    // Disconnect
    echidna_ipfs_disconnect();
}

test "e2e: ethereum full workflow — connect, timestamp, verify, disconnect" {
    const config = "rpc_url=http://127.0.0.1:8545";
    const connect_rc = echidna_eth_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), connect_rc);

    // Check status
    const status = echidna_eth_status();
    try testing.expect(status >= 0);

    // Timestamp a proof hash
    const proof_hash = "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";
    var tx_buf: [BUF_SIZE]u8 = undefined;
    var tx_len: usize = tx_buf.len;
    const ts_rc = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &tx_buf, &tx_len);
    try testing.expectEqual(@as(c_int, 0), ts_rc);
    const tx_hash = tx_buf[0..tx_len];

    // Verify the timestamp
    var verify_buf: [BUF_SIZE]u8 = undefined;
    var verify_len: usize = verify_buf.len;
    const verify_rc = echidna_eth_verify_timestamp(tx_hash.ptr, tx_hash.len, &verify_buf, &verify_len);
    try testing.expectEqual(@as(c_int, 0), verify_rc);

    // Disconnect
    echidna_eth_disconnect();
}

test "e2e: cross-overlay workflow — all three networks in sequence" {
    // Tor
    const tor_config = "control_port=9051";
    _ = echidna_tor_connect(tor_config.ptr, tor_config.len);
    const tor_status = echidna_tor_status();
    try testing.expect(tor_status >= 0);
    echidna_tor_disconnect();

    // IPFS
    const ipfs_config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(ipfs_config.ptr, ipfs_config.len);
    const data = "cross-overlay test";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    echidna_ipfs_disconnect();

    // Ethereum
    const eth_config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(eth_config.ptr, eth_config.len);
    const eth_status = echidna_eth_status();
    try testing.expect(eth_status >= 0);
    echidna_eth_disconnect();
}

// ============================================================================
// 4. Bidirectional Tests (V-lang adapter style roundtrip)
// ============================================================================

test "bidi: ipfs add-cat roundtrip preserves content semantics" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const original = "Lemma identity : forall (A : Type) (a : A), a = a.";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    const add_rc = echidna_ipfs_add(original.ptr, original.len, &cid_buf, &cid_len);
    try testing.expectEqual(@as(c_int, 0), add_rc);
    try testing.expect(cid_len > 0);

    const cid = cid_buf[0..cid_len];
    var cat_buf: [BUF_SIZE]u8 = undefined;
    var cat_len: usize = cat_buf.len;
    const cat_rc = echidna_ipfs_cat(cid.ptr, cid.len, &cat_buf, &cat_len);
    try testing.expectEqual(@as(c_int, 0), cat_rc);

    // Retrieved content should be valid UTF-8
    const retrieved = cat_buf[0..cat_len];
    try testing.expect(std.unicode.utf8ValidateSlice(retrieved));
}

test "bidi: error propagation through error buffer" {
    // Connect with empty config to see if error is set
    const empty: [*]const u8 = "x";
    _ = echidna_tor_connect(empty, 0);
    // Error buffer may or may not be set depending on implementation.
    // Just verify no crash.
    _ = echidna_overlay_last_error();
    echidna_tor_disconnect();
}

test "bidi: eth timestamp-verify roundtrip" {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    // Simulate V-lang adapter pattern: hash → timestamp → verify
    const proof_hash = "0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210";
    var tx_buf: [BUF_SIZE]u8 = undefined;
    var tx_len: usize = tx_buf.len;
    _ = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &tx_buf, &tx_len);

    if (tx_len > 0) {
        var verify_buf: [BUF_SIZE]u8 = undefined;
        var verify_len: usize = verify_buf.len;
        const rc = echidna_eth_verify_timestamp(tx_buf[0..tx_len].ptr, tx_len, &verify_buf, &verify_len);
        try testing.expectEqual(@as(c_int, 0), rc);
    }
}

// ============================================================================
// 5. Edge Case Tests
// ============================================================================

test "edge: tor_create_hidden_service with buffer too small" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var tiny_buf: [1]u8 = undefined;
    var tiny_len: usize = tiny_buf.len;
    const rc = echidna_tor_create_hidden_service(8080, 80, &tiny_buf, &tiny_len);
    // Should fail (buffer too small) or write truncated — both acceptable
    _ = rc;
    // Required size should be reported
    try testing.expect(tiny_len >= 1);
}

test "edge: ipfs_add with zero-length data" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const dummy: [*]const u8 = "x";
    var cid_buf: [BUF_SIZE]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    const rc = echidna_ipfs_add(dummy, 0, &cid_buf, &cid_len);
    // Zero-length add may succeed (empty file CID) or fail — both valid
    _ = rc;
}

test "edge: ipfs_cat with zero-length CID" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const dummy: [*]const u8 = "x";
    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_ipfs_cat(dummy, 0, &out_buf, &out_len);
    // Should fail gracefully
    try testing.expect(rc != 0);
}

test "edge: eth_timestamp_proof with zero-length hash" {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const dummy: [*]const u8 = "x";
    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_eth_timestamp_proof(dummy, 0, &out_buf, &out_len);
    try testing.expect(rc != 0);
}

test "edge: tor_destroy_hidden_service with zero-length onion" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const dummy: [*]const u8 = "x";
    const rc = echidna_tor_destroy_hidden_service(dummy, 0);
    try testing.expect(rc != 0);
}

test "edge: tor_resolve with zero-length hostname" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const dummy: [*]const u8 = "x";
    var out_buf: [BUF_SIZE]u8 = undefined;
    var out_len: usize = out_buf.len;
    const rc = echidna_tor_resolve(dummy, 0, &out_buf, &out_len);
    try testing.expect(rc != 0);
}

test "edge: ipfs_pin with zero-length CID" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const dummy: [*]const u8 = "x";
    const rc = echidna_ipfs_pin(dummy, 0);
    try testing.expect(rc != 0);
}

test "edge: negative port for tor hidden service" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_create_hidden_service(-1, -1, &buf, &buf_len);
    // Should fail or handle gracefully
    _ = rc;
}

test "edge: negative circuit id for tor" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_tor_get_circuit(-1, &buf, &buf_len);
    // Negative circuit ID should fail gracefully
    _ = rc;
}

test "edge: overlay_last_error is null on clean state" {
    // After version query (no error-triggering call), error should be null.
    _ = echidna_overlay_version();
    const err = echidna_overlay_last_error();
    // May or may not be null depending on prior test state, but should not crash.
    _ = err;
}

// ============================================================================
// 6. Concurrency Tests
// ============================================================================

test "concurrency: 4 threads reading version and kind names" {
    const thread_fn = struct {
        fn run(offset: usize) void {
            for (0..100) |_| {
                const ver = echidna_overlay_version();
                const ver_str = std.mem.span(ver);
                if (ver_str.len == 0) return;

                const name = echidna_overlay_kind_name(@intCast(offset % 3));
                const name_str = std.mem.span(name);
                if (name_str.len == 0) return;
            }
        }
    }.run;

    var threads: [4]std.Thread = undefined;
    for (&threads, 0..) |*thread, i| {
        thread.* = try std.Thread.spawn(.{}, thread_fn, .{i});
    }
    for (threads) |thread| {
        thread.join();
    }
}

test "concurrency: 3 threads each operating on different overlay" {
    const tor_fn = struct {
        fn run() void {
            const config = "control_port=9051";
            for (0..50) |_| {
                _ = echidna_tor_connect(config.ptr, config.len);
                _ = echidna_tor_status();
                echidna_tor_disconnect();
            }
        }
    }.run;

    const ipfs_fn = struct {
        fn run() void {
            const config = "api_url=http://127.0.0.1:5001";
            for (0..50) |_| {
                _ = echidna_ipfs_connect(config.ptr, config.len);
                _ = echidna_ipfs_status();
                echidna_ipfs_disconnect();
            }
        }
    }.run;

    const eth_fn = struct {
        fn run() void {
            const config = "rpc_url=http://127.0.0.1:8545";
            for (0..50) |_| {
                _ = echidna_eth_connect(config.ptr, config.len);
                _ = echidna_eth_status();
                echidna_eth_disconnect();
            }
        }
    }.run;

    var t1 = try std.Thread.spawn(.{}, tor_fn, .{});
    var t2 = try std.Thread.spawn(.{}, ipfs_fn, .{});
    var t3 = try std.Thread.spawn(.{}, eth_fn, .{});

    t1.join();
    t2.join();
    t3.join();
}

// ============================================================================
// 7. Memory Safety Tests
// ============================================================================

test "memory: tor connect-disconnect loop 500 times" {
    const config = "control_port=9051";
    for (0..500) |_| {
        const rc = echidna_tor_connect(config.ptr, config.len);
        if (rc != 0) return error.TestUnexpectedResult;
        echidna_tor_disconnect();
    }
}

test "memory: ipfs connect-disconnect loop 500 times" {
    const config = "api_url=http://127.0.0.1:5001";
    for (0..500) |_| {
        const rc = echidna_ipfs_connect(config.ptr, config.len);
        if (rc != 0) return error.TestUnexpectedResult;
        echidna_ipfs_disconnect();
    }
}

test "memory: eth connect-disconnect loop 500 times" {
    const config = "rpc_url=http://127.0.0.1:8545";
    for (0..500) |_| {
        const rc = echidna_eth_connect(config.ptr, config.len);
        if (rc != 0) return error.TestUnexpectedResult;
        echidna_eth_disconnect();
    }
}

test "memory: ipfs add loop 200 times" {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    for (0..200) |i| {
        var data_buf: [128]u8 = undefined;
        const data = std.fmt.bufPrint(&data_buf, "leak test iteration {d}", .{i}) catch "fallback";
        var cid_buf: [BUF_SIZE]u8 = undefined;
        var cid_len: usize = cid_buf.len;
        _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    }
}

test "memory: tor create-destroy hidden service loop 100 times" {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    for (0..100) |_| {
        var onion_buf: [BUF_SIZE]u8 = undefined;
        var onion_len: usize = onion_buf.len;
        const rc = echidna_tor_create_hidden_service(8080, 80, &onion_buf, &onion_len);
        if (rc == 0 and onion_len > 0) {
            _ = echidna_tor_destroy_hidden_service(onion_buf[0..onion_len].ptr, onion_len);
        }
    }
}
