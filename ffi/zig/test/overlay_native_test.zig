// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Overlay FFI — Pure Zig Integration Tests (Native Module Import)
//
// Tests the overlay module via direct @import — NO extern "C", no C-ABI overhead.
// This is the native Zig consumer path (in-process, zero-cost).
//
// Compared to overlay_integration_test.zig (which tests the C-ABI surface),
// these tests exercise the Zig module's public types, enums, and functions
// directly as a Zig dependency would use them.
//
// Categories:
//   1. Type Tests           — enum values, conversions, null safety
//   2. Native API Tests     — direct function calls via module import
//   3. Callback Tests       — register/fire/unregister bidirectional callbacks
//   4. State Machine Tests  — valid/invalid state transitions
//   5. Roundtrip Tests      — ABI-style roundtrip patterns via native path

const std = @import("std");
const testing = std.testing;
const overlay = @import("overlay");

// ============================================================================
// 1. Type Tests — Zig enum values, conversions, null safety
// ============================================================================

test "type: OverlayKind enum values match ABI spec" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.OverlayKind.tor));
    try testing.expectEqual(@as(c_int, 1), @intFromEnum(overlay.OverlayKind.ipfs));
    try testing.expectEqual(@as(c_int, 2), @intFromEnum(overlay.OverlayKind.ethereum));
}

test "type: OverlayKind.fromInt valid values" {
    try testing.expect(overlay.OverlayKind.fromInt(0) == .tor);
    try testing.expect(overlay.OverlayKind.fromInt(1) == .ipfs);
    try testing.expect(overlay.OverlayKind.fromInt(2) == .ethereum);
}

test "type: OverlayKind.fromInt invalid values return null" {
    try testing.expect(overlay.OverlayKind.fromInt(-1) == null);
    try testing.expect(overlay.OverlayKind.fromInt(3) == null);
    try testing.expect(overlay.OverlayKind.fromInt(99) == null);
    try testing.expect(overlay.OverlayKind.fromInt(-9999) == null);
}

test "type: OverlayKind.name returns correct C strings" {
    try testing.expectEqualStrings("Tor", std.mem.span(overlay.OverlayKind.tor.name()));
    try testing.expectEqualStrings("IPFS", std.mem.span(overlay.OverlayKind.ipfs.name()));
    try testing.expectEqualStrings("Ethereum", std.mem.span(overlay.OverlayKind.ethereum.name()));
}

test "type: OverlayStatus enum values" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.OverlayStatus.disconnected));
    try testing.expectEqual(@as(c_int, 1), @intFromEnum(overlay.OverlayStatus.connecting));
    try testing.expectEqual(@as(c_int, 2), @intFromEnum(overlay.OverlayStatus.connected));
    try testing.expectEqual(@as(c_int, 3), @intFromEnum(overlay.OverlayStatus.err));
}

test "type: OverlayError enum values match Idris2 ABI error codes" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.OverlayError.ok));
    try testing.expectEqual(@as(c_int, -100), @intFromEnum(overlay.OverlayError.not_connected));
    try testing.expectEqual(@as(c_int, -101), @intFromEnum(overlay.OverlayError.connection_refused));
    try testing.expectEqual(@as(c_int, -102), @intFromEnum(overlay.OverlayError.timeout));
    try testing.expectEqual(@as(c_int, -103), @intFromEnum(overlay.OverlayError.invalid_argument));
    try testing.expectEqual(@as(c_int, -104), @intFromEnum(overlay.OverlayError.not_found));
    try testing.expectEqual(@as(c_int, -105), @intFromEnum(overlay.OverlayError.buffer_too_small));
    try testing.expectEqual(@as(c_int, -106), @intFromEnum(overlay.OverlayError.daemon_not_running));
    try testing.expectEqual(@as(c_int, -107), @intFromEnum(overlay.OverlayError.auth_failed));
    try testing.expectEqual(@as(c_int, -108), @intFromEnum(overlay.OverlayError.not_implemented));
    try testing.expectEqual(@as(c_int, -199), @intFromEnum(overlay.OverlayError.unknown));
}

test "type: TorCircuitStatus enum values" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.TorCircuitStatus.building));
    try testing.expectEqual(@as(c_int, 1), @intFromEnum(overlay.TorCircuitStatus.built));
    try testing.expectEqual(@as(c_int, 2), @intFromEnum(overlay.TorCircuitStatus.closed));
    try testing.expectEqual(@as(c_int, 3), @intFromEnum(overlay.TorCircuitStatus.failed));
}

test "type: PinStatus enum values" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.PinStatus.pinned));
    try testing.expectEqual(@as(c_int, 1), @intFromEnum(overlay.PinStatus.unpinned));
    try testing.expectEqual(@as(c_int, 2), @intFromEnum(overlay.PinStatus.pin_queued));
    try testing.expectEqual(@as(c_int, 3), @intFromEnum(overlay.PinStatus.pin_failed));
}

test "type: EthNetwork enum values" {
    try testing.expectEqual(@as(c_int, 0), @intFromEnum(overlay.EthNetwork.mainnet));
    try testing.expectEqual(@as(c_int, 1), @intFromEnum(overlay.EthNetwork.sepolia));
    try testing.expectEqual(@as(c_int, 2), @intFromEnum(overlay.EthNetwork.holesky));
    try testing.expectEqual(@as(c_int, 3), @intFromEnum(overlay.EthNetwork.local));
}

// ============================================================================
// 2. Native API Tests — direct calls via module import
// ============================================================================

test "native: echidna_overlay_version returns 1.0.0" {
    const ver = overlay.echidna_overlay_version();
    try testing.expectEqualStrings("1.0.0", std.mem.span(ver));
}

test "native: echidna_overlay_kind_name via module" {
    try testing.expectEqualStrings("Tor", std.mem.span(overlay.echidna_overlay_kind_name(0)));
    try testing.expectEqualStrings("IPFS", std.mem.span(overlay.echidna_overlay_kind_name(1)));
    try testing.expectEqualStrings("Ethereum", std.mem.span(overlay.echidna_overlay_kind_name(2)));
    try testing.expectEqualStrings("Unknown", std.mem.span(overlay.echidna_overlay_kind_name(42)));
}

test "native: tor connect-disconnect via module" {
    const config = "{\"control_port\":9051}";
    const rc = overlay.echidna_tor_connect(config.ptr, config.len);
    try testing.expectEqual(@as(c_int, 0), rc);

    const status = overlay.echidna_tor_status();
    try testing.expectEqual(@intFromEnum(overlay.OverlayStatus.connected), status);

    overlay.echidna_tor_disconnect();
    try testing.expectEqual(@intFromEnum(overlay.OverlayStatus.disconnected), overlay.echidna_tor_status());
}

test "native: ipfs full workflow via module" {
    const config = "{\"api_port\":5001}";
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_connect(config.ptr, config.len));

    // Add
    const data = "native test content";
    var cid_buf: [256]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len));
    try testing.expect(cid_len > 0);

    // Cat
    const cid = cid_buf[0..cid_len];
    var out_buf: [4096]u8 = undefined;
    var out_len: usize = out_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_cat(cid.ptr, cid.len, &out_buf, &out_len));
    try testing.expect(out_len > 0);

    // Pin
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_pin(cid.ptr, cid.len));
    try testing.expect(overlay.echidna_ipfs_pin_count() >= 1);

    // Unpin
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_unpin(cid.ptr, cid.len));

    overlay.echidna_ipfs_disconnect();
}

test "native: eth timestamp-verify via module" {
    const config = "{\"rpc_url\":\"http://127.0.0.1:8545\"}";
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_eth_connect(config.ptr, config.len));

    const proof = "0x1234abcd";
    var tx_buf: [4096]u8 = undefined;
    var tx_len: usize = tx_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_eth_timestamp_proof(proof.ptr, proof.len, &tx_buf, &tx_len));

    var vfy_buf: [4096]u8 = undefined;
    var vfy_len: usize = vfy_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_eth_verify_timestamp(tx_buf[0..tx_len].ptr, tx_len, &vfy_buf, &vfy_len));
    try testing.expect(vfy_len > 0);

    overlay.echidna_eth_disconnect();
}

test "native: error buffer via module" {
    overlay.echidna_tor_disconnect();
    // Operation on disconnected Tor should set error
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    const rc = overlay.echidna_tor_create_hidden_service(80, 8080, &buf, &len);
    try testing.expect(rc < 0);

    const err = overlay.echidna_overlay_last_error();
    try testing.expect(err != null);
    if (err) |e| {
        try testing.expect(std.mem.span(e).len > 0);
    }
}

// ============================================================================
// 3. Callback Tests — register, fire, unregister (bidirectional ABI ↔ FFI)
// ============================================================================

test "callback: register on_status_change and verify it fires" {
    const State = struct {
        var invocations: u32 = 0;
        var last_kind: c_int = -1;
        var last_old: c_int = -1;
        var last_new: c_int = -1;
        fn handler(kind: c_int, old_s: c_int, new_s: c_int) callconv(.c) void {
            invocations += 1;
            last_kind = kind;
            last_old = old_s;
            last_new = new_s;
        }
    };
    State.invocations = 0;

    _ = overlay.echidna_overlay_register_on_status_change(State.handler);
    defer _ = overlay.echidna_overlay_unregister_all_callbacks();

    try testing.expectEqual(@as(c_int, 1), overlay.echidna_overlay_callback_count());

    // Tor connect → fires status change (disconnected → connected)
    const config = "{\"control_port\":9051}";
    _ = overlay.echidna_tor_connect(config.ptr, config.len);
    try testing.expectEqual(@as(u32, 1), State.invocations);
    try testing.expectEqual(@as(c_int, 0), State.last_kind); // Tor = 0
    try testing.expectEqual(@as(c_int, 0), State.last_old); // disconnected = 0
    try testing.expectEqual(@as(c_int, 2), State.last_new); // connected = 2

    // Tor disconnect → fires again
    overlay.echidna_tor_disconnect();
    try testing.expectEqual(@as(u32, 2), State.invocations);
    try testing.expectEqual(@as(c_int, 2), State.last_old); // connected = 2
    try testing.expectEqual(@as(c_int, 0), State.last_new); // disconnected = 0
}

test "callback: register on_error and verify it fires" {
    const ErrState = struct {
        var invocations: u32 = 0;
        var last_code: c_int = 0;
        var last_msg_len: usize = 0;
        fn handler(_: c_int, code: c_int, _: [*]const u8, msg_len: usize) callconv(.c) void {
            invocations += 1;
            last_code = code;
            last_msg_len = msg_len;
        }
    };
    ErrState.invocations = 0;

    _ = overlay.echidna_overlay_register_on_error(ErrState.handler);
    defer _ = overlay.echidna_overlay_unregister_all_callbacks();

    // Connect first
    const config = "{\"control_port\":9051}";
    _ = overlay.echidna_tor_connect(config.ptr, config.len);
    defer overlay.echidna_tor_disconnect();

    // Invalid hidden service port triggers error callback
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    _ = overlay.echidna_tor_create_hidden_service(-1, -1, &buf, &len);

    try testing.expectEqual(@as(u32, 1), ErrState.invocations);
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.invalid_argument), ErrState.last_code);
    try testing.expect(ErrState.last_msg_len > 0);
}

test "callback: register on_pin_change and verify it fires" {
    const PinState = struct {
        var invocations: u32 = 0;
        var last_old_status: c_int = -1;
        var last_new_status: c_int = -1;
        fn handler(_: [*]const u8, _: usize, old_s: c_int, new_s: c_int) callconv(.c) void {
            invocations += 1;
            last_old_status = old_s;
            last_new_status = new_s;
        }
    };
    PinState.invocations = 0;

    _ = overlay.echidna_overlay_register_on_pin_change(PinState.handler);
    defer _ = overlay.echidna_overlay_unregister_all_callbacks();

    const config = "{\"api_port\":5001}";
    _ = overlay.echidna_ipfs_connect(config.ptr, config.len);
    defer overlay.echidna_ipfs_disconnect();

    const cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    _ = overlay.echidna_ipfs_pin(cid.ptr, cid.len);
    try testing.expectEqual(@as(u32, 1), PinState.invocations);
    try testing.expectEqual(@intFromEnum(overlay.PinStatus.unpinned), PinState.last_old_status);
    try testing.expectEqual(@intFromEnum(overlay.PinStatus.pinned), PinState.last_new_status);

    _ = overlay.echidna_ipfs_unpin(cid.ptr, cid.len);
    try testing.expectEqual(@as(u32, 2), PinState.invocations);
    try testing.expectEqual(@intFromEnum(overlay.PinStatus.pinned), PinState.last_old_status);
    try testing.expectEqual(@intFromEnum(overlay.PinStatus.unpinned), PinState.last_new_status);
}

test "callback: unregister_all clears all callbacks" {
    const noop_status = struct {
        fn f(_: c_int, _: c_int, _: c_int) callconv(.c) void {}
    }.f;
    const noop_error = struct {
        fn f(_: c_int, _: c_int, _: [*]const u8, _: usize) callconv(.c) void {}
    }.f;
    const noop_progress = struct {
        fn f(_: c_int, _: c_int, _: u64, _: u64) callconv(.c) void {}
    }.f;

    _ = overlay.echidna_overlay_register_on_status_change(noop_status);
    _ = overlay.echidna_overlay_register_on_error(noop_error);
    _ = overlay.echidna_overlay_register_on_progress(noop_progress);
    try testing.expectEqual(@as(c_int, 3), overlay.echidna_overlay_callback_count());

    _ = overlay.echidna_overlay_unregister_all_callbacks();
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_overlay_callback_count());
}

test "callback: null callback unregisters" {
    const noop = struct {
        fn f(_: c_int, _: c_int, _: c_int) callconv(.c) void {}
    }.f;

    _ = overlay.echidna_overlay_register_on_status_change(noop);
    try testing.expectEqual(@as(c_int, 1), overlay.echidna_overlay_callback_count());

    _ = overlay.echidna_overlay_register_on_status_change(null);
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_overlay_callback_count());
}

// ============================================================================
// 4. State Machine Tests — valid/invalid transitions
// ============================================================================

test "state: tor operations fail when disconnected" {
    overlay.echidna_tor_disconnect(); // Ensure disconnected
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;

    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_tor_create_hidden_service(80, 80, &buf, &len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_tor_list_circuits(&buf, &len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_tor_get_circuit(0, &buf, &len));

    const host = "example.com";
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_tor_resolve(host.ptr, host.len, &buf, &len));

    const onion = "test.onion";
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_tor_destroy_hidden_service(onion.ptr, onion.len));
}

test "state: ipfs operations fail when disconnected" {
    overlay.echidna_ipfs_disconnect();
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;

    const data = "test";
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_ipfs_add(data.ptr, data.len, &buf, &len));

    const cid = "bafkrei";
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_ipfs_cat(cid.ptr, cid.len, &buf, &len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_ipfs_pin(cid.ptr, cid.len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_ipfs_unpin(cid.ptr, cid.len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_ipfs_dag_get(cid.ptr, cid.len, &buf, &len));
}

test "state: eth operations fail when disconnected" {
    overlay.echidna_eth_disconnect();
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;

    const hash = "0xabcdef";
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_eth_timestamp_proof(hash.ptr, hash.len, &buf, &len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayError.not_connected), overlay.echidna_eth_verify_timestamp(hash.ptr, hash.len, &buf, &len));
}

test "state: hidden service count tracks correctly" {
    const config = "{\"control_port\":9051}";
    _ = overlay.echidna_tor_connect(config.ptr, config.len);
    defer overlay.echidna_tor_disconnect();

    try testing.expectEqual(@as(c_int, 0), overlay.echidna_tor_hidden_service_count());

    var buf1: [256]u8 = undefined;
    var len1: usize = buf1.len;
    _ = overlay.echidna_tor_create_hidden_service(80, 80, &buf1, &len1);
    try testing.expectEqual(@as(c_int, 1), overlay.echidna_tor_hidden_service_count());

    var buf2: [256]u8 = undefined;
    var len2: usize = buf2.len;
    _ = overlay.echidna_tor_create_hidden_service(443, 443, &buf2, &len2);
    try testing.expectEqual(@as(c_int, 2), overlay.echidna_tor_hidden_service_count());

    _ = overlay.echidna_tor_destroy_hidden_service(buf1[0..len1].ptr, len1);
    try testing.expectEqual(@as(c_int, 1), overlay.echidna_tor_hidden_service_count());
}

test "state: ipfs pin count tracks correctly" {
    const config = "{\"api_port\":5001}";
    _ = overlay.echidna_ipfs_connect(config.ptr, config.len);
    defer overlay.echidna_ipfs_disconnect();

    const cid = "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc";
    _ = overlay.echidna_ipfs_pin(cid.ptr, cid.len);
    _ = overlay.echidna_ipfs_pin(cid.ptr, cid.len);
    try testing.expect(overlay.echidna_ipfs_pin_count() >= 2);
}

// ============================================================================
// 5. Roundtrip Tests — full ABI-style patterns via native path
// ============================================================================

test "roundtrip: all three overlays in sequence via native module" {
    // Tor
    const tor_cfg = "{\"control_port\":9051}";
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_tor_connect(tor_cfg.ptr, tor_cfg.len));
    try testing.expectEqual(@intFromEnum(overlay.OverlayStatus.connected), overlay.echidna_tor_status());
    var onion_buf: [256]u8 = undefined;
    var onion_len: usize = onion_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_tor_create_hidden_service(80, 80, &onion_buf, &onion_len));
    _ = overlay.echidna_tor_destroy_hidden_service(onion_buf[0..onion_len].ptr, onion_len);
    overlay.echidna_tor_disconnect();

    // IPFS
    const ipfs_cfg = "{\"api_port\":5001}";
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_connect(ipfs_cfg.ptr, ipfs_cfg.len));
    const data = "roundtrip proof certificate";
    var cid_buf: [256]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len));
    var cat_buf: [4096]u8 = undefined;
    var cat_len: usize = cat_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_ipfs_cat(cid_buf[0..cid_len].ptr, cid_len, &cat_buf, &cat_len));
    overlay.echidna_ipfs_disconnect();

    // Ethereum
    const eth_cfg = "{\"rpc_url\":\"http://127.0.0.1:8545\"}";
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_eth_connect(eth_cfg.ptr, eth_cfg.len));
    const proof = "0xdeadbeef";
    var tx_buf: [4096]u8 = undefined;
    var tx_len: usize = tx_buf.len;
    try testing.expectEqual(@as(c_int, 0), overlay.echidna_eth_timestamp_proof(proof.ptr, proof.len, &tx_buf, &tx_len));
    overlay.echidna_eth_disconnect();
}

test "roundtrip: callback observes full lifecycle" {
    const Tracker = struct {
        var transitions: [16][3]c_int = undefined; // [kind, old, new]
        var count: u32 = 0;
        fn handler(kind: c_int, old_s: c_int, new_s: c_int) callconv(.c) void {
            if (count < 16) {
                transitions[count] = .{ kind, old_s, new_s };
                count += 1;
            }
        }
    };
    Tracker.count = 0;

    _ = overlay.echidna_overlay_register_on_status_change(Tracker.handler);
    defer _ = overlay.echidna_overlay_unregister_all_callbacks();

    // Tor connect + disconnect
    const tor_cfg = "{\"control_port\":9051}";
    _ = overlay.echidna_tor_connect(tor_cfg.ptr, tor_cfg.len);
    overlay.echidna_tor_disconnect();

    // IPFS connect + disconnect
    const ipfs_cfg = "{\"api_port\":5001}";
    _ = overlay.echidna_ipfs_connect(ipfs_cfg.ptr, ipfs_cfg.len);
    overlay.echidna_ipfs_disconnect();

    // Eth connect + disconnect
    const eth_cfg = "{\"rpc_url\":\"http://127.0.0.1:8545\"}";
    _ = overlay.echidna_eth_connect(eth_cfg.ptr, eth_cfg.len);
    overlay.echidna_eth_disconnect();

    // Should have 6 transitions: 3 connects + 3 disconnects
    try testing.expectEqual(@as(u32, 6), Tracker.count);

    // Verify kinds: Tor=0, IPFS=1, Eth=2
    try testing.expectEqual(@as(c_int, 0), Tracker.transitions[0][0]); // Tor connect
    try testing.expectEqual(@as(c_int, 0), Tracker.transitions[1][0]); // Tor disconnect
    try testing.expectEqual(@as(c_int, 1), Tracker.transitions[2][0]); // IPFS connect
    try testing.expectEqual(@as(c_int, 1), Tracker.transitions[3][0]); // IPFS disconnect
    try testing.expectEqual(@as(c_int, 2), Tracker.transitions[4][0]); // Eth connect
    try testing.expectEqual(@as(c_int, 2), Tracker.transitions[5][0]); // Eth disconnect
}
