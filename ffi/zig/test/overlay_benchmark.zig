// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Overlay FFI — Benchmark Suite
//
// Measures latency and throughput of all overlay C-ABI exports.
// Run via: zig build benchmark-overlay
//
// Benchmarks:
//   1. Tor connect/disconnect cycle time
//   2. Tor hidden service create/destroy cycle
//   3. Tor resolve latency
//   4. Tor list circuits latency
//   5. IPFS connect/disconnect cycle time
//   6. IPFS add throughput (64B, 1KB, 64KB)
//   7. IPFS cat latency
//   8. IPFS pin/unpin cycle
//   9. IPFS dag_get latency
//  10. Ethereum connect/disconnect cycle time
//  11. Ethereum timestamp proof latency
//  12. Ethereum verify timestamp latency
//  13. Full Tor pipeline (connect→service→resolve→destroy→disconnect)
//  14. Full IPFS pipeline (connect→add→cat→pin→unpin→disconnect)
//  15. Full Ethereum pipeline (connect→timestamp→verify→disconnect)
//  16. Cross-overlay pipeline (all three in sequence)
//  17. Version/kind_name lookup throughput
//  18. Error buffer cycle time

const std = @import("std");

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
// Constants
// ============================================================================

const BUF_SIZE: usize = 131072; // 128KB

// ============================================================================
// Timing helpers (same pattern as benchmark.zig)
// ============================================================================

fn formatDuration(ns: u64, buf: []u8) []const u8 {
    if (ns < 1_000) {
        return std.fmt.bufPrint(buf, "{d} ns", .{ns}) catch "??";
    } else if (ns < 1_000_000) {
        const us_whole = ns / 1_000;
        const us_frac = (ns % 1_000) / 100;
        return std.fmt.bufPrint(buf, "{d}.{d} us", .{ us_whole, us_frac }) catch "??";
    } else if (ns < 1_000_000_000) {
        const ms_whole = ns / 1_000_000;
        const ms_frac = (ns % 1_000_000) / 100_000;
        return std.fmt.bufPrint(buf, "{d}.{d} ms", .{ ms_whole, ms_frac }) catch "??";
    } else {
        const s_whole = ns / 1_000_000_000;
        const s_frac = (ns % 1_000_000_000) / 100_000_000;
        return std.fmt.bufPrint(buf, "{d}.{d} s", .{ s_whole, s_frac }) catch "??";
    }
}

fn printRow(writer: anytype, name: []const u8, iterations: usize, total_ns: u64) void {
    const per_iter_ns = if (iterations > 0) total_ns / iterations else total_ns;
    var total_buf: [64]u8 = undefined;
    var per_buf: [64]u8 = undefined;
    const total_str = formatDuration(total_ns, &total_buf);
    const per_str = formatDuration(per_iter_ns, &per_buf);
    writer.print("| {s:<50} | {d:>10} | {s:>14} | {s:>14} |\n", .{
        name, iterations, total_str, per_str,
    });
}

fn printSeparator(writer: anytype) void {
    writer.print("|{s:-<52}|{s:-<12}|{s:-<16}|{s:-<16}|\n", .{
        "", "", "", "",
    });
}

const DebugWriter = struct {
    pub fn print(self: @This(), comptime fmt: []const u8, args: anytype) void {
        _ = self;
        std.debug.print(fmt, args);
    }
};

// ============================================================================
// Benchmark functions — Tor
// ============================================================================

fn benchTorConnectDisconnect(writer: anytype) void {
    const config = "control_port=9051";
    const iterations: usize = 1000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_tor_connect(config.ptr, config.len);
        echidna_tor_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "Tor connect/disconnect cycle", iterations, elapsed);
}

fn benchTorCreateDestroyService(writer: anytype) void {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const iterations: usize = 500;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var buf: [BUF_SIZE]u8 = undefined;
        var buf_len: usize = buf.len;
        const rc = echidna_tor_create_hidden_service(8080, 80, &buf, &buf_len);
        if (rc == 0 and buf_len > 0) {
            _ = echidna_tor_destroy_hidden_service(buf[0..buf_len].ptr, buf_len);
        }
    }
    const elapsed = timer.read();
    printRow(writer, "Tor create/destroy hidden service", iterations, elapsed);
}

fn benchTorResolve(writer: anytype) void {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const hostname = "example.com";
    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var buf: [BUF_SIZE]u8 = undefined;
        var buf_len: usize = buf.len;
        _ = echidna_tor_resolve(hostname.ptr, hostname.len, &buf, &buf_len);
    }
    const elapsed = timer.read();
    printRow(writer, "Tor resolve hostname", iterations, elapsed);
}

fn benchTorListCircuits(writer: anytype) void {
    const config = "control_port=9051";
    _ = echidna_tor_connect(config.ptr, config.len);
    defer echidna_tor_disconnect();

    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var buf: [BUF_SIZE]u8 = undefined;
        var buf_len: usize = buf.len;
        _ = echidna_tor_list_circuits(&buf, &buf_len);
    }
    const elapsed = timer.read();
    printRow(writer, "Tor list circuits", iterations, elapsed);
}

// ============================================================================
// Benchmark functions — IPFS
// ============================================================================

fn benchIpfsConnectDisconnect(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    const iterations: usize = 1000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_ipfs_connect(config.ptr, config.len);
        echidna_ipfs_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "IPFS connect/disconnect cycle", iterations, elapsed);
}

fn benchIpfsAdd(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const sizes = [_]struct { name: []const u8, size: usize }{
        .{ .name = "IPFS add 64B", .size = 64 },
        .{ .name = "IPFS add 1KB", .size = 1024 },
        .{ .name = "IPFS add 64KB", .size = 65536 },
    };

    for (sizes) |entry| {
        var content_buf: [65536]u8 = undefined;
        const pattern = "proof certificate data block ";
        var offset: usize = 0;
        while (offset < entry.size) {
            const remaining = entry.size - offset;
            const chunk = @min(remaining, pattern.len);
            @memcpy(content_buf[offset..][0..chunk], pattern[0..chunk]);
            offset += chunk;
        }
        const content = content_buf[0..entry.size];

        const iterations: usize = 1000;
        var timer = std.time.Timer.start() catch continue;
        for (0..iterations) |_| {
            var cid_buf: [256]u8 = undefined;
            var cid_len: usize = cid_buf.len;
            _ = echidna_ipfs_add(content.ptr, content.len, &cid_buf, &cid_len);
        }
        const elapsed = timer.read();
        printRow(writer, entry.name, iterations, elapsed);
    }
}

fn benchIpfsCat(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    // Add content first to get a CID
    const data = "benchmark cat content for ECHIDNA overlay";
    var cid_buf: [256]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var out_buf: [BUF_SIZE]u8 = undefined;
        var out_len: usize = out_buf.len;
        _ = echidna_ipfs_cat(cid.ptr, cid.len, &out_buf, &out_len);
    }
    const elapsed = timer.read();
    printRow(writer, "IPFS cat (retrieve by CID)", iterations, elapsed);
}

fn benchIpfsPinUnpin(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "benchmark pin content";
    var cid_buf: [256]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    const iterations: usize = 2000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_ipfs_pin(cid.ptr, cid.len);
        _ = echidna_ipfs_unpin(cid.ptr, cid.len);
    }
    const elapsed = timer.read();
    printRow(writer, "IPFS pin/unpin cycle", iterations, elapsed);
}

fn benchIpfsDagGet(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    _ = echidna_ipfs_connect(config.ptr, config.len);
    defer echidna_ipfs_disconnect();

    const data = "benchmark dag content";
    var cid_buf: [256]u8 = undefined;
    var cid_len: usize = cid_buf.len;
    _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
    const cid = cid_buf[0..cid_len];

    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var out_buf: [BUF_SIZE]u8 = undefined;
        var out_len: usize = out_buf.len;
        _ = echidna_ipfs_dag_get(cid.ptr, cid.len, &out_buf, &out_len);
    }
    const elapsed = timer.read();
    printRow(writer, "IPFS dag_get", iterations, elapsed);
}

// ============================================================================
// Benchmark functions — Ethereum
// ============================================================================

fn benchEthConnectDisconnect(writer: anytype) void {
    const config = "rpc_url=http://127.0.0.1:8545";
    const iterations: usize = 1000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_eth_connect(config.ptr, config.len);
        echidna_eth_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "Ethereum connect/disconnect cycle", iterations, elapsed);
}

fn benchEthTimestampProof(writer: anytype) void {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const proof_hash = "0xabcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890";
    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var out_buf: [BUF_SIZE]u8 = undefined;
        var out_len: usize = out_buf.len;
        _ = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &out_buf, &out_len);
    }
    const elapsed = timer.read();
    printRow(writer, "Ethereum timestamp proof", iterations, elapsed);
}

fn benchEthVerifyTimestamp(writer: anytype) void {
    const config = "rpc_url=http://127.0.0.1:8545";
    _ = echidna_eth_connect(config.ptr, config.len);
    defer echidna_eth_disconnect();

    const tx_hash = "0xdeadbeef1234567890abcdef1234567890abcdef1234567890abcdef12345678";
    const iterations: usize = 5000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var out_buf: [BUF_SIZE]u8 = undefined;
        var out_len: usize = out_buf.len;
        _ = echidna_eth_verify_timestamp(tx_hash.ptr, tx_hash.len, &out_buf, &out_len);
    }
    const elapsed = timer.read();
    printRow(writer, "Ethereum verify timestamp", iterations, elapsed);
}

// ============================================================================
// Full pipeline benchmarks
// ============================================================================

fn benchTorFullPipeline(writer: anytype) void {
    const config = "control_port=9051";
    const hostname = "example.com";

    const iterations: usize = 500;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_tor_connect(config.ptr, config.len);

        var onion_buf: [BUF_SIZE]u8 = undefined;
        var onion_len: usize = onion_buf.len;
        const rc = echidna_tor_create_hidden_service(8080, 80, &onion_buf, &onion_len);

        var resolve_buf: [BUF_SIZE]u8 = undefined;
        var resolve_len: usize = resolve_buf.len;
        _ = echidna_tor_resolve(hostname.ptr, hostname.len, &resolve_buf, &resolve_len);

        if (rc == 0 and onion_len > 0) {
            _ = echidna_tor_destroy_hidden_service(onion_buf[0..onion_len].ptr, onion_len);
        }

        echidna_tor_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "Tor full pipeline (connect->svc->resolve->destroy)", iterations, elapsed);
}

fn benchIpfsFullPipeline(writer: anytype) void {
    const config = "api_url=http://127.0.0.1:5001";
    const data = "Pipeline benchmark: formal proof certificate for ECHIDNA verification";

    const iterations: usize = 500;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_ipfs_connect(config.ptr, config.len);

        var cid_buf: [256]u8 = undefined;
        var cid_len: usize = cid_buf.len;
        _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
        const cid = cid_buf[0..cid_len];

        var cat_buf: [BUF_SIZE]u8 = undefined;
        var cat_len: usize = cat_buf.len;
        _ = echidna_ipfs_cat(cid.ptr, cid.len, &cat_buf, &cat_len);

        _ = echidna_ipfs_pin(cid.ptr, cid.len);
        _ = echidna_ipfs_unpin(cid.ptr, cid.len);

        echidna_ipfs_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "IPFS full pipeline (connect->add->cat->pin->unpin)", iterations, elapsed);
}

fn benchEthFullPipeline(writer: anytype) void {
    const config = "rpc_url=http://127.0.0.1:8545";
    const proof_hash = "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";

    const iterations: usize = 500;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_eth_connect(config.ptr, config.len);

        var tx_buf: [BUF_SIZE]u8 = undefined;
        var tx_len: usize = tx_buf.len;
        _ = echidna_eth_timestamp_proof(proof_hash.ptr, proof_hash.len, &tx_buf, &tx_len);

        if (tx_len > 0) {
            var verify_buf: [BUF_SIZE]u8 = undefined;
            var verify_len: usize = verify_buf.len;
            _ = echidna_eth_verify_timestamp(tx_buf[0..tx_len].ptr, tx_len, &verify_buf, &verify_len);
        }

        echidna_eth_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "Ethereum full pipeline (connect->ts->verify)", iterations, elapsed);
}

fn benchCrossOverlayPipeline(writer: anytype) void {
    const iterations: usize = 200;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        // Tor
        const tor_cfg = "control_port=9051";
        _ = echidna_tor_connect(tor_cfg.ptr, tor_cfg.len);
        _ = echidna_tor_status();
        echidna_tor_disconnect();

        // IPFS
        const ipfs_cfg = "api_url=http://127.0.0.1:5001";
        _ = echidna_ipfs_connect(ipfs_cfg.ptr, ipfs_cfg.len);
        const data = "cross-overlay bench";
        var cid_buf: [256]u8 = undefined;
        var cid_len: usize = cid_buf.len;
        _ = echidna_ipfs_add(data.ptr, data.len, &cid_buf, &cid_len);
        echidna_ipfs_disconnect();

        // Ethereum
        const eth_cfg = "rpc_url=http://127.0.0.1:8545";
        _ = echidna_eth_connect(eth_cfg.ptr, eth_cfg.len);
        _ = echidna_eth_status();
        echidna_eth_disconnect();
    }
    const elapsed = timer.read();
    printRow(writer, "Cross-overlay pipeline (Tor+IPFS+Eth)", iterations, elapsed);
}

// ============================================================================
// Utility benchmarks
// ============================================================================

fn benchVersionKindLookup(writer: anytype) void {
    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        const ver = echidna_overlay_version();
        std.mem.doNotOptimizeAway(ver);
        // All 3 overlay kinds
        var k: c_int = 0;
        while (k < 3) : (k += 1) {
            const name = echidna_overlay_kind_name(k);
            std.mem.doNotOptimizeAway(name);
        }
    }
    const elapsed = timer.read();
    printRow(writer, "Version + kind_name lookup (all 3, per batch)", iterations, elapsed);
}

fn benchErrorBufferCycle(writer: anytype) void {
    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        // Trigger an error with zero-length data
        const dummy: [*]const u8 = "x";
        _ = echidna_ipfs_pin(dummy, 0);
        const err = echidna_overlay_last_error();
        std.mem.doNotOptimizeAway(err);
    }
    const elapsed = timer.read();
    printRow(writer, "Error buffer set/get cycle", iterations, elapsed);
}

// ============================================================================
// Main entry point
// ============================================================================

pub fn main() !void {
    const w = DebugWriter{};

    w.print("\n", .{});
    w.print("==============================================================================================================\n", .{});
    w.print("                    ECHIDNA Overlay FFI - Benchmark Results (Tor / IPFS / Ethereum)                            \n", .{});
    w.print("==============================================================================================================\n", .{});
    w.print("\n", .{});

    const ver = echidna_overlay_version();
    w.print("  Version:  {s}\n", .{std.mem.span(ver)});
    w.print("  Overlays: Tor (0), IPFS (1), Ethereum (2)\n\n", .{});

    w.print("| {s:<50} | {s:>10} | {s:>14} | {s:>14} |\n", .{
        "Benchmark", "Iterations", "Total", "Per-iter",
    });
    printSeparator(w);

    // Tor benchmarks
    benchTorConnectDisconnect(w);
    benchTorCreateDestroyService(w);
    benchTorResolve(w);
    benchTorListCircuits(w);
    printSeparator(w);

    // IPFS benchmarks
    benchIpfsConnectDisconnect(w);
    benchIpfsAdd(w);
    benchIpfsCat(w);
    benchIpfsPinUnpin(w);
    benchIpfsDagGet(w);
    printSeparator(w);

    // Ethereum benchmarks
    benchEthConnectDisconnect(w);
    benchEthTimestampProof(w);
    benchEthVerifyTimestamp(w);
    printSeparator(w);

    // Full pipeline benchmarks
    benchTorFullPipeline(w);
    benchIpfsFullPipeline(w);
    benchEthFullPipeline(w);
    benchCrossOverlayPipeline(w);
    printSeparator(w);

    // Utility benchmarks
    benchVersionKindLookup(w);
    benchErrorBufferCycle(w);
    printSeparator(w);

    w.print("\nOverlay benchmark complete.\n\n", .{});
}
