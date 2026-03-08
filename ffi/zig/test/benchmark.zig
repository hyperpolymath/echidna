// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Zig FFI — Benchmark Suite
//
// Measures latency and throughput of all C-ABI exports.
// Run via: zig build benchmark
//
// Benchmarks:
//   1. Init/deinit cycle time
//   2. Create/destroy prover cycle per kind (all 30)
//   3. Parse string throughput (64B, 1KB, 64KB)
//   4. Verify proof latency
//   5. Export proof latency with varying buffer sizes
//   6. Suggest tactics latency
//   7. Full pipeline latency (create→parse→verify→export→destroy)
//   8. Prover name lookup throughput (all 30 kinds, 10000 iterations)
//   9. Error buffer set/get cycle time

const std = @import("std");

// ============================================================================
// C-ABI extern declarations (linked from libechidna_ffi)
// ============================================================================

extern "C" fn echidna_init() c_int;
extern "C" fn echidna_deinit() void;
extern "C" fn echidna_create_prover(kind: c_int) c_int;
extern "C" fn echidna_destroy_prover(handle: c_int) void;
extern "C" fn echidna_parse_file(handle: c_int, path_ptr: [*]const u8, path_len: usize) c_int;
extern "C" fn echidna_parse_string(handle: c_int, content_ptr: [*]const u8, content_len: usize) c_int;
extern "C" fn echidna_apply_tactic(handle: c_int, tactic_ptr: [*]const u8, tactic_len: usize) c_int;
extern "C" fn echidna_verify_proof(handle: c_int) c_int;
extern "C" fn echidna_export_proof(handle: c_int, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_suggest_tactics(handle: c_int, limit: c_int, out_ptr: [*]u8, out_len: *usize) c_int;
extern "C" fn echidna_version() [*:0]const u8;
extern "C" fn echidna_prover_count() c_int;
extern "C" fn echidna_prover_name(kind: c_int) [*:0]const u8;
extern "C" fn echidna_last_error() ?[*:0]const u8;
extern "C" fn echidna_build_info() [*:0]const u8;

// ============================================================================
// Constants
// ============================================================================

const PROVER_COUNT: c_int = 30;
const BUF_SIZE: usize = 131072; // 128KB — large enough for all operations

/// Prover names for table output (must match ProverKind ordinals 0..29).
const prover_names = [_][]const u8{
    "Agda",     "Coq",       "Lean",      "Isabelle",  "Z3",        "CVC5",
    "Metamath", "HOL Light", "Mizar",     "PVS",       "ACL2",      "HOL4",
    "Idris2",   "Vampire",   "E Prover",  "SPASS",     "Alt-Ergo",  "F*",
    "Dafny",    "Why3",      "TLAPS",     "Twelf",     "Nuprl",     "Minlog",
    "Imandra",  "GLPK",      "SCIP",      "MiniZinc",  "Chuffed",   "OR-Tools",
};

// ============================================================================
// Timing helpers
// ============================================================================

/// Measure the elapsed nanoseconds for a given number of iterations of a function.
fn benchmarkNs(comptime func: anytype, args: anytype, iterations: usize) u64 {
    var timer = std.time.Timer.start() catch return 0;
    for (0..iterations) |_| {
        @call(.auto, func, args);
    }
    return timer.read();
}

/// Format nanoseconds as a human-readable duration string.
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

/// Print a benchmark row: name, iterations, total time, per-iteration time.
fn printRow(writer: anytype, name: []const u8, iterations: usize, total_ns: u64) void {
    const per_iter_ns = if (iterations > 0) total_ns / iterations else total_ns;
    var total_buf: [64]u8 = undefined;
    var per_buf: [64]u8 = undefined;
    const total_str = formatDuration(total_ns, &total_buf);
    const per_str = formatDuration(per_iter_ns, &per_buf);
    writer.print("| {s:<45} | {d:>10} | {s:>14} | {s:>14} |\n", .{
        name, iterations, total_str, per_str,
    });
}

fn printSeparator(writer: anytype) void {
    writer.print("|{s:-<47}|{s:-<12}|{s:-<16}|{s:-<16}|\n", .{
        "", "", "", "",
    });
}

// ============================================================================
// Individual benchmark functions
// ============================================================================

fn benchInitDeinit(writer: anytype) void {
    const iterations: usize = 1000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_init();
        echidna_deinit();
    }
    const elapsed = timer.read();
    printRow(writer, "Init/deinit cycle", iterations, elapsed);
}

fn benchCreateDestroyPerKind(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const iterations: usize = 1000;
    var i: c_int = 0;
    while (i < PROVER_COUNT) : (i += 1) {
        var timer = std.time.Timer.start() catch continue;
        for (0..iterations) |_| {
            const h = echidna_create_prover(i);
            if (h >= 0) echidna_destroy_prover(h);
        }
        const elapsed = timer.read();
        var name_buf: [64]u8 = undefined;
        const label = std.fmt.bufPrint(&name_buf, "Create/destroy {s}", .{
            prover_names[@intCast(i)],
        }) catch "Create/destroy ??";
        printRow(writer, label, iterations, elapsed);
    }
}

fn benchParseString(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(0); // Agda
    if (handle < 0) return;
    defer echidna_destroy_prover(handle);

    const sizes = [_]struct { name: []const u8, size: usize }{
        .{ .name = "Parse string 64B", .size = 64 },
        .{ .name = "Parse string 1KB", .size = 1024 },
        .{ .name = "Parse string 64KB", .size = 65536 },
    };

    for (sizes) |entry| {
        // Generate content of the target size (repeat a pattern).
        var content_buf: [65536]u8 = undefined;
        const pattern = "theorem t : A -> A := fun x => x\n";
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
            _ = echidna_parse_string(handle, content.ptr, content.len);
        }
        const elapsed = timer.read();
        printRow(writer, entry.name, iterations, elapsed);
    }
}

fn benchVerifyProof(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(2); // Lean
    if (handle < 0) return;
    defer echidna_destroy_prover(handle);

    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_verify_proof(handle);
    }
    const elapsed = timer.read();
    printRow(writer, "Verify proof", iterations, elapsed);
}

fn benchExportProof(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(1); // Coq
    if (handle < 0) return;
    defer echidna_destroy_prover(handle);

    const buf_sizes = [_]struct { name: []const u8, size: usize }{
        .{ .name = "Export proof (256B buf)", .size = 256 },
        .{ .name = "Export proof (4KB buf)", .size = 4096 },
        .{ .name = "Export proof (64KB buf)", .size = 65536 },
    };

    for (buf_sizes) |entry| {
        var buf: [65536]u8 = undefined;
        const iterations: usize = 10000;
        var timer = std.time.Timer.start() catch continue;
        for (0..iterations) |_| {
            var buf_len: usize = entry.size;
            _ = echidna_export_proof(handle, &buf, &buf_len);
        }
        const elapsed = timer.read();
        printRow(writer, entry.name, iterations, elapsed);
    }
}

fn benchSuggestTactics(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(0); // Agda
    if (handle < 0) return;
    defer echidna_destroy_prover(handle);

    var buf: [BUF_SIZE]u8 = undefined;
    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var buf_len: usize = buf.len;
        _ = echidna_suggest_tactics(handle, 5, &buf, &buf_len);
    }
    const elapsed = timer.read();
    printRow(writer, "Suggest tactics (limit=5)", iterations, elapsed);
}

fn benchFullPipeline(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    const content = "Theorem pipeline_test : forall A, A -> A. Proof. auto. Qed.";
    var buf: [BUF_SIZE]u8 = undefined;

    const iterations: usize = 1000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        const handle = echidna_create_prover(1); // Coq
        if (handle < 0) continue;

        _ = echidna_parse_string(handle, content.ptr, content.len);
        _ = echidna_verify_proof(handle);

        var buf_len: usize = buf.len;
        _ = echidna_export_proof(handle, &buf, &buf_len);

        echidna_destroy_prover(handle);
    }
    const elapsed = timer.read();
    printRow(writer, "Full pipeline (create->export->destroy)", iterations, elapsed);
}

fn benchProverNameLookup(writer: anytype) void {
    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        var i: c_int = 0;
        while (i < PROVER_COUNT) : (i += 1) {
            const name = echidna_prover_name(i);
            // Prevent the compiler from optimising the call away.
            std.mem.doNotOptimizeAway(name);
        }
    }
    const elapsed = timer.read();
    printRow(writer, "Prover name lookup (all 30, per batch)", iterations, elapsed);
}

fn benchErrorBufferCycle(writer: anytype) void {
    _ = echidna_init();
    defer echidna_deinit();

    // Each iteration: trigger an error (invalid create) then read it back.
    const iterations: usize = 10000;
    var timer = std.time.Timer.start() catch return;
    for (0..iterations) |_| {
        _ = echidna_create_prover(-1); // Sets error
        const err = echidna_last_error(); // Reads error
        std.mem.doNotOptimizeAway(err);
    }
    const elapsed = timer.read();
    printRow(writer, "Error buffer set/get cycle", iterations, elapsed);
}

// ============================================================================
// Main entry point
// ============================================================================

/// Wrapper that provides .print() using std.debug.print (writes to stderr).
const DebugWriter = struct {
    pub fn print(self: @This(), comptime fmt: []const u8, args: anytype) void {
        _ = self;
        std.debug.print(fmt, args);
    }
};

pub fn main() !void {
    const w = DebugWriter{};

    // Header
    w.print("\n", .{});
    w.print("==============================================================================================================\n", .{});
    w.print("                        ECHIDNA Zig FFI - Benchmark Results                                                   \n", .{});
    w.print("==============================================================================================================\n", .{});
    w.print("\n", .{});

    // Version info
    const ver = echidna_version();
    const info = echidna_build_info();
    w.print("  Version:    {s}\n", .{std.mem.span(ver)});
    w.print("  Build info: {s}\n", .{std.mem.span(info)});
    w.print("  Provers:    {d}\n\n", .{echidna_prover_count()});

    // Table header
    w.print("| {s:<45} | {s:>10} | {s:>14} | {s:>14} |\n", .{
        "Benchmark", "Iterations", "Total", "Per-iter",
    });
    printSeparator(w);

    // Run benchmarks
    benchInitDeinit(w);
    printSeparator(w);

    benchCreateDestroyPerKind(w);
    printSeparator(w);

    benchParseString(w);
    printSeparator(w);

    benchVerifyProof(w);
    printSeparator(w);

    benchExportProof(w);
    printSeparator(w);

    benchSuggestTactics(w);
    printSeparator(w);

    benchFullPipeline(w);
    printSeparator(w);

    benchProverNameLookup(w);
    printSeparator(w);

    benchErrorBufferCycle(w);
    printSeparator(w);

    w.print("\nBenchmark complete.\n\n", .{});
}
