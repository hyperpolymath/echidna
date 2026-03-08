// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Zig FFI — Comprehensive Integration Tests
//
// Tests the C-ABI exports from main.zig by linking against the shared library.
// Categories:
//   1. Lifecycle Tests          — init/deinit, double-init, prover create/destroy ordering
//   2. Point-to-Point Tests     — each C-ABI export with valid + invalid inputs
//   3. End-to-End Tests         — full workflow pipelines
//   4. Bidirectional Tests      — V-lang style roundtrip, error propagation
//   5. Edge Case Tests          — buffer limits, zero-length strings, boundary handles
//   6. Concurrency Tests        — multi-threaded init/create/verify/destroy
//   7. Memory Safety Tests      — create/destroy loops, leak detection via iteration count

const std = @import("std");
const testing = std.testing;

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
// Helpers
// ============================================================================

/// Total number of supported provers (must match PROVER_COUNT in main.zig).
const PROVER_COUNT: c_int = 30;

/// Standard output buffer size for export/suggest operations.
const BUF_SIZE: usize = 4096;

/// Ensure the library is initialised for a test scope; deinit on scope exit.
fn ensureInit() void {
    _ = echidna_init();
}

fn ensureDeinit() void {
    echidna_deinit();
}

// ============================================================================
// 1. Lifecycle Tests
// ============================================================================

test "lifecycle: init returns zero on success" {
    const rc = echidna_init();
    defer echidna_deinit();
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "lifecycle: double init is safe" {
    const rc1 = echidna_init();
    const rc2 = echidna_init();
    defer echidna_deinit();
    try testing.expectEqual(@as(c_int, 0), rc1);
    try testing.expectEqual(@as(c_int, 0), rc2);
}

test "lifecycle: deinit without init is safe" {
    echidna_deinit();
    // Should not crash or set an error.
}

test "lifecycle: create all 30 provers" {
    ensureInit();
    defer ensureDeinit();

    var handles: [30]c_int = undefined;
    var i: c_int = 0;
    while (i < PROVER_COUNT) : (i += 1) {
        const h = echidna_create_prover(i);
        try testing.expect(h >= 0);
        handles[@intCast(i)] = h;
    }
    // Destroy in order
    for (handles) |h| {
        echidna_destroy_prover(h);
    }
}

test "lifecycle: create all 30 provers and destroy in reverse" {
    ensureInit();
    defer ensureDeinit();

    var handles: [30]c_int = undefined;
    var i: c_int = 0;
    while (i < PROVER_COUNT) : (i += 1) {
        handles[@intCast(i)] = echidna_create_prover(i);
    }
    // Destroy in reverse order
    var j: usize = 30;
    while (j > 0) {
        j -= 1;
        echidna_destroy_prover(handles[j]);
    }
}

test "lifecycle: init-deinit-init cycle" {
    const rc1 = echidna_init();
    try testing.expectEqual(@as(c_int, 0), rc1);
    echidna_deinit();

    const rc2 = echidna_init();
    try testing.expectEqual(@as(c_int, 0), rc2);
    echidna_deinit();
}

// ============================================================================
// 2. Point-to-Point Tests
// ============================================================================

test "point: echidna_version returns non-empty string" {
    const ver = echidna_version();
    const ver_str = std.mem.span(ver);
    try testing.expect(ver_str.len > 0);
    // Should contain at least one dot (semantic version).
    try testing.expect(std.mem.indexOfScalar(u8, ver_str, '.') != null);
}

test "point: echidna_build_info returns non-empty string" {
    const info = echidna_build_info();
    const info_str = std.mem.span(info);
    try testing.expect(info_str.len > 0);
    // Should mention "ECHIDNA" or "Zig".
    try testing.expect(std.mem.indexOf(u8, info_str, "ECHIDNA") != null or
        std.mem.indexOf(u8, info_str, "Zig") != null);
}

test "point: echidna_prover_count returns 30" {
    try testing.expectEqual(@as(c_int, 30), echidna_prover_count());
}

test "point: echidna_prover_name valid kinds" {
    const expected_names = [_][]const u8{
        "Agda",    "Coq",       "Lean",     "Isabelle", "Z3",       "CVC5",
        "Metamath", "HOL Light", "Mizar",   "PVS",      "ACL2",     "HOL4",
        "Idris2",  "Vampire",   "E Prover", "SPASS",    "Alt-Ergo", "F*",
        "Dafny",   "Why3",      "TLAPS",    "Twelf",    "Nuprl",    "Minlog",
        "Imandra", "GLPK",      "SCIP",     "MiniZinc", "Chuffed",  "OR-Tools",
    };
    for (expected_names, 0..) |expected, i| {
        const name = echidna_prover_name(@intCast(i));
        try testing.expectEqualStrings(expected, std.mem.span(name));
    }
}

test "point: echidna_prover_name invalid kind returns Unknown" {
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_prover_name(-1)));
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_prover_name(30)));
    try testing.expectEqualStrings("Unknown", std.mem.span(echidna_prover_name(9999)));
}

test "point: echidna_create_prover with invalid kind returns error" {
    ensureInit();
    defer ensureDeinit();

    try testing.expect(echidna_create_prover(-1) < 0);
    try testing.expect(echidna_create_prover(30) < 0);
    try testing.expect(echidna_create_prover(9999) < 0);
}

test "point: echidna_destroy_prover with negative handle is safe" {
    ensureInit();
    defer ensureDeinit();

    echidna_destroy_prover(-1);
    echidna_destroy_prover(-9999);
    // Should not crash.
}

test "point: echidna_parse_file with valid input returns success" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0); // Agda
    try testing.expect(handle >= 0);

    const path = "test/example.agda";
    const rc = echidna_parse_file(handle, path.ptr, path.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: echidna_parse_string with valid input returns success" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(1); // Coq
    try testing.expect(handle >= 0);

    const content = "Theorem test : True. Proof. exact I. Qed.";
    const rc = echidna_parse_string(handle, content.ptr, content.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: echidna_apply_tactic with valid input returns success" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(2); // Lean
    try testing.expect(handle >= 0);

    const tactic = "intro h";
    const rc = echidna_apply_tactic(handle, tactic.ptr, tactic.len);
    try testing.expectEqual(@as(c_int, 0), rc);
}

test "point: echidna_verify_proof returns 1 for valid handle" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(3); // Isabelle
    try testing.expect(handle >= 0);

    const rc = echidna_verify_proof(handle);
    // Standalone mode returns 1 (verified).
    try testing.expectEqual(@as(c_int, 1), rc);
}

test "point: echidna_verify_proof with negative handle returns error" {
    ensureInit();
    defer ensureDeinit();

    const rc = echidna_verify_proof(-1);
    try testing.expect(rc < 0);
}

test "point: echidna_last_error is null after successful operations" {
    ensureInit();
    defer ensureDeinit();

    // After a clean init, error should be null.
    const err = echidna_last_error();
    try testing.expect(err == null);
}

test "point: echidna_last_error is set after invalid create" {
    ensureInit();
    defer ensureDeinit();

    _ = echidna_create_prover(-1);
    const err = echidna_last_error();
    try testing.expect(err != null);
    if (err) |e| {
        const msg = std.mem.span(e);
        try testing.expect(msg.len > 0);
    }
}

// ============================================================================
// 3. End-to-End Tests
// ============================================================================

test "e2e: full workflow init-create-parse-verify-export-suggest-destroy-deinit" {
    // Init
    const init_rc = echidna_init();
    try testing.expectEqual(@as(c_int, 0), init_rc);

    // Create prover (Lean, kind=2)
    const handle = echidna_create_prover(2);
    try testing.expect(handle >= 0);

    // Parse string
    const content = "theorem test : True := trivial";
    const parse_rc = echidna_parse_string(handle, content.ptr, content.len);
    try testing.expectEqual(@as(c_int, 0), parse_rc);

    // Apply tactic
    const tactic = "exact trivial";
    const tactic_rc = echidna_apply_tactic(handle, tactic.ptr, tactic.len);
    try testing.expectEqual(@as(c_int, 0), tactic_rc);

    // Verify proof
    const verify_rc = echidna_verify_proof(handle);
    try testing.expectEqual(@as(c_int, 1), verify_rc);

    // Export proof
    var export_buf: [BUF_SIZE]u8 = undefined;
    var export_len: usize = export_buf.len;
    const export_rc = echidna_export_proof(handle, &export_buf, &export_len);
    try testing.expectEqual(@as(c_int, 0), export_rc);
    try testing.expect(export_len > 0);

    // Suggest tactics
    var suggest_buf: [BUF_SIZE]u8 = undefined;
    var suggest_len: usize = suggest_buf.len;
    const suggest_rc = echidna_suggest_tactics(handle, 5, &suggest_buf, &suggest_len);
    try testing.expectEqual(@as(c_int, 0), suggest_rc);
    try testing.expect(suggest_len > 0);

    // Destroy prover
    echidna_destroy_prover(handle);

    // Deinit
    echidna_deinit();
}

test "e2e: multiple provers in sequence" {
    ensureInit();
    defer ensureDeinit();

    // Create, use, destroy provers in sequence across different kinds.
    const kinds = [_]c_int{ 0, 4, 12, 17, 25, 29 }; // Agda, Z3, Idris2, F*, GLPK, OR-Tools
    for (kinds) |kind| {
        const handle = echidna_create_prover(kind);
        try testing.expect(handle >= 0);

        const content = "test content";
        _ = echidna_parse_string(handle, content.ptr, content.len);

        const verify_rc = echidna_verify_proof(handle);
        try testing.expectEqual(@as(c_int, 1), verify_rc);

        echidna_destroy_prover(handle);
    }
}

// ============================================================================
// 4. Bidirectional Tests (V-lang style roundtrip)
// ============================================================================

test "bidi: V-lang REST/gRPC roundtrip pattern" {
    // Simulates the call pattern used by the V-lang adapter:
    // init → create → parse_string → verify → export → destroy → deinit
    ensureInit();

    const handle = echidna_create_prover(1); // Coq
    try testing.expect(handle >= 0);

    // Simulated proof content from a gRPC request
    const proof_content = "Lemma identity : forall (A : Type) (a : A), a = a. Proof. intros. reflexivity. Qed.";
    const parse_rc = echidna_parse_string(handle, proof_content.ptr, proof_content.len);
    try testing.expectEqual(@as(c_int, 0), parse_rc);

    // Verify
    const verify_rc = echidna_verify_proof(handle);
    try testing.expectEqual(@as(c_int, 1), verify_rc);

    // Export for response
    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const export_rc = echidna_export_proof(handle, &buf, &buf_len);
    try testing.expectEqual(@as(c_int, 0), export_rc);
    try testing.expect(buf_len > 0);

    // Verify the exported data is valid UTF-8
    const exported = buf[0..buf_len];
    try testing.expect(std.unicode.utf8ValidateSlice(exported));

    echidna_destroy_prover(handle);
    ensureDeinit();
}

test "bidi: error propagation through error buffer" {
    ensureInit();
    defer ensureDeinit();

    // Trigger an error by using an invalid prover kind
    const bad_handle = echidna_create_prover(999);
    try testing.expect(bad_handle < 0);

    // Error buffer should have a message
    const err = echidna_last_error();
    try testing.expect(err != null);
    if (err) |e| {
        const msg = std.mem.span(e);
        try testing.expect(msg.len > 0);
        // Should mention "prover" or "kind" or "Invalid"
        const has_context = std.mem.indexOf(u8, msg, "prover") != null or
            std.mem.indexOf(u8, msg, "kind") != null or
            std.mem.indexOf(u8, msg, "Invalid") != null or
            std.mem.indexOf(u8, msg, "invalid") != null;
        try testing.expect(has_context);
    }
}

test "bidi: error cleared on successful operation" {
    ensureInit();
    defer ensureDeinit();

    // First trigger an error
    _ = echidna_create_prover(-1);
    try testing.expect(echidna_last_error() != null);

    // Successful init should clear it (init calls clearError)
    _ = echidna_init();
    try testing.expect(echidna_last_error() == null);
}

// ============================================================================
// 5. Edge Case Tests
// ============================================================================

test "edge: export proof with buffer too small" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    // Use a tiny buffer that cannot hold the exported proof
    var tiny_buf: [1]u8 = undefined;
    var tiny_len: usize = tiny_buf.len;
    const rc = echidna_export_proof(handle, &tiny_buf, &tiny_len);
    // Should return an error code (buffer too small → -2 = error_invalid_argument)
    try testing.expect(rc != 0);
    // tiny_len should be set to the required size
    try testing.expect(tiny_len > 1);
}

test "edge: suggest tactics with buffer too small" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    var tiny_buf: [1]u8 = undefined;
    var tiny_len: usize = tiny_buf.len;
    const rc = echidna_suggest_tactics(handle, 3, &tiny_buf, &tiny_len);
    try testing.expect(rc != 0);
    try testing.expect(tiny_len > 1);
}

test "edge: parse_file with zero-length path" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    const dummy: [*]const u8 = "x";
    const rc = echidna_parse_file(handle, dummy, 0);
    try testing.expect(rc != 0);
}

test "edge: parse_string with zero-length content" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    const dummy: [*]const u8 = "x";
    const rc = echidna_parse_string(handle, dummy, 0);
    try testing.expect(rc != 0);
}

test "edge: apply_tactic with zero-length tactic" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    const dummy: [*]const u8 = "x";
    const rc = echidna_apply_tactic(handle, dummy, 0);
    try testing.expect(rc != 0);
}

test "edge: negative handles rejected by all operations" {
    ensureInit();
    defer ensureDeinit();

    const dummy: [*]const u8 = "test";
    try testing.expect(echidna_parse_file(-1, dummy, 4) != 0);
    try testing.expect(echidna_parse_string(-1, dummy, 4) != 0);
    try testing.expect(echidna_apply_tactic(-1, dummy, 4) != 0);
    try testing.expect(echidna_verify_proof(-1) < 0);

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    try testing.expect(echidna_export_proof(-1, &buf, &buf_len) != 0);
    try testing.expect(echidna_suggest_tactics(-1, 3, &buf, &buf_len) != 0);
}

test "edge: suggest_tactics with negative limit" {
    ensureInit();
    defer ensureDeinit();

    const handle = echidna_create_prover(0);
    try testing.expect(handle >= 0);

    var buf: [BUF_SIZE]u8 = undefined;
    var buf_len: usize = buf.len;
    const rc = echidna_suggest_tactics(handle, -1, &buf, &buf_len);
    try testing.expect(rc != 0);
}

test "edge: all 30 prover kinds can be created and verified" {
    ensureInit();
    defer ensureDeinit();

    var i: c_int = 0;
    while (i < PROVER_COUNT) : (i += 1) {
        const handle = echidna_create_prover(i);
        try testing.expect(handle >= 0);

        const verify_rc = echidna_verify_proof(handle);
        try testing.expectEqual(@as(c_int, 1), verify_rc);

        echidna_destroy_prover(handle);
    }
}

// ============================================================================
// 6. Concurrency Tests
// ============================================================================

test "concurrency: 4 threads create-verify-destroy simultaneously" {
    ensureInit();
    defer ensureDeinit();

    const thread_fn = struct {
        fn run(kind: c_int) void {
            const handle = echidna_create_prover(kind);
            if (handle < 0) return;

            const content = "concurrent proof content";
            _ = echidna_parse_string(handle, content.ptr, content.len);

            _ = echidna_verify_proof(handle);

            var buf: [BUF_SIZE]u8 = undefined;
            var buf_len: usize = buf.len;
            _ = echidna_export_proof(handle, &buf, &buf_len);

            echidna_destroy_prover(handle);
        }
    }.run;

    var threads: [4]std.Thread = undefined;
    const kinds = [4]c_int{ 0, 5, 12, 29 }; // Agda, CVC5, Idris2, OR-Tools
    for (&threads, kinds) |*thread, kind| {
        thread.* = try std.Thread.spawn(.{}, thread_fn, .{kind});
    }
    for (threads) |thread| {
        thread.join();
    }
}

test "concurrency: 4 threads reading version and prover names" {
    const thread_fn = struct {
        fn run(offset: usize) void {
            for (0..100) |_| {
                const ver = echidna_version();
                const ver_str = std.mem.span(ver);
                if (ver_str.len == 0) return; // Should never happen

                const name = echidna_prover_name(@intCast(offset));
                const name_str = std.mem.span(name);
                if (name_str.len == 0) return; // Should never happen

                _ = echidna_build_info();
                _ = echidna_prover_count();
            }
        }
    }.run;

    var threads: [4]std.Thread = undefined;
    for (&threads, 0..) |*thread, i| {
        thread.* = try std.Thread.spawn(.{}, thread_fn, .{i * 7}); // kinds 0, 7, 14, 21
    }
    for (threads) |thread| {
        thread.join();
    }
}

// ============================================================================
// 7. Memory Safety Tests
// ============================================================================

test "memory: create-destroy loop 1000 times" {
    ensureInit();
    defer ensureDeinit();

    for (0..1000) |_| {
        const handle = echidna_create_prover(0); // Agda
        if (handle < 0) {
            // Should not happen — fail the test.
            return error.TestUnexpectedResult;
        }
        echidna_destroy_prover(handle);
    }
}

test "memory: init-deinit loop 100 times" {
    for (0..100) |_| {
        const rc = echidna_init();
        try testing.expectEqual(@as(c_int, 0), rc);
        echidna_deinit();
    }
}

test "memory: create all 30 provers, verify all, destroy all — 50 iterations" {
    ensureInit();
    defer ensureDeinit();

    for (0..50) |_| {
        var handles: [30]c_int = undefined;
        var i: c_int = 0;
        while (i < PROVER_COUNT) : (i += 1) {
            handles[@intCast(i)] = echidna_create_prover(i);
        }
        for (handles) |h| {
            if (h >= 0) {
                _ = echidna_verify_proof(h);
            }
        }
        for (handles) |h| {
            if (h >= 0) {
                echidna_destroy_prover(h);
            }
        }
    }
}
