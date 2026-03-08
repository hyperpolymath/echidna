// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Core FFI — Pure Zig Native Tests
//
// Tests the core FFI module via direct Zig @import (no C-ABI overhead).
// Validates types, enums, lifecycle, callbacks, and safe wrapper API.

const std = @import("std");
const testing = std.testing;
const core = @import("core");

// ============================================================================
// Type and enum tests
// ============================================================================

test "FfiStatus: all variants round-trip through fromInt" {
    const cases = [_]struct { val: c_int, expected: core.FfiStatus }{
        .{ .val = 0, .expected = .ok },
        .{ .val = -1, .expected = .error_invalid_handle },
        .{ .val = -2, .expected = .error_invalid_argument },
        .{ .val = -3, .expected = .error_prover_not_found },
        .{ .val = -4, .expected = .error_parse_failure },
        .{ .val = -5, .expected = .error_tactic_failure },
        .{ .val = -6, .expected = .error_verification_failure },
        .{ .val = -7, .expected = .error_out_of_memory },
        .{ .val = -8, .expected = .error_timeout },
        .{ .val = -9, .expected = .error_not_implemented },
        .{ .val = -99, .expected = .error_unknown },
    };
    for (cases) |c| {
        try testing.expectEqual(c.expected, core.FfiStatus.fromInt(c.val));
    }
    // Unknown values → error_unknown
    try testing.expectEqual(core.FfiStatus.error_unknown, core.FfiStatus.fromInt(-42));
    try testing.expectEqual(core.FfiStatus.error_unknown, core.FfiStatus.fromInt(100));
}

test "FfiStatus: isOk semantics" {
    try testing.expect(core.FfiStatus.ok.isOk());
    try testing.expect(!core.FfiStatus.error_timeout.isOk());
    try testing.expect(!core.FfiStatus.error_unknown.isOk());
}

test "ProverKind: all 30 variants have valid ordinals" {
    var i: c_int = 0;
    while (i < 30) : (i += 1) {
        const pk = core.ProverKind.fromInt(i);
        try testing.expect(pk != null);
        try testing.expectEqual(i, pk.?.toInt());
    }
}

test "ProverKind: out-of-range returns null" {
    try testing.expect(core.ProverKind.fromInt(-1) == null);
    try testing.expect(core.ProverKind.fromInt(30) == null);
    try testing.expect(core.ProverKind.fromInt(255) == null);
}

test "ProverKind: name strings are non-empty" {
    const provers = [_]core.ProverKind{
        .agda, .coq, .lean, .isabelle, .z3, .cvc5,
        .metamath, .hol_light, .mizar, .pvs, .acl2,
        .hol4, .idris2, .vampire, .eprover, .spass,
        .alt_ergo, .fstar, .dafny, .why3, .tlaps,
        .twelf, .nuprl, .minlog, .imandra, .glpk,
        .scip, .minizinc, .chuffed, .ortools,
    };
    for (provers) |pk| {
        const n = std.mem.span(pk.name());
        try testing.expect(n.len > 0);
    }
}

test "ProverKind: tier values are 1-5" {
    try testing.expectEqual(@as(u8, 1), core.ProverKind.agda.tier());
    try testing.expectEqual(@as(u8, 1), core.ProverKind.fstar.tier());
    try testing.expectEqual(@as(u8, 2), core.ProverKind.metamath.tier());
    try testing.expectEqual(@as(u8, 3), core.ProverKind.pvs.tier());
    try testing.expectEqual(@as(u8, 4), core.ProverKind.hol4.tier());
    try testing.expectEqual(@as(u8, 5), core.ProverKind.vampire.tier());
    try testing.expectEqual(@as(u8, 5), core.ProverKind.ortools.tier());
}

test "TacticResultKind: enum values" {
    try testing.expectEqual(@as(u8, 0), @intFromEnum(core.TacticResultKind.success));
    try testing.expectEqual(@as(u8, 1), @intFromEnum(core.TacticResultKind.err));
    try testing.expectEqual(@as(u8, 2), @intFromEnum(core.TacticResultKind.qed));
}

test "TermKind: all 13 variants" {
    try testing.expectEqual(@as(u8, 0), @intFromEnum(core.TermKind.variable));
    try testing.expectEqual(@as(u8, 12), @intFromEnum(core.TermKind.prover_specific));
}

test "TacticKind: all 10 variants" {
    try testing.expectEqual(@as(u8, 0), @intFromEnum(core.TacticKind.apply));
    try testing.expectEqual(@as(u8, 9), @intFromEnum(core.TacticKind.custom));
}

// ============================================================================
// StringSlice tests
// ============================================================================

test "StringSlice: fromSlice round-trip" {
    const data = "echidna proof certificate";
    const ss = core.StringSlice.fromSlice(data);
    try testing.expectEqual(data.len, ss.len);
    try testing.expectEqualStrings(data, ss.toSlice());
}

test "StringSlice: empty is safe" {
    const ss = core.StringSlice.empty();
    try testing.expectEqual(@as(usize, 0), ss.len);
    try testing.expect(ss.ptr == null);
    try testing.expectEqual(@as(usize, 0), ss.toSlice().len);
}

// ============================================================================
// Safe wrapper API tests
// ============================================================================

test "init/deinit lifecycle via safe API" {
    try core.init();
    const handle = try core.createProver(.lean);
    try testing.expectEqual(core.ProverKind.lean, handle.kind);
    try testing.expect(handle.id > 0);

    core.destroyProver(handle);
    core.deinit();
}

test "createProver fails before init" {
    // Force uninitialised state
    core.deinit();
    const result = core.createProver(.agda);
    try testing.expect(result == error.InvalidHandle);
}

test "parseFile rejects empty path" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.coq);
    const result = core.parseFile(handle, "");
    try testing.expect(result == error.InvalidArgument);
}

test "parseString rejects empty content" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.z3);
    const result = core.parseString(handle, "");
    try testing.expect(result == error.InvalidArgument);
}

test "applyTactic rejects empty tactic" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.isabelle);
    const result = core.applyTactic(handle, "");
    try testing.expect(result == error.InvalidArgument);
}

test "verifyProof returns true in standalone mode" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.lean);
    const valid = try core.verifyProof(handle);
    try testing.expect(valid);
}

test "exportProof returns non-empty in standalone mode" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.agda);
    const proof = try core.exportProof(handle);
    try testing.expect(proof.len > 0);
}

test "suggestTactics returns non-empty in standalone mode" {
    try core.init();
    defer core.deinit();
    const handle = try core.createProver(.coq);
    const tactics = try core.suggestTactics(handle, 5);
    try testing.expect(tactics.len > 0);
}

// ============================================================================
// C-ABI export tests via native path
// ============================================================================

test "echidna_version returns correct version" {
    const ver = core.echidna_version();
    try testing.expectEqualStrings("1.5.0", std.mem.span(ver));
}

test "echidna_prover_count is 30" {
    try testing.expectEqual(@as(c_int, 30), core.echidna_prover_count());
}

test "echidna_prover_name for all kinds" {
    try testing.expectEqualStrings("Agda", std.mem.span(core.echidna_prover_name(0)));
    try testing.expectEqualStrings("OR-Tools", std.mem.span(core.echidna_prover_name(29)));
    try testing.expectEqualStrings("Unknown", std.mem.span(core.echidna_prover_name(-1)));
    try testing.expectEqualStrings("Unknown", std.mem.span(core.echidna_prover_name(30)));
}

test "echidna_build_info is non-empty" {
    const info = core.echidna_build_info();
    try testing.expect(std.mem.span(info).len > 0);
}

// ============================================================================
// Callback tests
// ============================================================================

test "callback: register and count" {
    try testing.expectEqual(@as(c_int, 0), core.echidna_callback_count());

    const noop = struct {
        fn f(_: c_int, _: c_int) callconv(.c) void {}
    }.f;
    _ = core.echidna_register_on_init_change(noop);
    try testing.expectEqual(@as(c_int, 1), core.echidna_callback_count());

    const noop_prover = struct {
        fn f(_: c_int, _: c_int, _: c_int) callconv(.c) void {}
    }.f;
    _ = core.echidna_register_on_prover_change(noop_prover);
    try testing.expectEqual(@as(c_int, 2), core.echidna_callback_count());

    _ = core.echidna_unregister_all_callbacks();
    try testing.expectEqual(@as(c_int, 0), core.echidna_callback_count());
}

test "callback: init change fires on lifecycle" {
    const State = struct {
        var transitions: u32 = 0;
        var last_old: c_int = -1;
        var last_new: c_int = -1;
        fn handler(old: c_int, new: c_int) callconv(.c) void {
            transitions += 1;
            last_old = old;
            last_new = new;
        }
    };
    State.transitions = 0;
    _ = core.echidna_register_on_init_change(State.handler);
    defer _ = core.echidna_unregister_all_callbacks();

    _ = core.echidna_init();
    try testing.expectEqual(@as(u32, 1), State.transitions);
    try testing.expectEqual(@as(c_int, 0), State.last_old); // uninit → init
    try testing.expectEqual(@as(c_int, 1), State.last_new);

    core.echidna_deinit();
    try testing.expectEqual(@as(u32, 2), State.transitions);
    try testing.expectEqual(@as(c_int, 1), State.last_old); // init → uninit
    try testing.expectEqual(@as(c_int, 0), State.last_new);
}

test "callback: prover change tracks create and destroy" {
    const State = struct {
        var creates: u32 = 0;
        var destroys: u32 = 0;
        fn handler(_: c_int, _: c_int, created: c_int) callconv(.c) void {
            if (created == 1) creates += 1 else destroys += 1;
        }
    };
    State.creates = 0;
    State.destroys = 0;
    _ = core.echidna_register_on_prover_change(State.handler);
    defer _ = core.echidna_unregister_all_callbacks();

    _ = core.echidna_init();
    defer core.echidna_deinit();

    const h1 = core.echidna_create_prover(0); // Agda
    const h2 = core.echidna_create_prover(2); // Lean
    try testing.expectEqual(@as(u32, 2), State.creates);
    try testing.expectEqual(@as(u32, 0), State.destroys);

    core.echidna_destroy_prover(h1);
    core.echidna_destroy_prover(h2);
    try testing.expectEqual(@as(u32, 2), State.creates);
    try testing.expectEqual(@as(u32, 2), State.destroys);
}

test "callback: verify complete fires with correct result" {
    const State = struct {
        var fired: bool = false;
        var result: c_int = -1;
        fn handler(_: c_int, _: c_int, verified: c_int) callconv(.c) void {
            fired = true;
            result = verified;
        }
    };
    State.fired = false;
    _ = core.echidna_register_on_verify_complete(State.handler);
    defer _ = core.echidna_unregister_all_callbacks();

    _ = core.echidna_init();
    defer core.echidna_deinit();

    const handle = core.echidna_create_prover(2); // Lean
    _ = core.echidna_verify_proof(handle);
    try testing.expect(State.fired);
    try testing.expectEqual(@as(c_int, 1), State.result); // standalone always verified
}

test "callback: null callback unregisters" {
    const noop = struct {
        fn f(_: c_int, _: c_int) callconv(.c) void {}
    }.f;
    _ = core.echidna_register_on_init_change(noop);
    try testing.expectEqual(@as(c_int, 1), core.echidna_callback_count());

    _ = core.echidna_register_on_init_change(null);
    try testing.expectEqual(@as(c_int, 0), core.echidna_callback_count());
}
