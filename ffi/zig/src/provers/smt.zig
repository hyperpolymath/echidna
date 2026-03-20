// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: SMT Solvers
//
// C-ABI implementation for 3 SMT solvers: Z3, CVC5, Alt-Ergo.
// Enforces the SMT-LIB2 state machine proven in SmtSolvers.idr.
// Thread-safe via mutex-guarded per-session state.

const std = @import("std");

/// SMT session state (matches SmtSolvers.idr SmtState).
pub const SmtState = enum(c_int) {
    ready = 0,
    asserted = 1,
    checking = 2,
    sat = 3,
    unsat = 4,
    unknown = 5,
    err = 6,
};

/// Certificate format.
pub const CertFormat = enum(c_int) {
    alethe = 0,
    drat_lrat = 1,
    no_cert = 2,
};

const MAX_SMT_SESSIONS = 32;

const SmtSession = struct {
    state: SmtState,
    solver_kind: c_int, // 4=Z3, 5=CVC5, 16=AltErgo
    stack_depth: u32,
    assertions: u32,
    active: bool,
};

var smt_sessions: [MAX_SMT_SESSIONS]SmtSession = [_]SmtSession{.{
    .state = .ready,
    .solver_kind = 0,
    .stack_depth = 0,
    .assertions = 0,
    .active = false,
}} ** MAX_SMT_SESSIONS;

var smt_mutex: std.Thread.Mutex = .{};

/// Create an SMT solver session.
export fn smt_create_session(solver_kind: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    for (&smt_sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{
                .state = .ready,
                .solver_kind = solver_kind,
                .stack_depth = 0,
                .assertions = 0,
                .active = true,
            };
            return @intCast(i);
        }
    }
    return -1;
}

/// Destroy an SMT session.
export fn smt_destroy_session(handle: c_int) void {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx < MAX_SMT_SESSIONS) {
        smt_sessions[idx].active = false;
        smt_sessions[idx].state = .ready;
    }
}

/// Get current SMT session state.
export fn smt_get_state(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    return @intFromEnum(smt_sessions[idx].state);
}

/// Check if an SMT state transition is valid (mirrors Idris2 proof).
export fn smt_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0,
        1 => if (to == 1 or to == 2) @as(c_int, 1) else 0,
        2 => if (to >= 3 and to <= 5) @as(c_int, 1) else 0,
        3, 4, 5, 6 => if (to == 0) @as(c_int, 1) else 0,
        else => 0,
    };
}

/// Assert a formula (SMT-LIB2 assert command).
export fn smt_assert(handle: c_int, formula_ptr: [*]const u8, formula_len: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    if (smt_sessions[idx].state != .ready and smt_sessions[idx].state != .asserted) return -2;

    _ = formula_ptr;
    _ = formula_len;

    smt_sessions[idx].state = .asserted;
    smt_sessions[idx].assertions += 1;
    return 0;
}

/// Check satisfiability (SMT-LIB2 check-sat command).
export fn smt_check_sat(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    if (smt_sessions[idx].state != .asserted) return -2;

    smt_sessions[idx].state = .checking;
    return 0;
}

/// Set the satisfiability result (called after solver responds).
export fn smt_set_result(handle: c_int, result: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    if (smt_sessions[idx].state != .checking) return -2;

    smt_sessions[idx].state = switch (result) {
        0 => .sat,
        1 => .unsat,
        else => .unknown,
    };
    return 0;
}

/// Push assertion context (stack discipline).
export fn smt_push(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;

    smt_sessions[idx].stack_depth += 1;
    return 0;
}

/// Pop assertion context (stack discipline — enforces depth > 0).
export fn smt_pop(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    if (smt_sessions[idx].stack_depth == 0) return -2; // Can't pop empty stack

    smt_sessions[idx].stack_depth -= 1;
    return 0;
}

/// Get stack depth.
export fn smt_stack_depth(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;
    return @intCast(smt_sessions[idx].stack_depth);
}

/// Reset SMT session to ready state.
export fn smt_reset(handle: c_int) c_int {
    smt_mutex.lock();
    defer smt_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SMT_SESSIONS or !smt_sessions[idx].active) return -1;

    smt_sessions[idx].state = .ready;
    smt_sessions[idx].stack_depth = 0;
    smt_sessions[idx].assertions = 0;
    return 0;
}

/// Get certificate format for a solver.
export fn smt_cert_format(solver_kind: c_int) c_int {
    return switch (solver_kind) {
        4 => @intFromEnum(CertFormat.alethe), // Z3
        5 => @intFromEnum(CertFormat.alethe), // CVC5
        16 => @intFromEnum(CertFormat.no_cert), // Alt-Ergo
        else => -1,
    };
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "smt_session_lifecycle" {
    const handle = smt_create_session(4); // Z3
    try std.testing.expect(handle >= 0);

    // Assert
    try std.testing.expectEqual(@as(c_int, 0), smt_assert(handle, "(= x 1)", 7));
    try std.testing.expectEqual(@as(c_int, 1), smt_get_state(handle));

    // Check-sat
    try std.testing.expectEqual(@as(c_int, 0), smt_check_sat(handle));
    try std.testing.expectEqual(@as(c_int, 2), smt_get_state(handle));

    // Result: SAT
    try std.testing.expectEqual(@as(c_int, 0), smt_set_result(handle, 0));
    try std.testing.expectEqual(@as(c_int, 3), smt_get_state(handle));

    // Reset
    try std.testing.expectEqual(@as(c_int, 0), smt_reset(handle));
    smt_destroy_session(handle);
}

test "smt_stack_discipline" {
    const handle = smt_create_session(5); // CVC5
    try std.testing.expectEqual(@as(c_int, 0), smt_stack_depth(handle));

    try std.testing.expectEqual(@as(c_int, 0), smt_push(handle));
    try std.testing.expectEqual(@as(c_int, 1), smt_stack_depth(handle));

    try std.testing.expectEqual(@as(c_int, 0), smt_pop(handle));
    try std.testing.expectEqual(@as(c_int, 0), smt_stack_depth(handle));

    // Pop on empty stack should fail
    try std.testing.expectEqual(@as(c_int, -2), smt_pop(handle));

    smt_destroy_session(handle);
}

test "smt_transition_validator" {
    try std.testing.expectEqual(@as(c_int, 1), smt_can_transition(0, 1)); // Ready → Asserted
    try std.testing.expectEqual(@as(c_int, 1), smt_can_transition(1, 2)); // Asserted → Checking
    try std.testing.expectEqual(@as(c_int, 1), smt_can_transition(2, 4)); // Checking → Unsat
    try std.testing.expectEqual(@as(c_int, 0), smt_can_transition(0, 3)); // Invalid
}
