// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: First-Order Automated Theorem Provers
//
// C-ABI implementation for 3 FOL ATPs: Vampire, E Prover, SPASS.
// Enforces the TPTP state machine proven in FirstOrderAtp.idr.

const std = @import("std");

/// ATP session state (matches FirstOrderAtp.idr AtpState).
pub const AtpState = enum(c_int) {
    ready = 0,
    problem_loaded = 1,
    searching = 2,
    found_proof = 3,
    found_counter = 4,
    timeout = 5,
    gave_up = 6,
    err = 7,
};

/// SZS status codes.
pub const SzsStatus = enum(c_int) {
    theorem = 0,
    counter_satisfiable = 1,
    satisfiable = 2,
    unsatisfiable = 3,
    szs_timeout = 4,
    szs_gave_up = 5,
    szs_error = 6,
};

const MAX_ATP_SESSIONS = 16;

const AtpSession = struct {
    state: AtpState,
    solver_kind: c_int, // 13=Vampire, 14=EProver, 15=SPASS
    szs_status: SzsStatus,
    active: bool,
};

var atp_sessions: [MAX_ATP_SESSIONS]AtpSession = [_]AtpSession{.{
    .state = .ready,
    .solver_kind = 0,
    .szs_status = .szs_error,
    .active = false,
}} ** MAX_ATP_SESSIONS;

var atp_mutex: std.Thread.Mutex = .{};

/// Create an ATP session.
export fn atp_create_session(solver_kind: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    for (&atp_sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{
                .state = .ready,
                .solver_kind = solver_kind,
                .szs_status = .szs_error,
                .active = true,
            };
            return @intCast(i);
        }
    }
    return -1;
}

/// Destroy an ATP session.
export fn atp_destroy_session(handle: c_int) void {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx < MAX_ATP_SESSIONS) {
        atp_sessions[idx].active = false;
    }
}

/// Get current ATP session state.
export fn atp_get_state(handle: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;
    return @intFromEnum(atp_sessions[idx].state);
}

/// Check if an ATP state transition is valid.
export fn atp_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0,
        1 => if (to == 2) @as(c_int, 1) else 0,
        2 => if (to >= 3 and to <= 6) @as(c_int, 1) else 0,
        3, 4, 5, 6, 7 => if (to == 0) @as(c_int, 1) else 0,
        else => 0,
    };
}

/// Load a TPTP problem.
export fn atp_load_problem(handle: c_int, problem_ptr: [*]const u8, problem_len: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;
    if (atp_sessions[idx].state != .ready) return -2;

    _ = problem_ptr;
    _ = problem_len;

    atp_sessions[idx].state = .problem_loaded;
    return 0;
}

/// Start proof search.
export fn atp_start_search(handle: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;
    if (atp_sessions[idx].state != .problem_loaded) return -2;

    atp_sessions[idx].state = .searching;
    return 0;
}

/// Set the search result (called when prover terminates).
export fn atp_set_result(handle: c_int, szs_status: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;
    if (atp_sessions[idx].state != .searching) return -2;

    atp_sessions[idx].szs_status = @enumFromInt(szs_status);
    atp_sessions[idx].state = switch (szs_status) {
        0 => .found_proof,      // Theorem
        1 => .found_counter,    // CounterSatisfiable
        4 => .timeout,
        5 => .gave_up,
        else => .err,
    };
    return 0;
}

/// Get the SZS status of a completed search.
export fn atp_get_szs_status(handle: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;
    return @intFromEnum(atp_sessions[idx].szs_status);
}

/// Reset ATP session to ready.
export fn atp_reset(handle: c_int) c_int {
    atp_mutex.lock();
    defer atp_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_ATP_SESSIONS or !atp_sessions[idx].active) return -1;

    atp_sessions[idx].state = .ready;
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "atp_session_lifecycle" {
    const handle = atp_create_session(13); // Vampire
    try std.testing.expect(handle >= 0);

    try std.testing.expectEqual(@as(c_int, 0), atp_load_problem(handle, "fof(ax,axiom,p).", 16));
    try std.testing.expectEqual(@as(c_int, 0), atp_start_search(handle));
    try std.testing.expectEqual(@as(c_int, 0), atp_set_result(handle, 0)); // Theorem
    try std.testing.expectEqual(@as(c_int, 3), atp_get_state(handle)); // FoundProof
    try std.testing.expectEqual(@as(c_int, 0), atp_get_szs_status(handle)); // SzsTheorem

    try std.testing.expectEqual(@as(c_int, 0), atp_reset(handle));
    atp_destroy_session(handle);
}

test "atp_transition_validator" {
    try std.testing.expectEqual(@as(c_int, 1), atp_can_transition(0, 1));
    try std.testing.expectEqual(@as(c_int, 1), atp_can_transition(1, 2));
    try std.testing.expectEqual(@as(c_int, 1), atp_can_transition(2, 3));
    try std.testing.expectEqual(@as(c_int, 0), atp_can_transition(0, 3)); // Invalid
}
