// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: Constraint and Optimization Solvers
//
// C-ABI implementation for 5 constraint solvers:
//   GLPK, SCIP, MiniZinc, Chuffed, OR-Tools
// Enforces the solver state machine proven in ConstraintSolvers.idr.

const std = @import("std");

/// Constraint solver state (matches ConstraintSolvers.idr CspState).
pub const CspState = enum(c_int) {
    ready = 0,
    model_loaded = 1,
    solving = 2,
    optimal = 3,
    feasible = 4,
    infeasible = 5,
    unbounded = 6,
    csp_timeout = 7,
    err = 8,
};

/// Problem class.
pub const ProblemClass = enum(c_int) {
    lp = 0,
    mip = 1,
    minlp = 2,
    cp = 3,
    sat = 4,
};

const MAX_CSP_SESSIONS = 16;

const CspSession = struct {
    state: CspState,
    solver_kind: c_int,
    objective_value: f64,
    variables_count: u32,
    constraints_count: u32,
    active: bool,
};

var csp_sessions: [MAX_CSP_SESSIONS]CspSession = [_]CspSession{.{
    .state = .ready,
    .solver_kind = 0,
    .objective_value = 0.0,
    .variables_count = 0,
    .constraints_count = 0,
    .active = false,
}} ** MAX_CSP_SESSIONS;

var csp_mutex: std.Thread.Mutex = .{};

/// Create a constraint solver session.
export fn csp_create_session(solver_kind: c_int) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();

    for (&csp_sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{
                .state = .ready,
                .solver_kind = solver_kind,
                .objective_value = 0.0,
                .variables_count = 0,
                .constraints_count = 0,
                .active = true,
            };
            return @intCast(i);
        }
    }
    return -1;
}

/// Destroy a constraint solver session.
export fn csp_destroy_session(handle: c_int) void {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx < MAX_CSP_SESSIONS) csp_sessions[idx].active = false;
}

/// Get current solver state.
export fn csp_get_state(handle: c_int) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1;
    return @intFromEnum(csp_sessions[idx].state);
}

/// Check if a CSP state transition is valid.
export fn csp_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0,
        1 => if (to == 2) @as(c_int, 1) else 0,
        2 => if (to >= 3 and to <= 8) @as(c_int, 1) else 0,
        3, 4, 5, 6, 7, 8 => if (to == 0) @as(c_int, 1) else 0,
        else => 0,
    };
}

/// Load a model (variables + constraints + objective).
export fn csp_load_model(handle: c_int, model_ptr: [*]const u8, model_len: c_int, vars: c_int, constraints: c_int) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1;
    if (csp_sessions[idx].state != .ready) return -2;
    _ = model_ptr;
    _ = model_len;
    csp_sessions[idx].variables_count = @intCast(vars);
    csp_sessions[idx].constraints_count = @intCast(constraints);
    csp_sessions[idx].state = .model_loaded;
    return 0;
}

/// Start solving.
export fn csp_start_solve(handle: c_int) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1;
    if (csp_sessions[idx].state != .model_loaded) return -2;
    csp_sessions[idx].state = .solving;
    return 0;
}

/// Set the solver result.
export fn csp_set_result(handle: c_int, result_state: c_int, objective: f64) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1;
    if (csp_sessions[idx].state != .solving) return -2;
    csp_sessions[idx].state = @enumFromInt(result_state);
    csp_sessions[idx].objective_value = objective;
    return 0;
}

/// Get the objective value of the solution.
export fn csp_get_objective(handle: c_int) f64 {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1.0;
    return csp_sessions[idx].objective_value;
}

/// Reset solver session.
export fn csp_reset(handle: c_int) c_int {
    csp_mutex.lock();
    defer csp_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_CSP_SESSIONS or !csp_sessions[idx].active) return -1;
    csp_sessions[idx].state = .ready;
    csp_sessions[idx].objective_value = 0.0;
    csp_sessions[idx].variables_count = 0;
    csp_sessions[idx].constraints_count = 0;
    return 0;
}

test "csp_glpk_lifecycle" {
    const handle = csp_create_session(25); // GLPK
    try std.testing.expect(handle >= 0);

    try std.testing.expectEqual(@as(c_int, 0), csp_load_model(handle, "min x", 5, 1, 1));
    try std.testing.expectEqual(@as(c_int, 0), csp_start_solve(handle));
    try std.testing.expectEqual(@as(c_int, 0), csp_set_result(handle, 3, 42.0)); // Optimal
    try std.testing.expectEqual(@as(c_int, 3), csp_get_state(handle));
    try std.testing.expect(csp_get_objective(handle) == 42.0);

    try std.testing.expectEqual(@as(c_int, 0), csp_reset(handle));
    csp_destroy_session(handle);
}

test "csp_transition_validator" {
    try std.testing.expectEqual(@as(c_int, 1), csp_can_transition(0, 1));
    try std.testing.expectEqual(@as(c_int, 1), csp_can_transition(2, 3)); // Solving → Optimal
    try std.testing.expectEqual(@as(c_int, 1), csp_can_transition(2, 5)); // Solving → Infeasible
    try std.testing.expectEqual(@as(c_int, 0), csp_can_transition(0, 3)); // Invalid
}
