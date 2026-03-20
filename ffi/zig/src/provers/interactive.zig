// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: Interactive Proof Assistants
//
// C-ABI implementation for 10 interactive proof assistants:
//   Agda, Coq, Lean, Isabelle, Idris2, F*, HOL4, HOL Light, Nuprl, Minlog
//
// Enforces the session state machine proven in InteractiveAssistants.idr.
// Thread-safe via mutex-guarded session state per prover handle.

const std = @import("std");

// ═══════════════════════════════════════════════════════════════════════
// Types (match InteractiveAssistants.idr)
// ═══════════════════════════════════════════════════════════════════════

/// Session state machine (matches Idris2 SessionState).
pub const SessionState = enum(c_int) {
    idle = 0,
    goal_set = 1,
    tactic_applied = 2,
    proof_complete = 3,
    session_failed = 4,
};

/// Logic foundation for each prover.
pub const LogicFoundation = enum(c_int) {
    martin_loef = 0,
    calc_of_ind_constructions = 1,
    calc_of_constructions = 2,
    simple_type_theory = 3,
    effectful_dep_types = 4,
    constructive_type_theory = 5,
    minimal_logic = 6,
};

/// Tactic form for each prover.
pub const TacticForm = enum(c_int) {
    vernacular = 0,
    isar_script = 1,
    hol_tactic = 2,
    hole_filling = 3,
    elaboration = 4,
    effect_tactic = 5,
    extract_tactic = 6,
    realize_tactic = 7,
};

/// Prover kind (subset: interactive assistants only).
pub const InteractiveProver = enum(c_int) {
    agda = 0,
    coq = 1,
    lean = 2,
    isabelle = 3,
    idris2 = 12,
    fstar = 17,
    hol4 = 11,
    hol_light = 7,
    nuprl = 22,
    minlog = 23,
};

// ═══════════════════════════════════════════════════════════════════════
// Per-Handle Session State (mutex-guarded)
// ═══════════════════════════════════════════════════════════════════════

const MAX_SESSIONS = 64;

const Session = struct {
    state: SessionState,
    prover: InteractiveProver,
    goals_remaining: u32,
    tactics_applied: u32,
    active: bool,
};

var sessions: [MAX_SESSIONS]Session = [_]Session{.{
    .state = .idle,
    .prover = .agda,
    .goals_remaining = 0,
    .tactics_applied = 0,
    .active = false,
}} ** MAX_SESSIONS;

var session_mutex: std.Thread.Mutex = .{};

// ═══════════════════════════════════════════════════════════════════════
// Session Management (C ABI exports)
// ═══════════════════════════════════════════════════════════════════════

/// Create an interactive session for a given prover.
/// Returns session handle (0-63) or -1 on failure.
export fn interactive_create_session(prover_kind: c_int) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    for (&sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{
                .state = .idle,
                .prover = @enumFromInt(prover_kind),
                .goals_remaining = 0,
                .tactics_applied = 0,
                .active = true,
            };
            return @intCast(i);
        }
    }
    return -1; // No free session slots
}

/// Destroy an interactive session.
export fn interactive_destroy_session(handle: c_int) void {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx < MAX_SESSIONS) {
        sessions[idx].active = false;
        sessions[idx].state = .idle;
    }
}

/// Get the current session state.
export fn interactive_get_state(handle: c_int) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SESSIONS or !sessions[idx].active) return -1;
    return @intFromEnum(sessions[idx].state);
}

/// Check if a state transition is valid (mirrors Idris2 proof).
export fn interactive_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0, // Idle → GoalSet
        1 => if (to == 2 or to == 4) @as(c_int, 1) else 0, // GoalSet → TacticApplied | Failed
        2 => switch (to) {
            1, 3 => @as(c_int, 1), // TacticApplied → GoalSet | ProofComplete
            else => 0,
        },
        3 => if (to == 0) @as(c_int, 1) else 0, // ProofComplete → Idle
        4 => if (to == 0) @as(c_int, 1) else 0, // SessionFailed → Idle
        else => 0,
    };
}

/// Set a proof goal for the session.
export fn interactive_set_goal(
    handle: c_int,
    goal_ptr: [*]const u8,
    goal_len: c_int,
    num_goals: c_int,
) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SESSIONS or !sessions[idx].active) return -1;
    if (sessions[idx].state != .idle) return -2;

    _ = goal_ptr;
    _ = goal_len;

    sessions[idx].state = .goal_set;
    sessions[idx].goals_remaining = @intCast(num_goals);
    sessions[idx].tactics_applied = 0;
    return 0;
}

/// Apply a tactic to the current proof state.
export fn interactive_apply_tactic(
    handle: c_int,
    tactic_ptr: [*]const u8,
    tactic_len: c_int,
) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SESSIONS or !sessions[idx].active) return -1;
    if (sessions[idx].state != .goal_set) return -2;

    _ = tactic_ptr;
    _ = tactic_len;

    sessions[idx].state = .tactic_applied;
    sessions[idx].tactics_applied += 1;
    return 0;
}

/// Process the tactic result: advance to next state.
/// goals_remaining = 0 means proof is complete.
export fn interactive_process_result(
    handle: c_int,
    goals_remaining: c_int,
) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SESSIONS or !sessions[idx].active) return -1;
    if (sessions[idx].state != .tactic_applied) return -2;

    sessions[idx].goals_remaining = @intCast(goals_remaining);

    if (goals_remaining == 0) {
        sessions[idx].state = .proof_complete;
    } else {
        sessions[idx].state = .goal_set; // More goals to prove
    }
    return 0;
}

/// Reset the session to idle.
export fn interactive_reset(handle: c_int) c_int {
    session_mutex.lock();
    defer session_mutex.unlock();

    const idx: usize = @intCast(handle);
    if (idx >= MAX_SESSIONS or !sessions[idx].active) return -1;

    sessions[idx].state = .idle;
    sessions[idx].goals_remaining = 0;
    sessions[idx].tactics_applied = 0;
    return 0;
}

/// Get the logic foundation for a prover.
export fn interactive_logic_foundation(prover_kind: c_int) c_int {
    return switch (prover_kind) {
        0, 12 => @intFromEnum(LogicFoundation.martin_loef), // Agda, Idris2
        1 => @intFromEnum(LogicFoundation.calc_of_ind_constructions), // Coq
        2 => @intFromEnum(LogicFoundation.calc_of_constructions), // Lean
        3, 11, 7 => @intFromEnum(LogicFoundation.simple_type_theory), // Isabelle, HOL4, HOL Light
        17 => @intFromEnum(LogicFoundation.effectful_dep_types), // F*
        22 => @intFromEnum(LogicFoundation.constructive_type_theory), // Nuprl
        23 => @intFromEnum(LogicFoundation.minimal_logic), // Minlog
        else => -1,
    };
}

/// Get the tactic form for a prover.
export fn interactive_tactic_form(prover_kind: c_int) c_int {
    return switch (prover_kind) {
        0 => @intFromEnum(TacticForm.hole_filling), // Agda
        1 => @intFromEnum(TacticForm.vernacular), // Coq
        2 => @intFromEnum(TacticForm.vernacular), // Lean
        3 => @intFromEnum(TacticForm.isar_script), // Isabelle
        12 => @intFromEnum(TacticForm.elaboration), // Idris2
        17 => @intFromEnum(TacticForm.effect_tactic), // F*
        11 => @intFromEnum(TacticForm.hol_tactic), // HOL4
        7 => @intFromEnum(TacticForm.hol_tactic), // HOL Light
        22 => @intFromEnum(TacticForm.extract_tactic), // Nuprl
        23 => @intFromEnum(TacticForm.realize_tactic), // Minlog
        else => -1,
    };
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "interactive_session_lifecycle" {
    const handle = interactive_create_session(0); // Agda
    try std.testing.expect(handle >= 0);
    try std.testing.expectEqual(@as(c_int, 0), interactive_get_state(handle));

    // Set goal
    try std.testing.expectEqual(@as(c_int, 0), interactive_set_goal(handle, "goal", 4, 1));
    try std.testing.expectEqual(@as(c_int, 1), interactive_get_state(handle));

    // Apply tactic
    try std.testing.expectEqual(@as(c_int, 0), interactive_apply_tactic(handle, "refl", 4));
    try std.testing.expectEqual(@as(c_int, 2), interactive_get_state(handle));

    // Process result (0 goals = QED)
    try std.testing.expectEqual(@as(c_int, 0), interactive_process_result(handle, 0));
    try std.testing.expectEqual(@as(c_int, 3), interactive_get_state(handle));

    // Reset
    try std.testing.expectEqual(@as(c_int, 0), interactive_reset(handle));
    try std.testing.expectEqual(@as(c_int, 0), interactive_get_state(handle));

    interactive_destroy_session(handle);
}

test "interactive_transition_validator" {
    try std.testing.expectEqual(@as(c_int, 1), interactive_can_transition(0, 1));
    try std.testing.expectEqual(@as(c_int, 1), interactive_can_transition(1, 2));
    try std.testing.expectEqual(@as(c_int, 1), interactive_can_transition(2, 1));
    try std.testing.expectEqual(@as(c_int, 1), interactive_can_transition(2, 3));
    try std.testing.expectEqual(@as(c_int, 0), interactive_can_transition(0, 3)); // Invalid
}

test "interactive_logic_foundations" {
    try std.testing.expectEqual(@as(c_int, 0), interactive_logic_foundation(0)); // Agda = MLTT
    try std.testing.expectEqual(@as(c_int, 1), interactive_logic_foundation(1)); // Coq = CIC
    try std.testing.expectEqual(@as(c_int, 3), interactive_logic_foundation(3)); // Isabelle = HOL
}
