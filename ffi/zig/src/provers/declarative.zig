// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: Declarative Provers
//
// C-ABI implementation for 7 declarative provers:
//   Metamath, Mizar, PVS, ACL2, TLAPS, Twelf, Imandra
// Enforces the verification state machine proven in DeclarativeProvers.idr.

const std = @import("std");

/// Verification state (matches DeclarativeProvers.idr VerifyState).
pub const VerifyState = enum(c_int) {
    ready = 0,
    file_submitted = 1,
    verifying = 2,
    valid = 3,
    invalid = 4,
    err = 5,
};

/// Kernel size classification.
pub const KernelSize = enum(c_int) {
    tiny = 0,
    small = 1,
    medium = 2,
    large = 3,
    external = 4,
};

const MAX_VERIFY_SESSIONS = 16;

const VerifySession = struct {
    state: VerifyState,
    solver_kind: c_int,
    diagnostics_count: u32,
    active: bool,
};

var verify_sessions: [MAX_VERIFY_SESSIONS]VerifySession = [_]VerifySession{.{
    .state = .ready,
    .solver_kind = 0,
    .diagnostics_count = 0,
    .active = false,
}} ** MAX_VERIFY_SESSIONS;

var verify_mutex: std.Thread.Mutex = .{};

/// Create a declarative verification session.
export fn verify_create_session(solver_kind: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();

    for (&verify_sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{ .state = .ready, .solver_kind = solver_kind, .diagnostics_count = 0, .active = true };
            return @intCast(i);
        }
    }
    return -1;
}

/// Destroy a verification session.
export fn verify_destroy_session(handle: c_int) void {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx < MAX_VERIFY_SESSIONS) verify_sessions[idx].active = false;
}

/// Get current verification state.
export fn verify_get_state(handle: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_VERIFY_SESSIONS or !verify_sessions[idx].active) return -1;
    return @intFromEnum(verify_sessions[idx].state);
}

/// Check if a verification transition is valid.
export fn verify_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0,
        1 => if (to == 2) @as(c_int, 1) else 0,
        2 => if (to >= 3 and to <= 5) @as(c_int, 1) else 0,
        3, 4, 5 => if (to == 0) @as(c_int, 1) else 0,
        else => 0,
    };
}

/// Submit a proof file for verification.
export fn verify_submit_file(handle: c_int, file_ptr: [*]const u8, file_len: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_VERIFY_SESSIONS or !verify_sessions[idx].active) return -1;
    if (verify_sessions[idx].state != .ready) return -2;
    _ = file_ptr;
    _ = file_len;
    verify_sessions[idx].state = .file_submitted;
    return 0;
}

/// Start verification.
export fn verify_start(handle: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_VERIFY_SESSIONS or !verify_sessions[idx].active) return -1;
    if (verify_sessions[idx].state != .file_submitted) return -2;
    verify_sessions[idx].state = .verifying;
    return 0;
}

/// Set the verification result.
export fn verify_set_result(handle: c_int, is_valid: c_int, diagnostics: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_VERIFY_SESSIONS or !verify_sessions[idx].active) return -1;
    if (verify_sessions[idx].state != .verifying) return -2;
    verify_sessions[idx].diagnostics_count = @intCast(diagnostics);
    verify_sessions[idx].state = if (is_valid == 1) .valid else .invalid;
    return 0;
}

/// Reset verification session.
export fn verify_reset(handle: c_int) c_int {
    verify_mutex.lock();
    defer verify_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_VERIFY_SESSIONS or !verify_sessions[idx].active) return -1;
    verify_sessions[idx].state = .ready;
    verify_sessions[idx].diagnostics_count = 0;
    return 0;
}

/// Get kernel size for a declarative prover.
export fn verify_kernel_size(solver_kind: c_int) c_int {
    return switch (solver_kind) {
        6 => @intFromEnum(KernelSize.tiny),      // Metamath
        8 => @intFromEnum(KernelSize.medium),     // Mizar
        9 => @intFromEnum(KernelSize.large),      // PVS
        10 => @intFromEnum(KernelSize.large),     // ACL2
        19 => @intFromEnum(KernelSize.external),  // TLAPS
        20 => @intFromEnum(KernelSize.small),     // Twelf
        24 => @intFromEnum(KernelSize.medium),    // Imandra
        else => -1,
    };
}

test "verify_session_lifecycle" {
    const handle = verify_create_session(6); // Metamath
    try std.testing.expect(handle >= 0);
    try std.testing.expectEqual(@as(c_int, 0), verify_submit_file(handle, "proof.mm", 8));
    try std.testing.expectEqual(@as(c_int, 0), verify_start(handle));
    try std.testing.expectEqual(@as(c_int, 0), verify_set_result(handle, 1, 0));
    try std.testing.expectEqual(@as(c_int, 3), verify_get_state(handle));
    try std.testing.expectEqual(@as(c_int, 0), verify_reset(handle));
    verify_destroy_session(handle);
}
