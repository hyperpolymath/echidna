// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-Prover Zig FFI: Auto-Active Verifiers
//
// C-ABI implementation for 2 auto-active verifiers: Dafny, Why3.
// Enforces the pipeline state machine proven in AutoActive.idr.

const std = @import("std");

/// Pipeline stage (matches AutoActive.idr PipelineStage).
pub const PipelineStage = enum(c_int) {
    source_parsed = 0,
    vcs_generated = 1,
    vcs_discharging = 2,
    all_verified = 3,
    some_failed = 4,
    pipeline_error = 5,
};

/// VC outcome.
pub const VCOutcome = enum(c_int) {
    verified = 0,
    unverified = 1,
    vc_timeout = 2,
    skipped = 3,
};

const MAX_PIPELINE_SESSIONS = 16;

const PipelineSession = struct {
    stage: PipelineStage,
    solver_kind: c_int, // 18=Dafny, 19=Why3 (but 19 is TLAPS in Types.idr, need to check)
    total_vcs: u32,
    verified_vcs: u32,
    failed_vcs: u32,
    active: bool,
};

var pipeline_sessions: [MAX_PIPELINE_SESSIONS]PipelineSession = [_]PipelineSession{.{
    .stage = .source_parsed,
    .solver_kind = 0,
    .total_vcs = 0,
    .verified_vcs = 0,
    .failed_vcs = 0,
    .active = false,
}} ** MAX_PIPELINE_SESSIONS;

var pipeline_mutex: std.Thread.Mutex = .{};

/// Create an auto-active verification session.
export fn pipeline_create_session(solver_kind: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();

    for (&pipeline_sessions, 0..) |*s, i| {
        if (!s.active) {
            s.* = .{
                .stage = .source_parsed,
                .solver_kind = solver_kind,
                .total_vcs = 0,
                .verified_vcs = 0,
                .failed_vcs = 0,
                .active = true,
            };
            return @intCast(i);
        }
    }
    return -1;
}

/// Destroy a pipeline session.
export fn pipeline_destroy_session(handle: c_int) void {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx < MAX_PIPELINE_SESSIONS) pipeline_sessions[idx].active = false;
}

/// Get current pipeline stage.
export fn pipeline_get_stage(handle: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    return @intFromEnum(pipeline_sessions[idx].stage);
}

/// Check if a pipeline transition is valid.
export fn pipeline_can_transition(from: c_int, to: c_int) c_int {
    return switch (from) {
        0 => if (to == 1) @as(c_int, 1) else 0,
        1 => if (to == 2) @as(c_int, 1) else 0,
        2 => if (to >= 3 and to <= 5) @as(c_int, 1) else 0,
        3, 4, 5 => if (to == 0) @as(c_int, 1) else 0,
        else => 0,
    };
}

/// Set the number of generated VCs.
export fn pipeline_set_vcs(handle: c_int, total_vcs: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    if (pipeline_sessions[idx].stage != .source_parsed) return -2;
    pipeline_sessions[idx].total_vcs = @intCast(total_vcs);
    pipeline_sessions[idx].stage = .vcs_generated;
    return 0;
}

/// Start discharging VCs.
export fn pipeline_start_discharge(handle: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    if (pipeline_sessions[idx].stage != .vcs_generated) return -2;
    pipeline_sessions[idx].stage = .vcs_discharging;
    return 0;
}

/// Report a VC outcome.
export fn pipeline_report_vc(handle: c_int, outcome: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    if (pipeline_sessions[idx].stage != .vcs_discharging) return -2;

    if (outcome == 0) {
        pipeline_sessions[idx].verified_vcs += 1;
    } else {
        pipeline_sessions[idx].failed_vcs += 1;
    }
    return 0;
}

/// Finalise the pipeline (all VCs reported).
export fn pipeline_finalise(handle: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    if (pipeline_sessions[idx].stage != .vcs_discharging) return -2;

    if (pipeline_sessions[idx].failed_vcs == 0) {
        pipeline_sessions[idx].stage = .all_verified;
    } else {
        pipeline_sessions[idx].stage = .some_failed;
    }
    return 0;
}

/// Reset pipeline session.
export fn pipeline_reset(handle: c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    pipeline_sessions[idx].stage = .source_parsed;
    pipeline_sessions[idx].total_vcs = 0;
    pipeline_sessions[idx].verified_vcs = 0;
    pipeline_sessions[idx].failed_vcs = 0;
    return 0;
}

/// Get VC statistics.
export fn pipeline_get_vc_stats(handle: c_int, out_total: *c_int, out_verified: *c_int, out_failed: *c_int) c_int {
    pipeline_mutex.lock();
    defer pipeline_mutex.unlock();
    const idx: usize = @intCast(handle);
    if (idx >= MAX_PIPELINE_SESSIONS or !pipeline_sessions[idx].active) return -1;
    out_total.* = @intCast(pipeline_sessions[idx].total_vcs);
    out_verified.* = @intCast(pipeline_sessions[idx].verified_vcs);
    out_failed.* = @intCast(pipeline_sessions[idx].failed_vcs);
    return 0;
}

test "pipeline_dafny_lifecycle" {
    const handle = pipeline_create_session(18); // Dafny
    try std.testing.expect(handle >= 0);

    try std.testing.expectEqual(@as(c_int, 0), pipeline_set_vcs(handle, 5));
    try std.testing.expectEqual(@as(c_int, 0), pipeline_start_discharge(handle));

    // All 5 VCs verified
    var i: u32 = 0;
    while (i < 5) : (i += 1) {
        try std.testing.expectEqual(@as(c_int, 0), pipeline_report_vc(handle, 0));
    }

    try std.testing.expectEqual(@as(c_int, 0), pipeline_finalise(handle));
    try std.testing.expectEqual(@as(c_int, 3), pipeline_get_stage(handle)); // AllVerified

    try std.testing.expectEqual(@as(c_int, 0), pipeline_reset(handle));
    pipeline_destroy_session(handle);
}
