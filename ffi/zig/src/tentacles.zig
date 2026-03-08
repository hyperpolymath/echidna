// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Tentacles FFI — 7-Tentacles Compiler Agent Interface
//
// C-ABI exports for managing the 7 colour-coded compiler agents, dispatching
// tasks, tracking OODA phases, managing progressive reveal stages, and
// streaming events to external consumers (PanLL, CLI, etc.).
//
// Architecture:
//   Idris2 ABI (TentaclesForeign.idr) --> Zig FFI (tentacles.zig) --> C-ABI --> V-lang adapter
//
// Each agent maintains:
//   - Status (idle/busy/error/disabled)
//   - Current OODA phase (observe/orient/decide/act)
//   - Current stage (cuttle/squidlet/duet/octopus)
//   - Task description and error state

const std = @import("std");

// ============================================================================
// Constants
// ============================================================================

const TENTACLES_VERSION = "1.0.0";
const AGENT_COUNT: usize = 7;
const MAX_TASK_LEN: usize = 4096;
const MAX_EVENT_BUF: usize = 65536;
const ERROR_BUF_SIZE: usize = 512;

// ============================================================================
// Enums
// ============================================================================

/// Tentacle agent colour identifier.
pub const TentacleId = enum(c_int) {
    red = 0,
    orange = 1,
    yellow = 2,
    green = 3,
    blue = 4,
    indigo = 5,
    violet = 6,

    pub fn fromInt(v: c_int) ?TentacleId {
        return switch (v) {
            0 => .red,
            1 => .orange,
            2 => .yellow,
            3 => .green,
            4 => .blue,
            5 => .indigo,
            6 => .violet,
            else => null,
        };
    }

    pub fn name(self: TentacleId) [*:0]const u8 {
        return switch (self) {
            .red => "Red (Parser)",
            .orange => "Orange (Concurrency)",
            .yellow => "Yellow (Type System)",
            .green => "Green (AST Architect)",
            .blue => "Blue (Auditor)",
            .indigo => "Indigo (Metaprogrammer)",
            .violet => "Violet (Governance)",
        };
    }
};

/// OODA loop phase.
pub const OodaPhase = enum(c_int) {
    observe = 0,
    orient = 1,
    decide = 2,
    act = 3,

    pub fn fromInt(v: c_int) ?OodaPhase {
        return switch (v) {
            0 => .observe,
            1 => .orient,
            2 => .decide,
            3 => .act,
            else => null,
        };
    }

    pub fn name(self: OodaPhase) [*:0]const u8 {
        return switch (self) {
            .observe => "Observe",
            .orient => "Orient",
            .decide => "Decide",
            .act => "Act",
        };
    }
};

/// Progressive reveal stage.
pub const TentacleStage = enum(c_int) {
    cuttle = 0,
    squidlet = 1,
    duet = 2,
    octopus = 3,

    pub fn fromInt(v: c_int) ?TentacleStage {
        return switch (v) {
            0 => .cuttle,
            1 => .squidlet,
            2 => .duet,
            3 => .octopus,
            else => null,
        };
    }

    pub fn name(self: TentacleStage) [*:0]const u8 {
        return switch (self) {
            .cuttle => "Cuttle (8-12)",
            .squidlet => "Squidlet (13-14)",
            .duet => "Duet (15)",
            .octopus => "Octopus (16+)",
        };
    }
};

/// Agent runtime status.
pub const AgentStatus = enum(c_int) {
    idle = 0,
    busy = 1,
    agent_error = 2,
    disabled = 3,

    pub fn fromInt(v: c_int) ?AgentStatus {
        return switch (v) {
            0 => .idle,
            1 => .busy,
            2 => .agent_error,
            3 => .disabled,
            else => null,
        };
    }
};

// ============================================================================
// Error codes (-300 to -399)
// ============================================================================

const ERR_NOT_INIT: c_int = -300;
const ERR_INVALID_AGENT: c_int = -301;
const ERR_AGENT_BUSY: c_int = -302;
const ERR_AGENT_ERROR: c_int = -303;
const ERR_TASK_FAILED: c_int = -304;
const ERR_INVALID_STAGE: c_int = -305;
const ERR_BUFFER_TOO_SMALL: c_int = -306;
const ERR_BROADCAST_FAILED: c_int = -307;

// ============================================================================
// Agent state
// ============================================================================

const AgentState = struct {
    status: AgentStatus = .idle,
    phase: OodaPhase = .observe,
    stage: TentacleStage = .cuttle,
    task_buf: [MAX_TASK_LEN]u8 = [_]u8{0} ** MAX_TASK_LEN,
    task_len: usize = 0,
    error_buf: [ERROR_BUF_SIZE]u8 = [_]u8{0} ** ERROR_BUF_SIZE,
    error_len: usize = 0,
};

// ============================================================================
// Global state
// ============================================================================

var g_initialised: bool = false;
var g_agents: [AGENT_COUNT]AgentState = [_]AgentState{.{}} ** AGENT_COUNT;
var g_global_stage: TentacleStage = .cuttle;
var g_last_error: [ERROR_BUF_SIZE]u8 = [_]u8{0} ** ERROR_BUF_SIZE;
var g_last_error_len: usize = 0;

// Callback slots
pub const OnPhaseChangeFn = *const fn (agent_id: c_int, old_phase: c_int, new_phase: c_int) callconv(.c) void;
pub const OnTaskCompleteFn = *const fn (agent_id: c_int, result_code: c_int) callconv(.c) void;
pub const OnTentaclesErrorFn = *const fn (agent_id: c_int, error_code: c_int, msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void;

var g_on_phase_change: ?OnPhaseChangeFn = null;
var g_on_task_complete: ?OnTaskCompleteFn = null;
var g_on_error: ?OnTentaclesErrorFn = null;

fn setLastError(msg: []const u8) void {
    const len = @min(msg.len, ERROR_BUF_SIZE);
    @memcpy(g_last_error[0..len], msg[0..len]);
    g_last_error_len = len;
}

fn validAgent(agent_id: c_int) ?usize {
    if (agent_id < 0 or agent_id >= AGENT_COUNT) return null;
    return @intCast(agent_id);
}

// ============================================================================
// Initialisation
// ============================================================================

export fn echidna_tentacles_init() callconv(.c) c_int {
    for (&g_agents) |*a| {
        a.* = .{};
    }
    g_global_stage = .cuttle;
    g_last_error_len = 0;
    g_initialised = true;
    return 0;
}

export fn echidna_tentacles_shutdown() callconv(.c) void {
    g_initialised = false;
    g_on_phase_change = null;
    g_on_task_complete = null;
    g_on_error = null;
}

// ============================================================================
// Agent queries
// ============================================================================

export fn echidna_tentacles_agent_status(agent_id: c_int) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const idx = validAgent(agent_id) orelse return ERR_INVALID_AGENT;
    return @intFromEnum(g_agents[idx].status);
}

export fn echidna_tentacles_agent_phase(agent_id: c_int) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const idx = validAgent(agent_id) orelse return ERR_INVALID_AGENT;
    return @intFromEnum(g_agents[idx].phase);
}

export fn echidna_tentacles_agent_stage(agent_id: c_int) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const idx = validAgent(agent_id) orelse return ERR_INVALID_AGENT;
    return @intFromEnum(g_agents[idx].stage);
}

// ============================================================================
// Task dispatch
// ============================================================================

export fn echidna_tentacles_dispatch_task(agent_id: c_int, task_ptr: [*]const u8, task_len: usize) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const idx = validAgent(agent_id) orelse return ERR_INVALID_AGENT;
    var agent = &g_agents[idx];

    if (agent.status == .busy) return ERR_AGENT_BUSY;
    if (agent.status == .agent_error) return ERR_AGENT_ERROR;

    const len = @min(task_len, MAX_TASK_LEN);
    @memcpy(agent.task_buf[0..len], task_ptr[0..len]);
    agent.task_len = len;
    agent.status = .busy;
    agent.phase = .observe;
    agent.error_len = 0;

    return 0;
}

export fn echidna_tentacles_cancel_task(agent_id: c_int) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const idx = validAgent(agent_id) orelse return ERR_INVALID_AGENT;
    var agent = &g_agents[idx];

    agent.status = .idle;
    agent.task_len = 0;

    if (g_on_task_complete) |cb| {
        cb(agent_id, -1); // -1 = cancelled
    }

    return 0;
}

// ============================================================================
// Stage management
// ============================================================================

export fn echidna_tentacles_set_global_stage(stage_id: c_int) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    const stage = TentacleStage.fromInt(stage_id) orelse return ERR_INVALID_STAGE;
    g_global_stage = stage;

    for (&g_agents) |*a| {
        a.stage = stage;
    }

    return 0;
}

export fn echidna_tentacles_get_global_stage() callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;
    return @intFromEnum(g_global_stage);
}

// ============================================================================
// Event polling (JSON)
// ============================================================================

export fn echidna_tentacles_poll_events(out_ptr: [*]u8, out_len: *usize) callconv(.c) c_int {
    if (!g_initialised) return ERR_NOT_INIT;

    // Build JSON array of agent states
    var buf: [MAX_EVENT_BUF]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buf);
    var writer = stream.writer();

    writer.writeAll("[") catch return ERR_BUFFER_TOO_SMALL;

    for (0..AGENT_COUNT) |i| {
        if (i > 0) writer.writeAll(",") catch return ERR_BUFFER_TOO_SMALL;

        const a = &g_agents[i];
        const id_enum: TentacleId = @enumFromInt(@as(c_int, @intCast(i)));

        writer.print(
            \\{{"id":{d},"name":"{s}","status":{d},"phase":{d},"stage":{d},"busy":{s},"hasTask":{s},"hasError":{s}}}
        , .{
            i,
            id_enum.name(),
            @intFromEnum(a.status),
            @intFromEnum(a.phase),
            @intFromEnum(a.stage),
            if (a.status == .busy) "true" else "false",
            if (a.task_len > 0) "true" else "false",
            if (a.error_len > 0) "true" else "false",
        }) catch return ERR_BUFFER_TOO_SMALL;
    }

    writer.writeAll("]") catch return ERR_BUFFER_TOO_SMALL;

    const written = stream.pos;
    if (written > out_len.*) return ERR_BUFFER_TOO_SMALL;

    @memcpy(out_ptr[0..written], buf[0..written]);
    out_len.* = written;
    return 0;
}

export fn echidna_tentacles_event_count() callconv(.c) c_int {
    if (!g_initialised) return 0;
    var count: c_int = 0;
    for (&g_agents) |*a| {
        if (a.status == .busy) count += 1;
    }
    return count;
}

// ============================================================================
// Broadcast
// ============================================================================

export fn echidna_tentacles_broadcast(source_id: c_int, payload_ptr: [*]const u8, payload_len: usize) callconv(.c) c_int {
    _ = payload_ptr;
    _ = payload_len;
    if (!g_initialised) return ERR_NOT_INIT;
    if (validAgent(source_id) == null) return ERR_INVALID_AGENT;
    // Broadcast delivery is handled by the consumer (PanLL TEA loop or V-lang adapter).
    // This FFI call records the intent; actual routing is external.
    return 0;
}

// ============================================================================
// Callback registration
// ============================================================================

export fn echidna_tentacles_register_on_phase_change(cb: ?OnPhaseChangeFn) callconv(.c) c_int {
    g_on_phase_change = cb;
    return 0;
}

export fn echidna_tentacles_register_on_task_complete(cb: ?OnTaskCompleteFn) callconv(.c) c_int {
    g_on_task_complete = cb;
    return 0;
}

export fn echidna_tentacles_register_on_error(cb: ?OnTentaclesErrorFn) callconv(.c) c_int {
    g_on_error = cb;
    return 0;
}

export fn echidna_tentacles_unregister_all_callbacks() callconv(.c) c_int {
    g_on_phase_change = null;
    g_on_task_complete = null;
    g_on_error = null;
    return 0;
}

export fn echidna_tentacles_callback_count() callconv(.c) c_int {
    var count: c_int = 0;
    if (g_on_phase_change != null) count += 1;
    if (g_on_task_complete != null) count += 1;
    if (g_on_error != null) count += 1;
    return count;
}

// ============================================================================
// Unified
// ============================================================================

export fn echidna_tentacles_version() callconv(.c) [*:0]const u8 {
    return TENTACLES_VERSION;
}

export fn echidna_tentacles_last_error() callconv(.c) ?[*]const u8 {
    if (g_last_error_len == 0) return null;
    return &g_last_error;
}

export fn echidna_tentacles_agent_count() callconv(.c) c_int {
    return AGENT_COUNT;
}
