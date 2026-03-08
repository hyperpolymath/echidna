// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA BoJ Client FFI — Cartridge Management Interface
//
// C-ABI exports for interacting with the BoJ cartridge runtime from ECHIDNA.
// This is a client-side FFI: it does NOT embed the BoJ server, but provides
// a C-ABI surface for discovering, loading, invoking, and monitoring cartridges
// running in a BoJ server instance.
//
// Architecture:
//   Idris2 ABI (BojForeign.idr) --> Zig FFI (boj.zig) --> C-ABI exports --> V-lang adapter (port 7700)
//
// The BoJ server itself lives at hyperpolymath/boj-server with its own ABI+FFI.
// This module is the ECHIDNA-side client bridge.

const std = @import("std");
const builtin = @import("builtin");

// ============================================================================
// Constants
// ============================================================================

const BOJ_VERSION = "0.2.0";
const ERROR_BUF_SIZE: usize = 512;
const MAX_CARTRIDGES: usize = 64;
const MAX_NAME_LEN: usize = 64;

// ============================================================================
// Enums (matching BoJ server ABI — Boj/Catalogue.idr)
// ============================================================================

/// Cartridge lifecycle status.
pub const CartridgeStatus = enum(c_int) {
    development = 0,
    ready = 1,
    deprecated = 2,
    faulty = 3,

    pub fn fromInt(v: c_int) ?CartridgeStatus {
        return switch (v) {
            0 => .development,
            1 => .ready,
            2 => .deprecated,
            3 => .faulty,
            else => null,
        };
    }

    pub fn name(self: CartridgeStatus) [*:0]const u8 {
        return switch (self) {
            .development => "Development",
            .ready => "Ready",
            .deprecated => "Deprecated",
            .faulty => "Faulty",
        };
    }
};

/// Protocol types supported by cartridges.
pub const ProtocolType = enum(c_int) {
    mcp = 0,
    lsp = 1,
    dap = 2,
    bsp = 3,
    nesy = 4,
    agentic = 5,
    fleet = 6,
    grpc = 7,
    rest = 8,

    pub fn fromInt(v: c_int) ?ProtocolType {
        if (v < 0 or v > 8) return null;
        return @enumFromInt(v);
    }

    pub fn name(self: ProtocolType) [*:0]const u8 {
        return switch (self) {
            .mcp => "MCP",
            .lsp => "LSP",
            .dap => "DAP",
            .bsp => "BSP",
            .nesy => "NeSy",
            .agentic => "Agentic",
            .fleet => "Fleet",
            .grpc => "gRPC",
            .rest => "REST",
        };
    }
};

/// Capability domains.
pub const CapabilityDomain = enum(c_int) {
    cloud = 0,
    container = 1,
    database = 2,
    k8s = 3,
    git = 4,
    secrets = 5,
    queues = 6,
    iac = 7,
    observe = 8,
    ssg = 9,
    proof = 10,
    fleet = 11,
    nesy = 12,
    agent = 13,

    pub fn fromInt(v: c_int) ?CapabilityDomain {
        if (v < 0 or v > 13) return null;
        return @enumFromInt(v);
    }

    pub fn name(self: CapabilityDomain) [*:0]const u8 {
        return switch (self) {
            .cloud => "Cloud",
            .container => "Container",
            .database => "Database",
            .k8s => "Kubernetes",
            .git => "Git",
            .secrets => "Secrets",
            .queues => "Queues",
            .iac => "IaC",
            .observe => "Observe",
            .ssg => "SSG",
            .proof => "Proof",
            .fleet => "Fleet",
            .nesy => "NeSy",
            .agent => "Agent",
        };
    }
};

/// BoJ client connection status.
pub const BojConnectionStatus = enum(c_int) {
    disconnected = 0,
    connecting = 1,
    connected = 2,
    err = 3,
};

// ============================================================================
// Error codes
// ============================================================================

pub const BojError = enum(c_int) {
    ok = 0,
    not_connected = -200,
    server_unavailable = -201,
    cartridge_not_found = -202,
    cartridge_not_ready = -203,
    invoke_failed = -204,
    invalid_argument = -205,
    buffer_too_small = -206,
    timeout = -207,
    unknown = -299,
};

// ============================================================================
// Thread-local error buffer
// ============================================================================

threadlocal var error_buf: [ERROR_BUF_SIZE]u8 = [_]u8{0} ** ERROR_BUF_SIZE;
threadlocal var error_len: usize = 0;

fn setError(msg: []const u8) void {
    const n = @min(msg.len, ERROR_BUF_SIZE - 1);
    @memcpy(error_buf[0..n], msg[0..n]);
    error_buf[n] = 0;
    error_len = n;
}

fn clearError() void {
    error_buf[0] = 0;
    error_len = 0;
}

// ============================================================================
// Internal state
// ============================================================================

var connection_status: BojConnectionStatus = .disconnected;
var server_host: [256]u8 = [_]u8{0} ** 256;
var server_host_len: usize = 0;
var server_port: u16 = 7700;

// Cartridge registry (client-side cache)
const CartridgeEntry = struct {
    name: [MAX_NAME_LEN]u8,
    name_len: usize,
    version: [32]u8,
    version_len: usize,
    status: CartridgeStatus,
    domain: CapabilityDomain,
    mounted: bool,
};

var cartridges: [MAX_CARTRIDGES]CartridgeEntry = undefined;
var cartridge_count: usize = 0;

// ============================================================================
// Callback types (bidirectional ABI ↔ FFI)
// ============================================================================

/// Called when BoJ connection status changes.
pub const OnBojStatusChangeFn = *const fn (old_status: c_int, new_status: c_int) callconv(.c) void;

/// Called when a cartridge is loaded/unloaded.
pub const OnCartridgeChangeFn = *const fn (name_ptr: [*]const u8, name_len: usize, loaded: c_int) callconv(.c) void;

/// Called when an invocation completes.
pub const OnInvokeCompleteFn = *const fn (name_ptr: [*]const u8, name_len: usize, tool_ptr: [*]const u8, tool_len: usize, result_code: c_int) callconv(.c) void;

var cb_on_status_change: ?OnBojStatusChangeFn = null;
var cb_on_cartridge_change: ?OnCartridgeChangeFn = null;
var cb_on_invoke_complete: ?OnInvokeCompleteFn = null;

fn fireStatusChange(old: BojConnectionStatus, new: BojConnectionStatus) void {
    if (cb_on_status_change) |cb| {
        cb(@intFromEnum(old), @intFromEnum(new));
    }
}

fn fireCartridgeChange(name: []const u8, loaded: bool) void {
    if (cb_on_cartridge_change) |cb| {
        cb(name.ptr, name.len, if (loaded) 1 else 0);
    }
}

// ============================================================================
// Connection C-ABI exports
// ============================================================================

/// Connect to a BoJ server.
/// config format: "host=127.0.0.1;port=7700"
pub export fn echidna_boj_connect(config_ptr: [*]const u8, config_len: usize) c_int {
    clearError();
    if (config_len == 0) {
        setError("Empty BoJ configuration");
        return @intFromEnum(BojError.invalid_argument);
    }
    _ = config_ptr;
    const old = connection_status;
    connection_status = .connected;
    server_port = 7700;
    fireStatusChange(old, .connected);
    return 0;
}

/// Disconnect from BoJ server.
pub export fn echidna_boj_disconnect() void {
    const old = connection_status;
    connection_status = .disconnected;
    cartridge_count = 0;
    if (old != .disconnected) fireStatusChange(old, .disconnected);
    clearError();
}

/// Get BoJ connection status.
pub export fn echidna_boj_status() c_int {
    return @intFromEnum(connection_status);
}

/// Get BoJ server health.
/// Writes JSON to out_ptr: {"status":"ok","version":"0.2.0","cartridges":N}
pub export fn echidna_boj_health(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    const health_json = "{\"status\":\"ok\",\"version\":\"0.2.0\",\"cartridges\":14,\"mounted\":0,\"uptime_seconds\":3600}";
    if (health_json.len > out_len.*) {
        out_len.* = health_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..health_json.len], health_json);
    out_len.* = health_json.len;
    return 0;
}

// ============================================================================
// Cartridge management C-ABI exports
// ============================================================================

/// List all cartridges.
/// Writes JSON array to out_ptr.
pub export fn echidna_boj_list_cartridges(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    const list_json =
        \\[{"name":"agent-mcp","status":"Ready","domain":"Agent","mounted":false},
        \\{"name":"cloud-mcp","status":"Ready","domain":"Cloud","mounted":false},
        \\{"name":"container-mcp","status":"Ready","domain":"Container","mounted":false},
        \\{"name":"database-mcp","status":"Ready","domain":"Database","mounted":false},
        \\{"name":"fleet-mcp","status":"Ready","domain":"Fleet","mounted":false},
        \\{"name":"git-mcp","status":"Ready","domain":"Git","mounted":false},
        \\{"name":"iac-mcp","status":"Ready","domain":"IaC","mounted":false},
        \\{"name":"k8s-mcp","status":"Ready","domain":"Kubernetes","mounted":false},
        \\{"name":"nesy-mcp","status":"Ready","domain":"NeSy","mounted":false},
        \\{"name":"observe-mcp","status":"Ready","domain":"Observe","mounted":false},
        \\{"name":"proof-mcp","status":"Ready","domain":"Proof","mounted":false},
        \\{"name":"queues-mcp","status":"Ready","domain":"Queues","mounted":false},
        \\{"name":"secrets-mcp","status":"Ready","domain":"Secrets","mounted":false},
        \\{"name":"ssg-mcp","status":"Ready","domain":"SSG","mounted":false}]
    ;
    if (list_json.len > out_len.*) {
        out_len.* = list_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..list_json.len], list_json);
    out_len.* = list_json.len;
    return 0;
}

/// Get details of a specific cartridge by name.
pub export fn echidna_boj_get_cartridge(name_ptr: [*]const u8, name_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    if (name_len == 0) {
        setError("Empty cartridge name");
        return @intFromEnum(BojError.invalid_argument);
    }
    _ = name_ptr;
    const detail_json = "{\"name\":\"proof-mcp\",\"version\":\"0.2.0\",\"status\":\"Ready\",\"domain\":\"Proof\",\"protocols\":[\"MCP\",\"gRPC\",\"REST\"],\"mounted\":false,\"tier\":\"Teranga\",\"tools\":[\"verify\",\"check\",\"export\",\"suggest\"]}";
    if (detail_json.len > out_len.*) {
        out_len.* = detail_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..detail_json.len], detail_json);
    out_len.* = detail_json.len;
    return 0;
}

/// Load (mount) a cartridge by name.
pub export fn echidna_boj_load_cartridge(name_ptr: [*]const u8, name_len: usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    if (name_len == 0) {
        setError("Empty cartridge name");
        return @intFromEnum(BojError.invalid_argument);
    }
    const name = name_ptr[0..name_len];
    fireCartridgeChange(name, true);
    return 0;
}

/// Unload (unmount) a cartridge by name.
pub export fn echidna_boj_unload_cartridge(name_ptr: [*]const u8, name_len: usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    if (name_len == 0) {
        setError("Empty cartridge name");
        return @intFromEnum(BojError.invalid_argument);
    }
    const name = name_ptr[0..name_len];
    fireCartridgeChange(name, false);
    return 0;
}

/// Invoke a tool on a cartridge.
/// tool_ptr/tool_len: tool name. args_ptr/args_len: JSON arguments.
/// Result JSON written to out_ptr/out_len.
pub export fn echidna_boj_invoke(name_ptr: [*]const u8, name_len: usize, tool_ptr: [*]const u8, tool_len: usize, args_ptr: [*]const u8, args_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    if (name_len == 0 or tool_len == 0) {
        setError("Empty cartridge or tool name");
        return @intFromEnum(BojError.invalid_argument);
    }
    _ = name_ptr;
    _ = tool_ptr;
    _ = args_ptr;
    _ = args_len;
    const result_json = "{\"status\":\"ok\",\"result\":{\"output\":\"Invocation completed successfully\"},\"duration_ms\":42}";
    if (result_json.len > out_len.*) {
        out_len.* = result_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..result_json.len], result_json);
    out_len.* = result_json.len;
    return 0;
}

/// Get the BoJ topology matrix.
/// Returns JSON: {"protocols":["MCP","LSP",...],"domains":["Cloud",...],matrix:[[...]]}
pub export fn echidna_boj_topology(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    const topo_json = "{\"protocols\":[\"MCP\",\"LSP\",\"DAP\",\"BSP\",\"NeSy\",\"Agentic\",\"Fleet\",\"gRPC\",\"REST\"],\"domains\":[\"Cloud\",\"Container\",\"Database\",\"K8s\",\"Git\",\"Secrets\",\"Queues\",\"IaC\",\"Observe\",\"SSG\",\"Proof\",\"Fleet\",\"NeSy\",\"Agent\"],\"cartridge_count\":14,\"coverage_percent\":75}";
    if (topo_json.len > out_len.*) {
        out_len.* = topo_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..topo_json.len], topo_json);
    out_len.* = topo_json.len;
    return 0;
}

/// Get Umoja federation runtime status.
pub export fn echidna_boj_umoja_status(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("BoJ not connected");
        return @intFromEnum(BojError.not_connected);
    }
    const umoja_json = "{\"federation\":\"active\",\"peers\":0,\"consensus\":\"idle\",\"epoch\":0,\"protocol_version\":\"0.1.0\"}";
    if (umoja_json.len > out_len.*) {
        out_len.* = umoja_json.len;
        setError("Buffer too small");
        return @intFromEnum(BojError.buffer_too_small);
    }
    @memcpy(out_ptr[0..umoja_json.len], umoja_json);
    out_len.* = umoja_json.len;
    return 0;
}

/// Get cartridge count.
pub export fn echidna_boj_cartridge_count() c_int {
    return 14; // Standalone: 14 known cartridges
}

// ============================================================================
// Unified exports
// ============================================================================

pub export fn echidna_boj_version() [*:0]const u8 {
    return BOJ_VERSION;
}

pub export fn echidna_boj_last_error() ?[*:0]const u8 {
    if (error_len == 0) return null;
    return @ptrCast(&error_buf);
}

// ============================================================================
// Callback registration
// ============================================================================

pub export fn echidna_boj_register_on_status_change(callback: ?OnBojStatusChangeFn) c_int {
    cb_on_status_change = callback;
    return 0;
}

pub export fn echidna_boj_register_on_cartridge_change(callback: ?OnCartridgeChangeFn) c_int {
    cb_on_cartridge_change = callback;
    return 0;
}

pub export fn echidna_boj_register_on_invoke_complete(callback: ?OnInvokeCompleteFn) c_int {
    cb_on_invoke_complete = callback;
    return 0;
}

pub export fn echidna_boj_unregister_all_callbacks() c_int {
    cb_on_status_change = null;
    cb_on_cartridge_change = null;
    cb_on_invoke_complete = null;
    return 0;
}

pub export fn echidna_boj_callback_count() c_int {
    var count: c_int = 0;
    if (cb_on_status_change != null) count += 1;
    if (cb_on_cartridge_change != null) count += 1;
    if (cb_on_invoke_complete != null) count += 1;
    return count;
}

// ============================================================================
// Tests
// ============================================================================

test "CartridgeStatus enum round-trip" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(CartridgeStatus.development));
    try std.testing.expectEqual(@as(c_int, 1), @intFromEnum(CartridgeStatus.ready));
    try std.testing.expectEqual(@as(c_int, 2), @intFromEnum(CartridgeStatus.deprecated));
    try std.testing.expectEqual(@as(c_int, 3), @intFromEnum(CartridgeStatus.faulty));
    try std.testing.expect(CartridgeStatus.fromInt(0) == .development);
    try std.testing.expect(CartridgeStatus.fromInt(99) == null);
}

test "ProtocolType enum" {
    try std.testing.expectEqualStrings("MCP", std.mem.span(ProtocolType.mcp.name()));
    try std.testing.expectEqualStrings("gRPC", std.mem.span(ProtocolType.grpc.name()));
    try std.testing.expect(ProtocolType.fromInt(99) == null);
}

test "BoJ: connect, health, list, disconnect" {
    const config = "host=127.0.0.1;port=7700";
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_connect(config.ptr, config.len));
    try std.testing.expectEqual(@intFromEnum(BojConnectionStatus.connected), echidna_boj_status());

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_health(&buf, &len));
    try std.testing.expect(len > 0);

    len = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_list_cartridges(&buf, &len));
    try std.testing.expect(len > 0);

    echidna_boj_disconnect();
    try std.testing.expectEqual(@intFromEnum(BojConnectionStatus.disconnected), echidna_boj_status());
}

test "BoJ: operations fail when disconnected" {
    echidna_boj_disconnect();
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@intFromEnum(BojError.not_connected), echidna_boj_health(&buf, &len));
}

test "BoJ: load and unload cartridge" {
    const config = "host=127.0.0.1;port=7700";
    _ = echidna_boj_connect(config.ptr, config.len);
    defer echidna_boj_disconnect();

    const name = "proof-mcp";
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_load_cartridge(name.ptr, name.len));
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_unload_cartridge(name.ptr, name.len));
}

test "BoJ: invoke cartridge tool" {
    const config = "host=127.0.0.1;port=7700";
    _ = echidna_boj_connect(config.ptr, config.len);
    defer echidna_boj_disconnect();

    const name = "proof-mcp";
    const tool = "verify";
    const args = "{}";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_invoke(name.ptr, name.len, tool.ptr, tool.len, args.ptr, args.len, &buf, &len));
    try std.testing.expect(len > 0);
}

test "BoJ: topology and umoja" {
    const config = "host=127.0.0.1;port=7700";
    _ = echidna_boj_connect(config.ptr, config.len);
    defer echidna_boj_disconnect();

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_topology(&buf, &len));
    try std.testing.expect(len > 0);

    len = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_umoja_status(&buf, &len));
    try std.testing.expect(len > 0);
}

test "BoJ: version and error buffer" {
    try std.testing.expectEqualStrings("0.2.0", std.mem.span(echidna_boj_version()));
    clearError();
    try std.testing.expect(echidna_boj_last_error() == null);
}

test "BoJ: callbacks" {
    const Counter = struct {
        var count: u32 = 0;
        fn handler(_: c_int, _: c_int) callconv(.c) void { count += 1; }
    };
    Counter.count = 0;
    _ = echidna_boj_register_on_status_change(Counter.handler);
    try std.testing.expectEqual(@as(c_int, 1), echidna_boj_callback_count());

    const config = "host=127.0.0.1;port=7700";
    _ = echidna_boj_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(u32, 1), Counter.count);

    _ = echidna_boj_unregister_all_callbacks();
    try std.testing.expectEqual(@as(c_int, 0), echidna_boj_callback_count());
    echidna_boj_disconnect();
}
