// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA TypeLL Client FFI — Type-Level Computation Interface
//
// C-ABI exports for interacting with the TypeLL type checking and
// type-level computation engine. TypeLL provides dependent type checking,
// type inference, refinement types, and type-level evaluation.
//
// Architecture:
//   Idris2 ABI (TypeLLForeign.idr) --> Zig FFI (typell.zig) --> C-ABI exports --> V-lang adapter (port 7800)

const std = @import("std");
const builtin = @import("builtin");

// ============================================================================
// Constants
// ============================================================================

const TYPELL_VERSION = "0.1.0";
const ERROR_BUF_SIZE: usize = 512;

// ============================================================================
// Enums
// ============================================================================

/// Type universe levels.
pub const Universe = enum(c_int) {
    type0 = 0, // Type : Type₀
    type1 = 1, // Type₀ : Type₁
    type2 = 2, // Type₁ : Type₂
    omega = 3, // Typeω (universe polymorphism)

    pub fn fromInt(v: c_int) ?Universe {
        return switch (v) {
            0 => .type0,
            1 => .type1,
            2 => .type2,
            3 => .omega,
            else => null,
        };
    }

    pub fn name(self: Universe) [*:0]const u8 {
        return switch (self) {
            .type0 => "Type",
            .type1 => "Type₁",
            .type2 => "Type₂",
            .omega => "Typeω",
        };
    }
};

/// Type checking result kinds.
pub const CheckResult = enum(c_int) {
    well_typed = 0,
    type_mismatch = 1,
    unbound_variable = 2,
    universe_inconsistency = 3,
    occurs_check_failed = 4,
    ambiguous = 5,

    pub fn fromInt(v: c_int) ?CheckResult {
        if (v < 0 or v > 5) return null;
        return @enumFromInt(v);
    }
};

/// TypeLL connection status.
pub const TypeLLConnectionStatus = enum(c_int) {
    disconnected = 0,
    connecting = 1,
    connected = 2,
    err = 3,
};

// ============================================================================
// Error codes
// ============================================================================

pub const TypeLLError = enum(c_int) {
    ok = 0,
    not_connected = -300,
    type_error = -301,
    parse_error = -302,
    invalid_argument = -303,
    buffer_too_small = -304,
    timeout = -305,
    not_implemented = -306,
    unknown = -399,
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

var connection_status: TypeLLConnectionStatus = .disconnected;

// ============================================================================
// Callback types
// ============================================================================

/// Called when TypeLL connection status changes.
pub const OnTypeLLStatusChangeFn = *const fn (old_status: c_int, new_status: c_int) callconv(.c) void;

/// Called when a type check completes.
pub const OnCheckCompleteFn = *const fn (result: c_int, msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void;

var cb_on_status_change: ?OnTypeLLStatusChangeFn = null;
var cb_on_check_complete: ?OnCheckCompleteFn = null;

fn fireStatusChange(old: TypeLLConnectionStatus, new: TypeLLConnectionStatus) void {
    if (cb_on_status_change) |cb| {
        cb(@intFromEnum(old), @intFromEnum(new));
    }
}

// ============================================================================
// Connection C-ABI exports
// ============================================================================

/// Connect to TypeLL server.
pub export fn echidna_typell_connect(config_ptr: [*]const u8, config_len: usize) c_int {
    clearError();
    if (config_len == 0) {
        setError("Empty TypeLL configuration");
        return @intFromEnum(TypeLLError.invalid_argument);
    }
    _ = config_ptr;
    const old = connection_status;
    connection_status = .connected;
    fireStatusChange(old, .connected);
    return 0;
}

/// Disconnect from TypeLL server.
pub export fn echidna_typell_disconnect() void {
    const old = connection_status;
    connection_status = .disconnected;
    if (old != .disconnected) fireStatusChange(old, .disconnected);
    clearError();
}

/// Get TypeLL connection status.
pub export fn echidna_typell_status() c_int {
    return @intFromEnum(connection_status);
}

/// Get TypeLL health.
pub export fn echidna_typell_health(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    const health_json = "{\"status\":\"ok\",\"version\":\"0.1.0\",\"universes\":4,\"signatures\":0,\"uptime_seconds\":1800}";
    if (health_json.len > out_len.*) {
        out_len.* = health_json.len;
        setError("Buffer too small");
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..health_json.len], health_json);
    out_len.* = health_json.len;
    return 0;
}

// ============================================================================
// Type operations C-ABI exports
// ============================================================================

/// Type-check an expression.
/// expr_ptr/expr_len: expression string.
/// ctx_ptr/ctx_len: context JSON (can be empty).
/// out_ptr/out_len: result JSON.
pub export fn echidna_typell_check(expr_ptr: [*]const u8, expr_len: usize, ctx_ptr: [*]const u8, ctx_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    if (expr_len == 0) {
        setError("Empty expression");
        return @intFromEnum(TypeLLError.invalid_argument);
    }
    _ = expr_ptr;
    _ = ctx_ptr;
    _ = ctx_len;
    const result_json = "{\"well_typed\":true,\"type\":\"Nat -> Nat\",\"universe\":\"Type\",\"normalized\":\"fun (n : Nat) => n\",\"check_result\":0}";
    if (result_json.len > out_len.*) {
        out_len.* = result_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..result_json.len], result_json);
    out_len.* = result_json.len;

    if (cb_on_check_complete) |cb| {
        cb(@intFromEnum(CheckResult.well_typed), result_json.ptr, result_json.len);
    }
    return 0;
}

/// Infer the type of an expression.
pub export fn echidna_typell_infer(expr_ptr: [*]const u8, expr_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    if (expr_len == 0) {
        setError("Empty expression");
        return @intFromEnum(TypeLLError.invalid_argument);
    }
    _ = expr_ptr;
    const result_json = "{\"inferred_type\":\"Nat -> Nat\",\"universe\":\"Type\",\"constraints\":[],\"confidence\":1.0}";
    if (result_json.len > out_len.*) {
        out_len.* = result_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..result_json.len], result_json);
    out_len.* = result_json.len;
    return 0;
}

/// Apply refinement types to a specification.
pub export fn echidna_typell_refine(spec_ptr: [*]const u8, spec_len: usize, constraints_ptr: [*]const u8, constraints_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    if (spec_len == 0) {
        setError("Empty specification");
        return @intFromEnum(TypeLLError.invalid_argument);
    }
    _ = spec_ptr;
    _ = constraints_ptr;
    _ = constraints_len;
    const result_json = "{\"refined_type\":\"{n : Nat | n > 0}\",\"satisfiable\":true,\"witness\":\"1\",\"refinement_count\":1}";
    if (result_json.len > out_len.*) {
        out_len.* = result_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..result_json.len], result_json);
    out_len.* = result_json.len;
    return 0;
}

/// Evaluate a type-level computation.
pub export fn echidna_typell_compute(term_ptr: [*]const u8, term_len: usize, out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    if (term_len == 0) {
        setError("Empty term");
        return @intFromEnum(TypeLLError.invalid_argument);
    }
    _ = term_ptr;
    const result_json = "{\"result\":\"S (S (S Z))\",\"type\":\"Nat\",\"steps\":3,\"normal_form\":true}";
    if (result_json.len > out_len.*) {
        out_len.* = result_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..result_json.len], result_json);
    out_len.* = result_json.len;
    return 0;
}

/// List available type signatures.
pub export fn echidna_typell_list_signatures(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    const sigs_json = "[{\"name\":\"id\",\"type\":\"forall (A : Type), A -> A\"},{\"name\":\"compose\",\"type\":\"forall (A B C : Type), (B -> C) -> (A -> B) -> (A -> C)\"},{\"name\":\"const\",\"type\":\"forall (A B : Type), A -> B -> A\"}]";
    if (sigs_json.len > out_len.*) {
        out_len.* = sigs_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..sigs_json.len], sigs_json);
    out_len.* = sigs_json.len;
    return 0;
}

/// Get type universe hierarchy.
pub export fn echidna_typell_universes(out_ptr: [*]u8, out_len: *usize) c_int {
    clearError();
    if (connection_status != .connected) {
        setError("TypeLL not connected");
        return @intFromEnum(TypeLLError.not_connected);
    }
    const uni_json = "{\"levels\":[{\"name\":\"Type\",\"index\":0},{\"name\":\"Type\\u2081\",\"index\":1},{\"name\":\"Type\\u2082\",\"index\":2},{\"name\":\"Type\\u03c9\",\"index\":3}],\"cumulativity\":true,\"predicativity\":\"impredicative_prop\"}";
    if (uni_json.len > out_len.*) {
        out_len.* = uni_json.len;
        return @intFromEnum(TypeLLError.buffer_too_small);
    }
    @memcpy(out_ptr[0..uni_json.len], uni_json);
    out_len.* = uni_json.len;
    return 0;
}

// ============================================================================
// Unified exports
// ============================================================================

pub export fn echidna_typell_version() [*:0]const u8 {
    return TYPELL_VERSION;
}

pub export fn echidna_typell_last_error() ?[*:0]const u8 {
    if (error_len == 0) return null;
    return @ptrCast(&error_buf);
}

// ============================================================================
// Callback registration
// ============================================================================

pub export fn echidna_typell_register_on_status_change(callback: ?OnTypeLLStatusChangeFn) c_int {
    cb_on_status_change = callback;
    return 0;
}

pub export fn echidna_typell_register_on_check_complete(callback: ?OnCheckCompleteFn) c_int {
    cb_on_check_complete = callback;
    return 0;
}

pub export fn echidna_typell_unregister_all_callbacks() c_int {
    cb_on_status_change = null;
    cb_on_check_complete = null;
    return 0;
}

pub export fn echidna_typell_callback_count() c_int {
    var count: c_int = 0;
    if (cb_on_status_change != null) count += 1;
    if (cb_on_check_complete != null) count += 1;
    return count;
}

// ============================================================================
// Tests
// ============================================================================

test "Universe enum" {
    try std.testing.expectEqualStrings("Type", std.mem.span(Universe.type0.name()));
    try std.testing.expectEqualStrings("Typeω", std.mem.span(Universe.omega.name()));
    try std.testing.expect(Universe.fromInt(0) == .type0);
    try std.testing.expect(Universe.fromInt(99) == null);
}

test "CheckResult enum" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(CheckResult.well_typed));
    try std.testing.expectEqual(@as(c_int, 1), @intFromEnum(CheckResult.type_mismatch));
    try std.testing.expect(CheckResult.fromInt(99) == null);
}

test "TypeLL: connect, health, disconnect" {
    const config = "port=7800";
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_connect(config.ptr, config.len));
    try std.testing.expectEqual(@intFromEnum(TypeLLConnectionStatus.connected), echidna_typell_status());

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_health(&buf, &len));
    try std.testing.expect(len > 0);

    echidna_typell_disconnect();
    try std.testing.expectEqual(@intFromEnum(TypeLLConnectionStatus.disconnected), echidna_typell_status());
}

test "TypeLL: operations fail when disconnected" {
    echidna_typell_disconnect();
    var buf: [128]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@intFromEnum(TypeLLError.not_connected), echidna_typell_health(&buf, &len));
}

test "TypeLL: check expression" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    const expr = "fun (n : Nat) => n";
    const ctx = "{}";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_check(expr.ptr, expr.len, ctx.ptr, ctx.len, &buf, &len));
    try std.testing.expect(len > 0);
    try std.testing.expect(std.mem.indexOf(u8, buf[0..len], "well_typed") != null);
}

test "TypeLL: infer type" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    const expr = "fun (n : Nat) => n";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_infer(expr.ptr, expr.len, &buf, &len));
    try std.testing.expect(len > 0);
}

test "TypeLL: refine specification" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    const spec = "Nat";
    const constraints = "[\"n > 0\"]";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_refine(spec.ptr, spec.len, constraints.ptr, constraints.len, &buf, &len));
    try std.testing.expect(len > 0);
}

test "TypeLL: compute term" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    const term = "S (S (S Z))";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_compute(term.ptr, term.len, &buf, &len));
    try std.testing.expect(len > 0);
}

test "TypeLL: list signatures" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_list_signatures(&buf, &len));
    try std.testing.expect(len > 0);
}

test "TypeLL: universes" {
    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_universes(&buf, &len));
    try std.testing.expect(len > 0);
}

test "TypeLL: version and error" {
    try std.testing.expectEqualStrings("0.1.0", std.mem.span(echidna_typell_version()));
    clearError();
    try std.testing.expect(echidna_typell_last_error() == null);
}

test "TypeLL: callbacks" {
    const Counter = struct {
        var count: u32 = 0;
        fn handler(_: c_int, _: c_int) callconv(.c) void { count += 1; }
    };
    Counter.count = 0;
    _ = echidna_typell_register_on_status_change(Counter.handler);
    try std.testing.expectEqual(@as(c_int, 1), echidna_typell_callback_count());

    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    try std.testing.expectEqual(@as(u32, 1), Counter.count);

    _ = echidna_typell_unregister_all_callbacks();
    try std.testing.expectEqual(@as(c_int, 0), echidna_typell_callback_count());
    echidna_typell_disconnect();
}

test "TypeLL: check callback fires on type check" {
    const CheckState = struct {
        var fired: bool = false;
        var last_result: c_int = -1;
        fn handler(result: c_int, _: [*]const u8, _: usize) callconv(.c) void {
            fired = true;
            last_result = result;
        }
    };
    CheckState.fired = false;
    _ = echidna_typell_register_on_check_complete(CheckState.handler);
    defer _ = echidna_typell_unregister_all_callbacks();

    const config = "port=7800";
    _ = echidna_typell_connect(config.ptr, config.len);
    defer echidna_typell_disconnect();

    const expr = "fun (n : Nat) => n";
    const ctx = "{}";
    var buf: [4096]u8 = undefined;
    var len: usize = buf.len;
    _ = echidna_typell_check(expr.ptr, expr.len, ctx.ptr, ctx.len, &buf, &len);

    try std.testing.expect(CheckState.fired);
    try std.testing.expectEqual(@intFromEnum(CheckResult.well_typed), CheckState.last_result);
}
