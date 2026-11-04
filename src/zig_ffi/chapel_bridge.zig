// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Chapel FFI Bridge (Zig Layer) — 30 Prover Backends
//
// This module provides a type-safe bridge between Rust and Chapel.
// Chapel exports C functions → Zig imports and wraps them → Rust calls Zig.
//
// Architecture (per ZIG_FFI_ANALYSIS.md):
//   Chapel (C API) → Zig (@cImport) → Rust (safe calls)

const std = @import("std");
const options = @import("chapel_options");
const runtime_owner = @import("runtime_owner.zig");

//==============================================================================
// Import Chapel's C API
//==============================================================================

const chapel = @cImport({
    @cInclude("chapel_ffi_exports.h");
    @cInclude("stdlib.h");
});

// Chapel's qthreads runtime binds its process task bundle to the OS thread
// that initializes it. A once guard alone does not make foreign threads valid.
// Every real export, Chapel allocation/free, and finalization uses this owner.
// Stub builds call only the unavailable stubs and start no native runtime.
const ChapelRuntime = struct {
    var program_name = [_:0]u8{ 'e', 'c', 'h', 'i', 'd', 'n', 'a' };
    var arguments = [_]?[*:0]u8{ &program_name, null };

    extern fn chpl_library_init(argc: c_int, argv: [*]?[*:0]u8) void;
    extern fn chpl_library_finalize() void;
    extern fn chpl__init_parallel_proof_search(line: i64, file: i32) void;
    extern fn chpl__init_chapel_ffi_exports(line: i64, file: i32) void;

    pub fn initialize(_: *@This()) void {
        chpl_library_init(1, &arguments);
        chpl__init_parallel_proof_search(0, 0);
        chpl__init_chapel_ffi_exports(0, 0);
    }

    pub fn finalize(_: *@This()) void {
        chpl_library_finalize();
    }
};

var chapel_owner = runtime_owner.Owner(ChapelRuntime).init(.{});
var chapel_shutdown_once = std.once(registerChapelShutdown);

fn registerChapelShutdown() void {
    if (chapel.atexit(shutdownChapel) != 0) {
        // Refuse startup if normal process exit cannot join the owner.
        chapel_owner.shutdown() catch unreachable;
    }
}

fn shutdownChapel() callconv(.c) void {
    chapel_owner.shutdownForProcessExit() catch {
        // A fatal Chapel task can call exit while the owner waits for that task.
        // Never join active work from an unknown exit thread: fail the process.
        std.process.abort();
    };
}

fn callOnOwner(owner: anytype, comptime function: anytype, args: anytype, result: anytype) runtime_owner.CallError!void {
    const Context = struct {
        arguments: @TypeOf(args),
        result: @TypeOf(result),

        fn run(raw: *anyopaque) void {
            const self: *@This() = @ptrCast(@alignCast(raw));
            self.result.* = @call(.auto, function, self.arguments);
        }
    };
    var context = Context{ .arguments = args, .result = result };
    var work = runtime_owner.Work{ .context = &context, .run = Context.run };
    try owner.call(&work);
}

fn callOnChapelOwner(comptime function: anytype, args: anytype, result: anytype) runtime_owner.CallError!void {
    if (options.chapel_stubs) {
        result.* = @call(.auto, function, args);
        return;
    }
    chapel_shutdown_once.call();
    try callOnOwner(&chapel_owner, function, args, result);
}

//==============================================================================
// Core Types — all 30 prover backends
//==============================================================================

/// Prover identifiers — must match Chapel's PROVER_* constants
pub const ProverKind = enum(c_int) {
    // Interactive proof assistants (10)
    Agda = 0,
    Coq = 1,
    Lean = 2,
    Isabelle = 3,
    Idris2 = 4,
    FStar = 5,
    HOL4 = 6,
    HOLLight = 7,
    Nuprl = 8,
    Minlog = 9,

    // SMT solvers (3)
    Z3 = 10,
    CVC5 = 11,
    AltErgo = 12,

    // First-order ATPs (3)
    Vampire = 13,
    EProver = 14,
    SPASS = 15,

    // Declarative provers (7)
    Metamath = 16,
    Mizar = 17,
    PVS = 18,
    ACL2 = 19,
    TLAPS = 20,
    Twelf = 21,
    Imandra = 22,

    // Auto-active verifiers (2)
    Dafny = 23,
    Why3 = 24,

    // Constraint solvers (5)
    GLPK = 25,
    SCIP = 26,
    MiniZinc = 27,
    Chuffed = 28,
    ORTools = 29,

    /// Total number of prover backends
    pub const count: usize = 30;

    /// Convert to display string
    pub fn toString(self: ProverKind) []const u8 {
        return switch (self) {
            .Agda => "Agda",
            .Coq => "Coq",
            .Lean => "Lean",
            .Isabelle => "Isabelle",
            .Idris2 => "Idris2",
            .FStar => "F*",
            .HOL4 => "HOL4",
            .HOLLight => "HOL Light",
            .Nuprl => "Nuprl",
            .Minlog => "Minlog",
            .Z3 => "Z3",
            .CVC5 => "CVC5",
            .AltErgo => "Alt-Ergo",
            .Vampire => "Vampire",
            .EProver => "E Prover",
            .SPASS => "SPASS",
            .Metamath => "Metamath",
            .Mizar => "Mizar",
            .PVS => "PVS",
            .ACL2 => "ACL2",
            .TLAPS => "TLAPS",
            .Twelf => "Twelf",
            .Imandra => "Imandra",
            .Dafny => "Dafny",
            .Why3 => "Why3",
            .GLPK => "GLPK",
            .SCIP => "SCIP",
            .MiniZinc => "MiniZinc",
            .Chuffed => "Chuffed",
            .ORTools => "OR-Tools",
        };
    }
};

/// Prover category
pub const ProverCategory = enum(c_int) {
    Interactive = 0,
    Smt = 1,
    Atp = 2,
    Declarative = 3,
    AutoActive = 4,
    Constraint = 5,

    pub fn toString(self: ProverCategory) []const u8 {
        return switch (self) {
            .Interactive => "Interactive Proof Assistant",
            .Smt => "SMT Solver",
            .Atp => "First-Order ATP",
            .Declarative => "Declarative Prover",
            .AutoActive => "Auto-Active Verifier",
            .Constraint => "Constraint Solver",
        };
    }
};

/// Proof result (safe Zig wrapper around Chapel's CProofResult)
pub const ProofResult = struct {
    success: bool,
    prover: ?ProverKind,
    prover_name: ?[]const u8,
    time_seconds: f64,
    exit_code: i32,
    tactic_count: u32,
    error_message: ?[]const u8,
    category: ?ProverCategory,

    /// Create from Chapel's C result (copies strings, caller frees C result)
    pub fn fromChapel(c_result: chapel.CProofResult, allocator: std.mem.Allocator) !ProofResult {
        var result = ProofResult{
            .success = c_result.success != 0,
            .prover = null,
            .prover_name = null,
            .time_seconds = c_result.time_seconds,
            .exit_code = @intCast(c_result.exit_code),
            .tactic_count = @intCast(c_result.tactic_count),
            .error_message = null,
            .category = null,
        };
        errdefer result.deinit(allocator);

        // Parse prover ID
        if (c_result.prover_id >= 0 and c_result.prover_id < @as(c_int, ProverKind.count)) {
            result.prover = @enumFromInt(c_result.prover_id);
        }

        // Parse category
        if (c_result.category >= 0 and c_result.category <= 5) {
            result.category = @enumFromInt(c_result.category);
        }

        // Copy prover name if present
        if (c_result.prover_name) |name_ptr| {
            const name_slice = std.mem.span(name_ptr);
            result.prover_name = try allocator.dupe(u8, name_slice);
        }

        // Copy error message if present
        if (c_result.error_message) |err_ptr| {
            const err_slice = std.mem.span(err_ptr);
            result.error_message = try allocator.dupe(u8, err_slice);
        }

        return result;
    }

    // Transfer a temporary result into the caller's allocator on its thread.
    fn clone(self: ProofResult, allocator: std.mem.Allocator) !ProofResult {
        var copy = self;
        copy.prover_name = null;
        copy.error_message = null;
        errdefer copy.deinit(allocator);
        if (self.prover_name) |name| copy.prover_name = try allocator.dupe(u8, name);
        if (self.error_message) |message| copy.error_message = try allocator.dupe(u8, message);
        return copy;
    }

    /// Free owned strings
    pub fn deinit(self: *ProofResult, allocator: std.mem.Allocator) void {
        if (self.prover_name) |name| {
            allocator.free(name);
            self.prover_name = null;
        }
        if (self.error_message) |err| {
            allocator.free(err);
            self.error_message = null;
        }
    }
};

/// Error types for FFI operations
pub const ChapelError = error{
    InvalidGoal,
    InvalidTimeout,
    ChapelRuntimeUnavailable,
    ProofSearchFailed,
    OutOfMemory,
    AllocationFailed,
    UnknownProver,
};

//==============================================================================
// Chapel Runtime Queries
//==============================================================================

/// Check if Chapel runtime is available
pub fn isChapelAvailable() bool {
    var result: bool = undefined;
    callOnChapelOwner(isChapelAvailableOnOwner, .{}, &result) catch return false;
    return result;
}

fn isChapelAvailableOnOwner() bool {
    return chapel.chapel_is_available() != 0;
}

/// Get Chapel metalayer version string
pub fn getChapelVersion(allocator: std.mem.Allocator) ![]const u8 {
    return getChapelVersionUsing(NativeBridge{}, allocator);
}

fn getChapelVersionUsing(bridge: anytype, allocator: std.mem.Allocator) ![]const u8 {
    const temporary = try bridge.version();
    defer std.heap.c_allocator.free(temporary);
    return allocator.dupe(u8, temporary);
}

const NativeBridge = struct {
    fn version(_: @This()) ![]const u8 {
        var result: anyerror![]const u8 = undefined;
        try callOnChapelOwner(getChapelVersionOnOwner, .{}, &result);
        return result;
    }

    fn search(_: @This(), goal: []const u8, provers: ?[]const ProverKind, timeout_secs: u32) !ProofResult {
        var result: anyerror!ProofResult = undefined;
        try callOnChapelOwner(parallelProofSearchOnOwner, .{ goal, provers, timeout_secs }, &result);
        return result;
    }
};

fn getChapelVersionOnOwner() ![]const u8 {
    const allocator = std.heap.c_allocator;
    const c_version = chapel.chapel_get_version();
    if (c_version == null) {
        return error.ChapelRuntimeUnavailable;
    }

    const version_slice = std.mem.span(c_version);
    return try allocator.dupe(u8, version_slice);
}

/// Get count of provers available on this system (0-30)
pub fn availableProverCount() u32 {
    var result: u32 = undefined;
    callOnChapelOwner(availableProverCountOnOwner, .{}, &result) catch return 0;
    return result;
}

fn availableProverCountOnOwner() u32 {
    const count = chapel.chapel_available_prover_count();
    return if (count >= 0) @intCast(count) else 0;
}

/// Check if a specific prover is available
pub fn isProverAvailable(prover: ProverKind) bool {
    var result: bool = undefined;
    callOnChapelOwner(isProverAvailableOnOwner, .{prover}, &result) catch return false;
    return result;
}

fn isProverAvailableOnOwner(prover: ProverKind) bool {
    return chapel.chapel_is_prover_available(@intFromEnum(prover)) != 0;
}

//==============================================================================
// Main FFI Function: Parallel Proof Search
//==============================================================================

/// Call Chapel's parallel proof search across all 30 backends
///
/// Parameters:
///   - goal: Theorem statement to prove
///   - provers: Optional list of provers to use (null = use all 30)
///   - timeout_secs: Per-prover timeout in seconds (0 = default 300s)
///   - allocator: Memory allocator for result strings
///
/// Returns:
///   ProofResult with best successful proof or failure details.
///   Caller must call result.deinit() to free strings.
pub fn parallelProofSearch(
    goal: []const u8,
    provers: ?[]const ProverKind,
    timeout_secs: u32,
    allocator: std.mem.Allocator,
) !ProofResult {
    return parallelProofSearchUsing(NativeBridge{}, goal, provers, timeout_secs, allocator);
}

fn parallelProofSearchUsing(
    bridge: anytype,
    goal: []const u8,
    provers: ?[]const ProverKind,
    timeout_secs: u32,
    allocator: std.mem.Allocator,
) !ProofResult {
    if (timeout_secs > std.math.maxInt(c_int)) return error.InvalidTimeout;
    var temporary = try bridge.search(goal, provers, timeout_secs);
    defer temporary.deinit(std.heap.c_allocator);
    return temporary.clone(allocator);
}

fn parallelProofSearchOnOwner(
    goal: []const u8,
    provers: ?[]const ProverKind,
    timeout_secs: u32,
) !ProofResult {
    const allocator = std.heap.c_allocator;
    if (!isChapelAvailableOnOwner()) return error.ChapelRuntimeUnavailable;

    // Convert goal to C string
    const goal_cstr = try allocator.dupeZ(u8, goal);
    defer allocator.free(goal_cstr);

    // Prepare prover IDs array (or NULL for all provers)
    var prover_ids: ?[]c_int = null;
    var num_provers: c_int = 0;

    if (provers) |prover_list| {
        prover_ids = try allocator.alloc(c_int, prover_list.len);
        errdefer allocator.free(prover_ids.?);

        for (prover_list, 0..) |p, i| {
            prover_ids.?[i] = @intFromEnum(p);
        }
        num_provers = @intCast(prover_list.len);
    }
    defer if (prover_ids) |ids| allocator.free(ids);

    // Call Chapel FFI
    var c_result = chapel.chapel_parallel_search(
        goal_cstr.ptr,
        if (prover_ids) |ids| ids.ptr else null,
        num_provers,
        @intCast(timeout_secs),
    );

    // Copy and free on the owner even when copying fails. Only bridge-owned
    // strings cross back to the caller, so shutdown never races Chapel data.
    defer chapel.chapel_free_result(&c_result);
    return ProofResult.fromChapel(c_result, allocator);
}

//==============================================================================
// C-Compatible Exports for Rust
//==============================================================================

/// C-compatible proof result for Rust FFI
pub const CProofResultForRust = extern struct {
    success: c_int,
    prover_id: c_int,
    time_seconds: f64,
    exit_code: c_int,
    tactic_count: u32,
    category: c_int,
    prover_name: ?[*:0]const u8,
    error_message: ?[*:0]const u8,
};

/// Export for Rust: Parallel proof search
/// Rust must free the result using echidna_free_proof_result()
export fn echidna_prove_parallel(
    goal_cstr: [*:0]const u8,
    prover_ids: ?[*]const c_int,
    num_provers: c_int,
    timeout_secs: c_int,
) CProofResultForRust {
    const allocator = std.heap.c_allocator;
    if (timeout_secs < 0) {
        return .{
            .success = 0,
            .prover_id = -1,
            .time_seconds = 0.0,
            .exit_code = -2,
            .tactic_count = 0,
            .category = -1,
            .prover_name = null,
            .error_message = allocator.dupeZ(u8, "Invalid negative timeout") catch null,
        };
    }

    const goal = std.mem.span(goal_cstr);

    // Convert prover IDs to slice
    var prover_list: ?[]ProverKind = null;
    if (prover_ids != null and num_provers > 0) {
        prover_list = allocator.alloc(ProverKind, @intCast(num_provers)) catch {
            return .{
                .success = 0,
                .prover_id = -1,
                .time_seconds = 0.0,
                .exit_code = -1,
                .tactic_count = 0,
                .category = -1,
                .prover_name = null,
                .error_message = allocator.dupeZ(u8, "Memory allocation failed") catch null,
            };
        };

        const ids_slice = prover_ids.?[0..@intCast(num_provers)];
        for (ids_slice, 0..) |id, i| {
            prover_list.?[i] = @enumFromInt(id);
        }
    }
    defer if (prover_list) |list| allocator.free(list);

    const timeout: u32 = @intCast(timeout_secs);

    // Call Chapel via Zig bridge
    var result = parallelProofSearch(goal, prover_list, timeout, allocator) catch {
        return .{
            .success = 0,
            .prover_id = -1,
            .time_seconds = 0.0,
            .exit_code = -1,
            .tactic_count = 0,
            .category = -1,
            .prover_name = null,
            .error_message = allocator.dupeZ(u8, "Proof search failed") catch null,
        };
    };

    // Convert to C-compatible result
    const c_result = CProofResultForRust{
        .success = if (result.success) 1 else 0,
        .prover_id = if (result.prover) |p| @intFromEnum(p) else -1,
        .time_seconds = result.time_seconds,
        .exit_code = result.exit_code,
        .tactic_count = result.tactic_count,
        .category = if (result.category) |c| @intFromEnum(c) else -1,
        .prover_name = if (result.prover_name) |name|
            (allocator.dupeZ(u8, name) catch null)
        else
            null,
        .error_message = if (result.error_message) |err|
            (allocator.dupeZ(u8, err) catch null)
        else
            null,
    };

    // Free Zig-owned strings (we've duplicated them for Rust)
    result.deinit(allocator);

    return c_result;
}

/// Free a proof result allocated by echidna_prove_parallel()
export fn echidna_free_proof_result(result: *CProofResultForRust) void {
    const allocator = std.heap.c_allocator;

    if (result.prover_name) |name| {
        const name_slice = std.mem.span(name);
        allocator.free(name_slice);
        result.prover_name = null;
    }

    if (result.error_message) |err| {
        const err_slice = std.mem.span(err);
        allocator.free(err_slice);
        result.error_message = null;
    }
}

/// Export for Rust: Check if Chapel is available
export fn echidna_chapel_is_available() c_int {
    return if (isChapelAvailable()) 1 else 0;
}

/// Export for Rust: Get Chapel version
export fn echidna_chapel_get_version() ?[*:0]const u8 {
    const allocator = std.heap.c_allocator;
    const version = getChapelVersion(allocator) catch return null;
    defer allocator.free(version);
    const c_version = allocator.dupeZ(u8, version) catch return null;
    return c_version.ptr;
}

/// Export for Rust: Get available prover count
export fn echidna_chapel_available_prover_count() c_int {
    return @intCast(availableProverCount());
}

/// Export for Rust: Check if a specific prover is available
export fn echidna_chapel_is_prover_available(prover_id: c_int) c_int {
    if (prover_id < 0 or prover_id >= ProverKind.count) return 0;
    return if (isProverAvailable(@enumFromInt(prover_id))) 1 else 0;
}

/// Free a string allocated by echidna_chapel_get_version()
export fn echidna_free_string(str: ?[*:0]const u8) void {
    const s = str orelse return;
    const allocator = std.heap.c_allocator;
    const slice = std.mem.span(s);
    allocator.free(slice);
}

//==============================================================================
// Tests
//==============================================================================

test "prover_kind_to_string_all_30" {
    try std.testing.expectEqualStrings("Agda", ProverKind.Agda.toString());
    try std.testing.expectEqualStrings("Lean", ProverKind.Lean.toString());
    try std.testing.expectEqualStrings("HOL Light", ProverKind.HOLLight.toString());
    try std.testing.expectEqualStrings("Z3", ProverKind.Z3.toString());
    try std.testing.expectEqualStrings("Vampire", ProverKind.Vampire.toString());
    try std.testing.expectEqualStrings("Dafny", ProverKind.Dafny.toString());
    try std.testing.expectEqualStrings("GLPK", ProverKind.GLPK.toString());
    try std.testing.expectEqualStrings("OR-Tools", ProverKind.ORTools.toString());
    try std.testing.expectEqual(@as(usize, 30), ProverKind.count);
}

test "prover_category_to_string" {
    try std.testing.expectEqualStrings("SMT Solver", ProverCategory.Smt.toString());
    try std.testing.expectEqualStrings("Interactive Proof Assistant", ProverCategory.Interactive.toString());
    try std.testing.expectEqualStrings("Constraint Solver", ProverCategory.Constraint.toString());
}

test "stub_chapel_unavailable" {
    // When using stubs, Chapel should report unavailable
    try std.testing.expectEqual(false, isChapelAvailable());
    try std.testing.expectEqual(@as(u32, 0), availableProverCount());
}


// This allocator is deliberately bound to its creating thread. Returning null
// on foreign-thread allocation makes the previous owner-side clone observable.
const CallerAllocator = struct {
    thread_id: std.Thread.Id,
    wrong_thread: bool = false,
    callbacks: usize = 0,
    allocations: usize = 0,
    frees: usize = 0,
    live_bytes: usize = 0,
    fail_after: usize = std.math.maxInt(usize),

    fn init(fail_after: usize) @This() {
        return .{ .thread_id = std.Thread.getCurrentId(), .fail_after = fail_after };
    }

    fn allocator(self: *@This()) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{
            .alloc = alloc,
            .resize = resize,
            .remap = remap,
            .free = free,
        } };
    }

    fn record(self: *@This()) bool {
        self.callbacks += 1;
        if (self.thread_id != std.Thread.getCurrentId()) {
            self.wrong_thread = true;
            return false;
        }
        return true;
    }

    fn alloc(raw: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *@This() = @ptrCast(@alignCast(raw));
        if (!self.record() or self.allocations >= self.fail_after) return null;
        const pointer = std.heap.c_allocator.rawAlloc(len, alignment, ret_addr) orelse return null;
        self.allocations += 1;
        self.live_bytes += len;
        return pointer;
    }

    fn resize(raw: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *@This() = @ptrCast(@alignCast(raw));
        _ = self.record();
        _ = memory;
        _ = alignment;
        _ = new_len;
        _ = ret_addr;
        return false;
    }

    fn remap(raw: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *@This() = @ptrCast(@alignCast(raw));
        _ = self.record();
        _ = memory;
        _ = alignment;
        _ = new_len;
        _ = ret_addr;
        return null;
    }

    fn free(raw: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *@This() = @ptrCast(@alignCast(raw));
        _ = self.record();
        // The backing allocator is cross-thread safe so a failed assertion
        // never requires corrupting memory or leaking the test allocation.
        std.heap.c_allocator.rawFree(memory, alignment, ret_addr);
        self.frees += 1;
        self.live_bytes -= memory.len;
    }
};

// The production transfer helpers above receive a completed, c_allocator-owned
// result from this real OS owner. The fixture is not a Chapel runtime receipt.
const TransferFixture = struct {
    const Runtime = struct {
        initialized: usize = 0,
        finalized: usize = 0,

        pub fn initialize(self: *@This()) void {
            self.initialized += 1;
        }

        pub fn finalize(self: *@This()) void {
            self.finalized += 1;
        }
    };

    owner: runtime_owner.Owner(Runtime) = runtime_owner.Owner(Runtime).init(.{}),
    submissions: usize = 0,
    producer_thread: std.Thread.Id = 0,
    requested_provers: usize = 0,
    requested_timeout: u32 = 0,

    fn version(self: *@This()) ![]const u8 {
        self.submissions += 1;
        var result: anyerror![]const u8 = undefined;
        try callOnOwner(&self.owner, produceVersion, .{self}, &result);
        return result;
    }

    fn produceVersion(self: *@This()) ![]const u8 {
        self.producer_thread = std.Thread.getCurrentId();
        return std.heap.c_allocator.dupe(u8, "recorded owner version");
    }

    fn search(self: *@This(), goal: []const u8, provers: ?[]const ProverKind, timeout_secs: u32) !ProofResult {
        _ = goal;
        self.submissions += 1;
        var result: anyerror!ProofResult = undefined;
        try callOnOwner(&self.owner, produceResult, .{ self, provers, timeout_secs }, &result);
        return result;
    }

    fn produceResult(self: *@This(), provers: ?[]const ProverKind, timeout_secs: u32) !ProofResult {
        self.producer_thread = std.Thread.getCurrentId();
        self.requested_provers = if (provers) |ids| ids.len else 0;
        self.requested_timeout = timeout_secs;
        const allocator = std.heap.c_allocator;
        var result = ProofResult{
            .success = false,
            .prover = .Z3,
            .prover_name = null,
            .time_seconds = 0.25,
            .exit_code = -1,
            .tactic_count = 0,
            .error_message = null,
            .category = .Smt,
        };
        errdefer result.deinit(allocator);
        result.prover_name = try allocator.dupe(u8, "fixture prover");
        result.error_message = try allocator.dupe(u8, "fixture failure");
        return result;
    }
};

test "owner results are cloned and freed using only caller-thread allocator callbacks" {
    var fixture = TransferFixture{};
    defer fixture.owner.shutdown() catch unreachable;
    var caller_allocator = CallerAllocator.init(std.math.maxInt(usize));
    const allocator = caller_allocator.allocator();

    {
        const version = try getChapelVersionUsing(&fixture, allocator);
        defer allocator.free(version);
        try std.testing.expectEqualStrings("recorded owner version", version);
    }
    {
        var result = try parallelProofSearchUsing(&fixture, "True", &.{.Z3}, 1, allocator);
        defer result.deinit(allocator);
        try std.testing.expect(!result.success);
        try std.testing.expectEqualStrings("fixture prover", result.prover_name.?);
        try std.testing.expectEqualStrings("fixture failure", result.error_message.?);
    }
    try fixture.owner.shutdown();

    try std.testing.expect(fixture.producer_thread != caller_allocator.thread_id);
    try std.testing.expect(!caller_allocator.wrong_thread);
    try std.testing.expectEqual(@as(usize, 3), caller_allocator.allocations);
    try std.testing.expectEqual(caller_allocator.allocations, caller_allocator.frees);
    try std.testing.expectEqual(@as(usize, 0), caller_allocator.live_bytes);
    try std.testing.expectEqual(@as(usize, 1), fixture.requested_provers);
    try std.testing.expectEqual(@as(usize, 1), fixture.owner.runtime.initialized);
    try std.testing.expectEqual(@as(usize, 1), fixture.owner.runtime.finalized);
}

test "caller-side first and partial copy failures release every supplied allocation" {
    var fixture = TransferFixture{};
    defer fixture.owner.shutdown() catch unreachable;
    for ([_]usize{ 0, 1 }) |fail_after| {
        var caller_allocator = CallerAllocator.init(fail_after);
        try std.testing.expectError(
            error.OutOfMemory,
            parallelProofSearchUsing(&fixture, "True", &.{.Z3}, 1, caller_allocator.allocator()),
        );
        try std.testing.expect(fixture.producer_thread != caller_allocator.thread_id);
        try std.testing.expect(!caller_allocator.wrong_thread);
        try std.testing.expectEqual(fail_after, caller_allocator.allocations);
        try std.testing.expectEqual(caller_allocator.allocations, caller_allocator.frees);
        try std.testing.expectEqual(@as(usize, 0), caller_allocator.live_bytes);
        try std.testing.expectEqual(@as(usize, 1), fixture.requested_provers);
    }
    var version_allocator = CallerAllocator.init(0);
    try std.testing.expectError(error.OutOfMemory, getChapelVersionUsing(&fixture, version_allocator.allocator()));
    try std.testing.expect(!version_allocator.wrong_thread);
    try std.testing.expectEqual(@as(usize, 1), version_allocator.callbacks);
    try std.testing.expectEqual(@as(usize, 0), version_allocator.live_bytes);
}

test "Zig timeout overflow is refused before owner admission and zero retains default semantics" {
    var fixture = TransferFixture{};
    defer fixture.owner.shutdown() catch unreachable;
    var caller_allocator = CallerAllocator.init(std.math.maxInt(usize));
    const allocator = caller_allocator.allocator();
    const maximum: u32 = std.math.maxInt(c_int);
    try std.testing.expectError(
        error.InvalidTimeout,
        parallelProofSearchUsing(&fixture, "True", &.{.Z3}, maximum + 1, allocator),
    );
    try std.testing.expectEqual(@as(usize, 0), fixture.submissions);
    try std.testing.expectEqual(@as(usize, 0), fixture.owner.runtime.initialized);
    try std.testing.expectEqual(@as(usize, 0), caller_allocator.callbacks);

    for ([_]u32{ 0, maximum }) |timeout_secs| {
        var result = try parallelProofSearchUsing(&fixture, "True", &.{.Z3}, timeout_secs, allocator);
        result.deinit(allocator);
        try std.testing.expectEqual(timeout_secs, fixture.requested_timeout);
    }
    try std.testing.expectEqual(@as(usize, 0), caller_allocator.live_bytes);
}

test "negative C timeouts are rejected instead of selecting the native default" {
    for ([_]c_int{ -1, std.math.minInt(c_int) }) |timeout_secs| {
        var result = echidna_prove_parallel("True", null, 0, timeout_secs);
        defer echidna_free_proof_result(&result);
        try std.testing.expectEqual(@as(c_int, 0), result.success);
        try std.testing.expectEqual(@as(c_int, -2), result.exit_code);
        try std.testing.expectEqualStrings("Invalid negative timeout", std.mem.span(result.error_message.?));
    }
    if (options.chapel_stubs) {
        var default_result = echidna_prove_parallel("True", null, 0, 0);
        defer echidna_free_proof_result(&default_result);
        try std.testing.expectEqual(@as(c_int, 0), default_result.success);
        try std.testing.expectEqual(@as(c_int, -1), default_result.exit_code);
        try std.testing.expect(chapel_owner.worker == null);
    }
}
