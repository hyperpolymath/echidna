// SPDX-License-Identifier: PMPL-1.0-or-later
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

//==============================================================================
// Import Chapel's C API
//==============================================================================

const chapel = @cImport({
    @cInclude("chapel_ffi_exports.h");
});

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
    const result = chapel.chapel_is_available();
    return result != 0;
}

/// Get Chapel metalayer version string
pub fn getChapelVersion(allocator: std.mem.Allocator) ![]const u8 {
    const c_version = chapel.chapel_get_version();
    if (c_version == null) {
        return error.ChapelRuntimeUnavailable;
    }

    const version_slice = std.mem.span(c_version);
    return try allocator.dupe(u8, version_slice);
}

/// Get count of provers available on this system (0-30)
pub fn availableProverCount() u32 {
    const count = chapel.chapel_available_prover_count();
    return if (count >= 0) @intCast(count) else 0;
}

/// Check if a specific prover is available
pub fn isProverAvailable(prover: ProverKind) bool {
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
    // Validate Chapel is available
    if (!isChapelAvailable()) {
        return error.ChapelRuntimeUnavailable;
    }

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

    // Convert Chapel result to Zig (copies strings)
    const result = try ProofResult.fromChapel(c_result, allocator);

    // Free Chapel-allocated strings
    chapel.chapel_free_result(&c_result);

    return result;
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

    const timeout: u32 = if (timeout_secs > 0) @intCast(timeout_secs) else 0;

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
    const c_version = allocator.dupeZ(u8, version) catch return null;
    allocator.free(version);
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
