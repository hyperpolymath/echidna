// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA Chapel FFI Bridge (Zig Layer)
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

// Chapel generates C headers from its `export` functions
// We import them directly using Zig's @cImport
const chapel = @cImport({
    // These headers are generated when Chapel code is compiled
    @cInclude("chapel_ffi_exports.h");
});

//==============================================================================
// Core Types (C-compatible, match Chapel's extern records)
//==============================================================================

/// Prover identifiers (must match Chapel's PROVER_* constants)
pub const ProverKind = enum(c_int) {
    Coq = 0,
    Lean = 1,
    Isabelle = 2,
    Agda = 3,
    Z3 = 4,
    CVC5 = 5,
    ACL2 = 6,
    PVS = 7,
    HOL4 = 8,
    Metamath = 9,
    HOLLight = 10,
    Mizar = 11,

    /// Convert to string for display
    pub fn toString(self: ProverKind) []const u8 {
        return switch (self) {
            .Coq => "Coq",
            .Lean => "Lean",
            .Isabelle => "Isabelle",
            .Agda => "Agda",
            .Z3 => "Z3",
            .CVC5 => "CVC5",
            .ACL2 => "ACL2",
            .PVS => "PVS",
            .HOL4 => "HOL4",
            .Metamath => "Metamath",
            .HOLLight => "HOL Light",
            .Mizar => "Mizar",
        };
    }
};

/// Proof result (safe Zig wrapper around Chapel's CProofResult)
pub const ProofResult = struct {
    success: bool,
    prover: ?ProverKind,
    time_seconds: f64,
    tactic_count: u32,
    prover_name: ?[]const u8, // Optional owned string
    error_message: ?[]const u8, // Optional owned string

    /// Create from Chapel's C result (takes ownership of strings)
    pub fn fromChapel(c_result: chapel.CProofResult, allocator: std.mem.Allocator) !ProofResult {
        var result = ProofResult{
            .success = c_result.success != 0,
            .prover = null,
            .time_seconds = c_result.time_seconds,
            .tactic_count = @intCast(c_result.tactic_count),
            .prover_name = null,
            .error_message = null,
        };

        // Copy prover name if present
        if (c_result.prover_name != null) {
            const name_cstr = c_result.prover_name;
            const name_slice = std.mem.span(name_cstr);
            result.prover_name = try allocator.dupe(u8, name_slice);

            // Try to parse prover kind from name
            result.prover = proverKindFromString(name_slice) catch null;
        }

        // Copy error message if present
        if (c_result.error_message != null) {
            const err_cstr = c_result.error_message;
            const err_slice = std.mem.span(err_cstr);
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
// Helper Functions
//==============================================================================

/// Parse ProverKind from string name
fn proverKindFromString(name: []const u8) !ProverKind {
    if (std.mem.eql(u8, name, "Coq")) return .Coq;
    if (std.mem.eql(u8, name, "Lean")) return .Lean;
    if (std.mem.eql(u8, name, "Isabelle")) return .Isabelle;
    if (std.mem.eql(u8, name, "Agda")) return .Agda;
    if (std.mem.eql(u8, name, "Z3")) return .Z3;
    if (std.mem.eql(u8, name, "CVC5")) return .CVC5;
    if (std.mem.eql(u8, name, "ACL2")) return .ACL2;
    if (std.mem.eql(u8, name, "PVS")) return .PVS;
    if (std.mem.eql(u8, name, "HOL4")) return .HOL4;
    if (std.mem.eql(u8, name, "Metamath")) return .Metamath;
    if (std.mem.eql(u8, name, "HOL Light")) return .HOLLight;
    if (std.mem.eql(u8, name, "Mizar")) return .Mizar;
    return error.UnknownProver;
}

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

//==============================================================================
// Main FFI Function: Parallel Proof Search
//==============================================================================

/// Call Chapel's parallel proof search
///
/// Parameters:
///   - goal: Theorem statement to prove
///   - provers: Optional list of provers to use (null = use all 12)
///   - allocator: Memory allocator for result strings
///
/// Returns:
///   ProofResult with success/failure and proof details
///   Caller must call result.deinit() to free strings
pub fn parallelProofSearch(
    goal: []const u8,
    provers: ?[]const ProverKind,
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
    const c_result = chapel.chapel_parallel_search(
        goal_cstr.ptr,
        if (prover_ids) |ids| ids.ptr else null,
        num_provers,
    );

    // Convert Chapel result to Zig (takes ownership of strings)
    var result = try ProofResult.fromChapel(c_result, allocator);

    // Free Chapel-allocated strings (we've copied them)
    chapel.chapel_free_result(@constCast(&c_result));

    return result;
}

//==============================================================================
// C-Compatible Exports for Rust
//==============================================================================

/// C-compatible proof result for Rust FFI
pub const CProofResultForRust = extern struct {
    success: c_int, // 0 = false, 1 = true
    prover_id: c_int, // ProverKind enum value (-1 if unknown)
    time_seconds: f64,
    tactic_count: u32,
    prover_name: ?[*:0]const u8, // Null-terminated string (Rust must free)
    error_message: ?[*:0]const u8, // Null-terminated string (Rust must free)
};

/// Export for Rust: Parallel proof search
/// Rust must free the result using echidna_free_proof_result()
export fn echidna_prove_parallel(
    goal_cstr: [*:0]const u8,
    prover_ids: ?[*]const c_int,
    num_provers: c_int,
) CProofResultForRust {
    const allocator = std.heap.c_allocator;

    // Convert C string to slice
    const goal = std.mem.span(goal_cstr);

    // Convert prover IDs to slice
    var prover_list: ?[]ProverKind = null;
    if (prover_ids != null and num_provers > 0) {
        const ids_slice = prover_ids.?[0..@intCast(num_provers)];
        prover_list = allocator.alloc(ProverKind, ids_slice.len) catch {
            // Allocation failed
            return .{
                .success = 0,
                .prover_id = -1,
                .time_seconds = 0.0,
                .tactic_count = 0,
                .prover_name = null,
                .error_message = allocator.dupeZ(u8, "Memory allocation failed") catch null,
            };
        };

        for (ids_slice, 0..) |id, i| {
            prover_list.?[i] = @enumFromInt(id);
        }
    }
    defer if (prover_list) |list| allocator.free(list);

    // Call Chapel via Zig bridge
    var result = parallelProofSearch(goal, prover_list, allocator) catch {
        // Error in proof search
        return .{
            .success = 0,
            .prover_id = -1,
            .time_seconds = 0.0,
            .tactic_count = 0,
            .prover_name = null,
            .error_message = allocator.dupeZ(u8, "Proof search failed") catch null,
        };
    };

    // Convert to C-compatible result
    const c_result = CProofResultForRust{
        .success = if (result.success) 1 else 0,
        .prover_id = if (result.prover) |p| @intFromEnum(p) else -1,
        .time_seconds = result.time_seconds,
        .tactic_count = result.tactic_count,
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
/// Rust must free the returned string
export fn echidna_chapel_get_version() ?[*:0]const u8 {
    const allocator = std.heap.c_allocator;
    const version = getChapelVersion(allocator) catch return null;
    const c_version = allocator.dupeZ(u8, version) catch return null;
    allocator.free(version);
    return c_version.ptr;
}

/// Free a version string allocated by echidna_chapel_get_version()
export fn echidna_free_string(str: ?[*:0]const u8) void {
    const s = str orelse return;
    const allocator = std.heap.c_allocator;
    const slice = std.mem.span(s);
    allocator.free(slice);
}

//==============================================================================
// Tests
//==============================================================================

test "prover_kind_to_string" {
    try std.testing.expectEqualStrings("Coq", ProverKind.Coq.toString());
    try std.testing.expectEqualStrings("Lean", ProverKind.Lean.toString());
    try std.testing.expectEqualStrings("HOL Light", ProverKind.HOLLight.toString());
}

test "prover_kind_from_string" {
    const coq = try proverKindFromString("Coq");
    try std.testing.expectEqual(ProverKind.Coq, coq);

    const lean = try proverKindFromString("Lean");
    try std.testing.expectEqual(ProverKind.Lean, lean);
}
