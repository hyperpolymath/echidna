// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! ECHIDNA FFI Bridge Layer
//!
//! Provides C-compatible foreign function interface for integrating
//! ECHIDNA's theorem proving capabilities with external systems like
//! bulletproof-core (Idris 2) and other language runtimes.
//!
//! Architecture:
//! - Zig provides zero-overhead C ABI compatibility
//! - Can be called from Rust, Idris 2, Julia, or any C-compatible language
//! - Memory-safe with explicit allocation strategies
//! - No hidden runtime or garbage collector

const std = @import("std");
const Allocator = std.mem.Allocator;

// ============================================================================
// Type Definitions
// ============================================================================

/// Opaque handle to a prover instance
pub const ProverHandle = *anyopaque;

/// Opaque handle to a proof state
pub const ProofStateHandle = *anyopaque;

/// Opaque handle to a term
pub const TermHandle = *anyopaque;

/// Prover kind enumeration (mirrors Rust ProverKind)
pub const ProverKind = enum(u8) {
    Agda = 0,
    Coq = 1,
    Lean = 2,
    Isabelle = 3,
    Z3 = 4,
    CVC5 = 5,
    Metamath = 6,
    HOLLight = 7,
    Mizar = 8,
    PVS = 9,
    ACL2 = 10,
    HOL4 = 11,
    Idris2 = 12,
};

/// Result status codes
pub const Status = enum(i32) {
    Ok = 0,
    ErrorInvalidHandle = -1,
    ErrorInvalidArgument = -2,
    ErrorProverNotFound = -3,
    ErrorParseFailure = -4,
    ErrorTacticFailure = -5,
    ErrorVerificationFailure = -6,
    ErrorOutOfMemory = -7,
    ErrorTimeout = -8,
    ErrorNotImplemented = -9,
    ErrorUnknown = -99,
};

/// Tactic result type
pub const TacticResultKind = enum(u8) {
    Success = 0,
    Error = 1,
    QED = 2,
};

/// String slice for FFI (non-owning)
pub const StringSlice = extern struct {
    ptr: [*]const u8,
    len: usize,

    pub fn fromSlice(slice: []const u8) StringSlice {
        return .{
            .ptr = slice.ptr,
            .len = slice.len,
        };
    }

    pub fn toSlice(self: StringSlice) []const u8 {
        return self.ptr[0..self.len];
    }

    pub fn empty() StringSlice {
        return .{ .ptr = undefined, .len = 0 };
    }
};

/// Owned string for FFI (must be freed)
pub const OwnedString = extern struct {
    ptr: [*]u8,
    len: usize,
    capacity: usize,

    pub fn fromAllocated(allocator: Allocator, str: []const u8) !OwnedString {
        const buf = try allocator.alloc(u8, str.len);
        @memcpy(buf, str);
        return .{
            .ptr = buf.ptr,
            .len = str.len,
            .capacity = str.len,
        };
    }

    pub fn deinit(self: *OwnedString, allocator: Allocator) void {
        if (self.capacity > 0) {
            allocator.free(self.ptr[0..self.capacity]);
        }
        self.* = .{ .ptr = undefined, .len = 0, .capacity = 0 };
    }
};

/// Prover configuration
pub const ProverConfig = extern struct {
    executable_path: StringSlice,
    library_paths: [*]StringSlice,
    library_paths_len: usize,
    timeout_ms: u64,
    neural_enabled: bool,
    _padding: [7]u8 = [_]u8{0} ** 7,
};

/// Term type enumeration
pub const TermKind = enum(u8) {
    Var = 0,
    Const = 1,
    App = 2,
    Lambda = 3,
    Pi = 4,
    Type = 5,
    Sort = 6,
    Let = 7,
    Match = 8,
    Fix = 9,
    Hole = 10,
    Meta = 11,
    ProverSpecific = 12,
};

/// Serialized term representation for FFI
pub const SerializedTerm = extern struct {
    kind: TermKind,
    _padding: [3]u8 = [_]u8{0} ** 3,
    data_len: u32,
    data: [*]const u8,

    pub fn getData(self: SerializedTerm) []const u8 {
        return self.data[0..self.data_len];
    }
};

/// Goal representation for FFI
pub const Goal = extern struct {
    id: StringSlice,
    target: SerializedTerm,
    hypotheses_count: u32,
    _padding: [4]u8 = [_]u8{0} ** 4,
};

/// Tactic types
pub const TacticKind = enum(u8) {
    Apply = 0,
    Intro = 1,
    Cases = 2,
    Induction = 3,
    Rewrite = 4,
    Simplify = 5,
    Reflexivity = 6,
    Assumption = 7,
    Exact = 8,
    Custom = 9,
};

/// Tactic representation for FFI
pub const Tactic = extern struct {
    kind: TacticKind,
    _padding: [3]u8 = [_]u8{0} ** 3,
    arg_len: u32,
    arg: [*]const u8,

    pub fn getArg(self: Tactic) []const u8 {
        return self.arg[0..self.arg_len];
    }
};

/// Tactic result for FFI
pub const TacticResult = extern struct {
    kind: TacticResultKind,
    _padding: [3]u8 = [_]u8{0} ** 3,
    message_len: u32,
    message: [*]const u8,
    new_state: ?ProofStateHandle,

    pub fn getMessage(self: TacticResult) []const u8 {
        return self.message[0..self.message_len];
    }
};

// ============================================================================
// Global State
// ============================================================================

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();

/// Registry of active prover instances
var prover_registry: std.AutoHashMap(usize, ProverInstance) = undefined;
var registry_initialized: bool = false;
var next_handle_id: usize = 1;

const ProverInstance = struct {
    kind: ProverKind,
    config: ProverConfig,
    // Opaque pointer to language-specific prover state
    native_handle: ?*anyopaque,
};

fn initRegistry() void {
    if (!registry_initialized) {
        prover_registry = std.AutoHashMap(usize, ProverInstance).init(allocator);
        registry_initialized = true;
    }
}

// ============================================================================
// Prover Lifecycle Functions
// ============================================================================

/// Initialize the FFI layer. Must be called before any other functions.
export fn echidna_init() Status {
    initRegistry();
    return .Ok;
}

/// Shutdown the FFI layer and release all resources.
export fn echidna_shutdown() Status {
    if (registry_initialized) {
        var iter = prover_registry.iterator();
        while (iter.next()) |_| {
            // Clean up each prover instance
        }
        prover_registry.deinit();
        registry_initialized = false;
    }
    return .Ok;
}

/// Create a new prover instance.
export fn echidna_prover_create(
    kind: ProverKind,
    config: *const ProverConfig,
    out_handle: *ProverHandle,
) Status {
    initRegistry();

    const handle_id = next_handle_id;
    next_handle_id += 1;

    const instance = ProverInstance{
        .kind = kind,
        .config = config.*,
        .native_handle = null,
    };

    prover_registry.put(handle_id, instance) catch {
        return .ErrorOutOfMemory;
    };

    out_handle.* = @ptrFromInt(handle_id);
    return .Ok;
}

/// Destroy a prover instance.
export fn echidna_prover_destroy(handle: ProverHandle) Status {
    const handle_id = @intFromPtr(handle);
    if (prover_registry.remove(handle_id)) |_| {
        return .Ok;
    }
    return .ErrorInvalidHandle;
}

/// Get the version string of a prover.
export fn echidna_prover_version(
    handle: ProverHandle,
    out_version: *OwnedString,
) Status {
    const handle_id = @intFromPtr(handle);
    const instance = prover_registry.get(handle_id) orelse {
        return .ErrorInvalidHandle;
    };

    const version_str = switch (instance.kind) {
        .Agda => "Agda 2.6.x (ECHIDNA FFI)",
        .Coq => "Coq 8.x (ECHIDNA FFI)",
        .Lean => "Lean 4.x (ECHIDNA FFI)",
        .Isabelle => "Isabelle 2024 (ECHIDNA FFI)",
        .Z3 => "Z3 4.x (ECHIDNA FFI)",
        .CVC5 => "CVC5 1.x (ECHIDNA FFI)",
        .Metamath => "Metamath (ECHIDNA FFI)",
        .HOLLight => "HOL Light (ECHIDNA FFI)",
        .Mizar => "Mizar 8.x (ECHIDNA FFI)",
        .PVS => "PVS 7.x (ECHIDNA FFI)",
        .ACL2 => "ACL2 8.x (ECHIDNA FFI)",
        .HOL4 => "HOL4 (ECHIDNA FFI)",
        .Idris2 => "Idris 2.x (ECHIDNA FFI)",
    };

    out_version.* = OwnedString.fromAllocated(allocator, version_str) catch {
        return .ErrorOutOfMemory;
    };

    return .Ok;
}

// ============================================================================
// Parsing Functions
// ============================================================================

/// Parse a proof file.
export fn echidna_parse_file(
    handle: ProverHandle,
    path: StringSlice,
    out_state: *ProofStateHandle,
) Status {
    _ = handle;
    _ = path;
    _ = out_state;
    // TODO: Implement file parsing via Rust callback
    return .ErrorNotImplemented;
}

/// Parse a proof string.
export fn echidna_parse_string(
    handle: ProverHandle,
    content: StringSlice,
    out_state: *ProofStateHandle,
) Status {
    _ = handle;
    _ = content;
    _ = out_state;
    // TODO: Implement string parsing via Rust callback
    return .ErrorNotImplemented;
}

// ============================================================================
// Tactic Application
// ============================================================================

/// Apply a tactic to a proof state.
export fn echidna_apply_tactic(
    handle: ProverHandle,
    state: ProofStateHandle,
    tactic: *const Tactic,
    out_result: *TacticResult,
) Status {
    _ = handle;
    _ = state;
    _ = tactic;
    _ = out_result;
    // TODO: Implement tactic application via Rust callback
    return .ErrorNotImplemented;
}

/// Get suggested tactics for current proof state.
export fn echidna_suggest_tactics(
    handle: ProverHandle,
    state: ProofStateHandle,
    limit: u32,
    out_tactics: [*]Tactic,
    out_count: *u32,
) Status {
    _ = handle;
    _ = state;
    _ = limit;
    _ = out_tactics;
    _ = out_count;
    // TODO: Implement tactic suggestion via Rust callback
    return .ErrorNotImplemented;
}

// ============================================================================
// Verification Functions
// ============================================================================

/// Verify a proof state.
export fn echidna_verify_proof(
    handle: ProverHandle,
    state: ProofStateHandle,
    out_valid: *bool,
) Status {
    _ = handle;
    _ = state;
    _ = out_valid;
    // TODO: Implement proof verification via Rust callback
    return .ErrorNotImplemented;
}

/// Export a proof to prover-specific format.
export fn echidna_export_proof(
    handle: ProverHandle,
    state: ProofStateHandle,
    out_content: *OwnedString,
) Status {
    _ = handle;
    _ = state;
    _ = out_content;
    // TODO: Implement proof export via Rust callback
    return .ErrorNotImplemented;
}

// ============================================================================
// Term Construction (for bulletproof-core integration)
// ============================================================================

/// Create a variable term.
export fn echidna_term_var(name: StringSlice, out_term: *TermHandle) Status {
    _ = name;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create a constant term.
export fn echidna_term_const(name: StringSlice, out_term: *TermHandle) Status {
    _ = name;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create an application term.
export fn echidna_term_app(
    func: TermHandle,
    args: [*]const TermHandle,
    args_len: usize,
    out_term: *TermHandle,
) Status {
    _ = func;
    _ = args;
    _ = args_len;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create a lambda term.
export fn echidna_term_lambda(
    param: StringSlice,
    param_type: ?TermHandle,
    body: TermHandle,
    out_term: *TermHandle,
) Status {
    _ = param;
    _ = param_type;
    _ = body;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create a Pi (dependent function) type.
export fn echidna_term_pi(
    param: StringSlice,
    param_type: TermHandle,
    body: TermHandle,
    out_term: *TermHandle,
) Status {
    _ = param;
    _ = param_type;
    _ = body;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create a Type universe term.
export fn echidna_term_type(level: u32, out_term: *TermHandle) Status {
    _ = level;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Create a hole (goal marker) term.
export fn echidna_term_hole(name: StringSlice, out_term: *TermHandle) Status {
    _ = name;
    _ = out_term;
    return .ErrorNotImplemented;
}

/// Free a term.
export fn echidna_term_free(term: TermHandle) Status {
    _ = term;
    return .ErrorNotImplemented;
}

// ============================================================================
// Proof State Queries
// ============================================================================

/// Get the number of goals in a proof state.
export fn echidna_state_goal_count(state: ProofStateHandle, out_count: *u32) Status {
    _ = state;
    _ = out_count;
    return .ErrorNotImplemented;
}

/// Get a goal from a proof state.
export fn echidna_state_get_goal(
    state: ProofStateHandle,
    index: u32,
    out_goal: *Goal,
) Status {
    _ = state;
    _ = index;
    _ = out_goal;
    return .ErrorNotImplemented;
}

/// Check if proof is complete.
export fn echidna_state_is_complete(state: ProofStateHandle, out_complete: *bool) Status {
    _ = state;
    _ = out_complete;
    return .ErrorNotImplemented;
}

/// Free a proof state.
export fn echidna_state_free(state: ProofStateHandle) Status {
    _ = state;
    return .ErrorNotImplemented;
}

// ============================================================================
// Memory Management
// ============================================================================

/// Free an owned string.
export fn echidna_string_free(str: *OwnedString) void {
    str.deinit(allocator);
}

/// Allocate memory (for external use).
export fn echidna_alloc(size: usize) ?[*]u8 {
    const buf = allocator.alloc(u8, size) catch return null;
    return buf.ptr;
}

/// Free allocated memory.
export fn echidna_free(ptr: [*]u8, size: usize) void {
    allocator.free(ptr[0..size]);
}

// ============================================================================
// Callback Registration (for Rust integration)
// ============================================================================

/// Callback function types for Rust integration
pub const ParseFileCallback = *const fn (ProverKind, StringSlice, *ProofStateHandle) callconv(.C) Status;
pub const ParseStringCallback = *const fn (ProverKind, StringSlice, *ProofStateHandle) callconv(.C) Status;
pub const ApplyTacticCallback = *const fn (ProverKind, ProofStateHandle, *const Tactic, *TacticResult) callconv(.C) Status;
pub const VerifyProofCallback = *const fn (ProverKind, ProofStateHandle, *bool) callconv(.C) Status;
pub const ExportProofCallback = *const fn (ProverKind, ProofStateHandle, *OwnedString) callconv(.C) Status;
pub const SuggestTacticsCallback = *const fn (ProverKind, ProofStateHandle, u32, [*]Tactic, *u32) callconv(.C) Status;

/// Registered callbacks (set by Rust side)
var callbacks: struct {
    parse_file: ?ParseFileCallback = null,
    parse_string: ?ParseStringCallback = null,
    apply_tactic: ?ApplyTacticCallback = null,
    verify_proof: ?VerifyProofCallback = null,
    export_proof: ?ExportProofCallback = null,
    suggest_tactics: ?SuggestTacticsCallback = null,
} = .{};

/// Register callbacks from Rust.
export fn echidna_register_callbacks(
    parse_file: ?ParseFileCallback,
    parse_string: ?ParseStringCallback,
    apply_tactic: ?ApplyTacticCallback,
    verify_proof: ?VerifyProofCallback,
    export_proof: ?ExportProofCallback,
    suggest_tactics: ?SuggestTacticsCallback,
) Status {
    callbacks.parse_file = parse_file;
    callbacks.parse_string = parse_string;
    callbacks.apply_tactic = apply_tactic;
    callbacks.verify_proof = verify_proof;
    callbacks.export_proof = export_proof;
    callbacks.suggest_tactics = suggest_tactics;
    return .Ok;
}

// ============================================================================
// Bulletproof-Core Integration Helpers
// ============================================================================

/// Proof obligation from bulletproof-core
pub const ProofObligation = extern struct {
    name: StringSlice,
    statement: SerializedTerm,
    context_len: u32,
    _padding: [4]u8 = [_]u8{0} ** 4,
};

/// Verification result for bulletproof-core
pub const VerificationResult = extern struct {
    valid: bool,
    _padding1: [3]u8 = [_]u8{0} ** 3,
    message_len: u32,
    message: [*]const u8,
    proof_term: ?TermHandle,

    pub fn getMessage(self: VerificationResult) []const u8 {
        return self.message[0..self.message_len];
    }
};

/// Submit a proof obligation from bulletproof-core for verification.
export fn echidna_bulletproof_verify(
    prover: ProverKind,
    obligation: *const ProofObligation,
    out_result: *VerificationResult,
) Status {
    _ = prover;
    _ = obligation;
    out_result.* = .{
        .valid = false,
        .message_len = 0,
        .message = undefined,
        .proof_term = null,
    };
    return .ErrorNotImplemented;
}

/// Request neural tactic suggestions for a bulletproof-core proof.
export fn echidna_bulletproof_suggest(
    prover: ProverKind,
    obligation: *const ProofObligation,
    limit: u32,
    out_tactics: [*]Tactic,
    out_count: *u32,
) Status {
    _ = prover;
    _ = obligation;
    _ = limit;
    _ = out_tactics;
    out_count.* = 0;
    return .ErrorNotImplemented;
}

// ============================================================================
// Tests
// ============================================================================

test "init and shutdown" {
    try std.testing.expectEqual(Status.Ok, echidna_init());
    try std.testing.expectEqual(Status.Ok, echidna_shutdown());
}

test "prover lifecycle" {
    _ = echidna_init();
    defer _ = echidna_shutdown();

    var handle: ProverHandle = undefined;
    const config = ProverConfig{
        .executable_path = StringSlice.empty(),
        .library_paths = undefined,
        .library_paths_len = 0,
        .timeout_ms = 30000,
        .neural_enabled = true,
    };

    try std.testing.expectEqual(Status.Ok, echidna_prover_create(.Idris2, &config, &handle));
    try std.testing.expectEqual(Status.Ok, echidna_prover_destroy(handle));
}

test "version query" {
    _ = echidna_init();
    defer _ = echidna_shutdown();

    var handle: ProverHandle = undefined;
    const config = ProverConfig{
        .executable_path = StringSlice.empty(),
        .library_paths = undefined,
        .library_paths_len = 0,
        .timeout_ms = 30000,
        .neural_enabled = true,
    };

    _ = echidna_prover_create(.Idris2, &config, &handle);
    defer _ = echidna_prover_destroy(handle);

    var version: OwnedString = undefined;
    try std.testing.expectEqual(Status.Ok, echidna_prover_version(handle, &version));
    defer echidna_string_free(&version);

    const version_str = version.ptr[0..version.len];
    try std.testing.expect(std.mem.startsWith(u8, version_str, "Idris 2"));
}
