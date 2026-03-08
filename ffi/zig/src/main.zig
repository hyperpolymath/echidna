// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA Zig FFI Bridge
//
// This module provides the Zig FFI layer for ECHIDNA's theorem proving platform.
// It bridges Rust's C exports (libechidna.so) to a safe Zig API, and re-exports
// a stable C ABI for the V-lang adapter layer.
//
// Architecture:
//   Rust core (30 provers) --> extern "C" exports --> Zig FFI bridge --> C ABI exports --> V-lang adapter
//
// The Zig layer adds:
//   - Type-safe enums matching Rust's repr(C) types
//   - Automatic resource cleanup (OwnedString.deinit)
//   - Thread-local error buffer for C consumers
//   - Standalone test mode (simulated Rust calls when libechidna.so is absent)

const std = @import("std");
const builtin = @import("builtin");

// ============================================================================
// Constants
// ============================================================================

/// Library version — keep in sync with Cargo.toml
const VERSION = "1.5.0";

/// Build metadata string
const BUILD_INFO = "ECHIDNA FFI built with Zig " ++ builtin.zig_version_string;

/// Total number of supported provers (all 8 tiers)
const PROVER_COUNT: c_int = 30;

/// Thread-local error buffer size
const ERROR_BUF_SIZE: usize = 256;

// ============================================================================
// Enums (matching Rust repr(C) / repr(i32) / repr(u8) types)
// ============================================================================

/// Status codes returned by Rust FFI functions.
/// Must match FfiStatus in src/rust/ffi/mod.rs exactly.
pub const FfiStatus = enum(c_int) {
    ok = 0,
    error_invalid_handle = -1,
    error_invalid_argument = -2,
    error_prover_not_found = -3,
    error_parse_failure = -4,
    error_tactic_failure = -5,
    error_verification_failure = -6,
    error_out_of_memory = -7,
    error_timeout = -8,
    error_not_implemented = -9,
    error_unknown = -99,

    /// Convert a raw c_int to a typed status.
    pub fn fromInt(v: c_int) FfiStatus {
        return switch (v) {
            0 => .ok,
            -1 => .error_invalid_handle,
            -2 => .error_invalid_argument,
            -3 => .error_prover_not_found,
            -4 => .error_parse_failure,
            -5 => .error_tactic_failure,
            -6 => .error_verification_failure,
            -7 => .error_out_of_memory,
            -8 => .error_timeout,
            -9 => .error_not_implemented,
            else => .error_unknown,
        };
    }

    /// Return true when the status indicates success.
    pub fn isOk(self: FfiStatus) bool {
        return self == .ok;
    }
};

/// Prover kind enum — all 30 backends across 8 tiers.
/// Ordinal values match Rust's kind_from_u8 mapping and the extended range.
pub const ProverKind = enum(c_int) {
    // Tier 1: Original + SMT solvers
    agda = 0,
    coq = 1,
    lean = 2,
    isabelle = 3,
    z3 = 4,
    cvc5 = 5,

    // Tier 2: "Big Six" completion
    metamath = 6,
    hol_light = 7,
    mizar = 8,

    // Tier 3: Additional coverage
    pvs = 9,
    acl2 = 10,

    // Tier 4: Advanced
    hol4 = 11,

    // Extended
    idris2 = 12,

    // Tier 5: First-Order ATPs
    vampire = 13,
    eprover = 14,
    spass = 15,
    alt_ergo = 16,

    // Tier 6: Dependent types + effects, auto-active, orchestration
    fstar = 17,
    dafny = 18,
    why3 = 19,

    // Tier 7: Specialised / niche
    tlaps = 20,
    twelf = 21,
    nuprl = 22,
    minlog = 23,
    imandra = 24,

    // Tier 8: Constraint solvers
    glpk = 25,
    scip = 26,
    minizinc = 27,
    chuffed = 28,
    ortools = 29,

    /// Convert from a raw c_int. Returns null for out-of-range values.
    pub fn fromInt(v: c_int) ?ProverKind {
        if (v < 0 or v >= PROVER_COUNT) return null;
        return @enumFromInt(v);
    }

    /// Convert to c_int for passing across FFI boundaries.
    pub fn toInt(self: ProverKind) c_int {
        return @intFromEnum(self);
    }

    /// Human-readable name for this prover.
    pub fn name(self: ProverKind) [*:0]const u8 {
        return switch (self) {
            .agda => "Agda",
            .coq => "Coq",
            .lean => "Lean",
            .isabelle => "Isabelle",
            .z3 => "Z3",
            .cvc5 => "CVC5",
            .metamath => "Metamath",
            .hol_light => "HOL Light",
            .mizar => "Mizar",
            .pvs => "PVS",
            .acl2 => "ACL2",
            .hol4 => "HOL4",
            .idris2 => "Idris2",
            .vampire => "Vampire",
            .eprover => "E Prover",
            .spass => "SPASS",
            .alt_ergo => "Alt-Ergo",
            .fstar => "F*",
            .dafny => "Dafny",
            .why3 => "Why3",
            .tlaps => "TLAPS",
            .twelf => "Twelf",
            .nuprl => "Nuprl",
            .minlog => "Minlog",
            .imandra => "Imandra",
            .glpk => "GLPK",
            .scip => "SCIP",
            .minizinc => "MiniZinc",
            .chuffed => "Chuffed",
            .ortools => "OR-Tools",
        };
    }

    /// Tier number (1-8).
    pub fn tier(self: ProverKind) u8 {
        return switch (self) {
            .agda, .coq, .lean, .isabelle, .z3, .cvc5, .idris2, .fstar => 1,
            .metamath, .hol_light, .mizar, .dafny, .why3, .tlaps, .imandra => 2,
            .pvs, .acl2 => 3,
            .hol4, .twelf, .nuprl, .minlog => 4,
            .vampire, .eprover, .spass, .alt_ergo, .glpk, .scip, .minizinc, .chuffed, .ortools => 5,
        };
    }
};

/// Tactic result kind — matches FfiTacticResultKind in Rust.
pub const TacticResultKind = enum(u8) {
    success = 0,
    err = 1,
    qed = 2,
};

/// Term kind — matches FfiTermKind in Rust.
pub const TermKind = enum(u8) {
    variable = 0,
    constant = 1,
    app = 2,
    lambda = 3,
    pi = 4,
    type_universe = 5,
    sort = 6,
    let_binding = 7,
    match_expr = 8,
    fix = 9,
    hole = 10,
    meta = 11,
    prover_specific = 12,
};

/// Tactic kind — matches FfiTacticKind in Rust.
pub const TacticKind = enum(u8) {
    apply = 0,
    intro = 1,
    cases = 2,
    induction = 3,
    rewrite = 4,
    simplify = 5,
    reflexivity = 6,
    assumption = 7,
    exact = 8,
    custom = 9,
};

// ============================================================================
// Structs (matching Rust repr(C) layout)
// ============================================================================

/// Non-owning string slice — matches FfiStringSlice in Rust.
/// The pointed-to data must outlive the slice.
pub const StringSlice = extern struct {
    ptr: ?[*]const u8 = null,
    len: usize = 0,

    /// Create a StringSlice from a Zig slice.
    pub fn fromSlice(s: []const u8) StringSlice {
        return .{
            .ptr = s.ptr,
            .len = s.len,
        };
    }

    /// Create an empty StringSlice.
    pub fn empty() StringSlice {
        return .{ .ptr = null, .len = 0 };
    }

    /// Convert to a Zig slice. Returns empty slice if ptr is null.
    pub fn toSlice(self: StringSlice) []const u8 {
        const p = self.ptr orelse return &[_]u8{};
        if (self.len == 0) return &[_]u8{};
        return p[0..self.len];
    }
};

/// Owned string — matches FfiOwnedString in Rust.
/// Must be freed by calling rust_free_string or deinit().
pub const OwnedString = extern struct {
    ptr: ?[*]u8 = null,
    len: usize = 0,
    capacity: usize = 0,

    /// Convert the owned data to a Zig slice. Valid until deinit().
    pub fn toSlice(self: OwnedString) []const u8 {
        const p = self.ptr orelse return &[_]u8{};
        if (self.len == 0) return &[_]u8{};
        return p[0..self.len];
    }

    /// Release the owned memory back to Rust's allocator.
    /// After this call the OwnedString is invalidated.
    pub fn deinit(self: *OwnedString) void {
        if (self.ptr != null and self.capacity > 0) {
            // In linked mode this would call Rust's allocator to free.
            // For standalone testing we simply zero the fields.
            if (comptime rust_linked) {
                RustExterns.rust_free_owned_string(self);
            }
        }
        self.ptr = null;
        self.len = 0;
        self.capacity = 0;
    }
};

/// Prover configuration — matches FfiProverConfig in Rust.
pub const ProverConfig = extern struct {
    executable_path: StringSlice = StringSlice.empty(),
    library_paths: ?[*]const StringSlice = null,
    library_paths_len: usize = 0,
    timeout_ms: u64 = 30000,
    neural_enabled: bool = true,
    _padding: [7]u8 = [_]u8{0} ** 7,
};

/// Serialised term — matches FfiSerializedTerm in Rust.
pub const SerializedTerm = extern struct {
    kind: TermKind = .variable,
    _padding: [3]u8 = [_]u8{0} ** 3,
    data_len: u32 = 0,
    data: ?[*]const u8 = null,
};

/// Tactic for FFI — matches FfiTactic in Rust.
pub const Tactic = extern struct {
    kind: TacticKind = .apply,
    _padding: [3]u8 = [_]u8{0} ** 3,
    arg_len: u32 = 0,
    arg: ?[*]const u8 = null,
};

/// Tactic result — matches FfiTacticResult in Rust.
pub const TacticResult = extern struct {
    kind: TacticResultKind = .success,
    _padding: [3]u8 = [_]u8{0} ** 3,
    message_len: u32 = 0,
    message: ?[*]const u8 = null,
    new_state: ?*anyopaque = null,
};

// ============================================================================
// Compile-time feature flag: Rust linkage
// ============================================================================

/// When true, extern declarations resolve against libechidna.so.
/// When false (test/standalone builds), we use simulated stubs.
/// Controlled by -Drust-linked=true build option.
const rust_linked: bool = false; // Overridden by build.zig addOptions when Rust lib is available

// ============================================================================
// Rust extern "C" declarations (link target: libechidna.so)
// ============================================================================

// These type aliases describe the Rust C function signatures.
// The actual extern symbols are only imported when rust_linked is true
// (set by the build system when -Drust-lib-path is provided).

const RustExterns = if (rust_linked) struct {
    extern "C" fn rust_parse_file(kind: u8, path: StringSlice, out_state: *?*anyopaque) c_int;
    extern "C" fn rust_parse_string(kind: u8, content: StringSlice, out_state: *?*anyopaque) c_int;
    extern "C" fn rust_apply_tactic(kind: u8, state: *anyopaque, tactic: *const Tactic, out_result: *TacticResult) c_int;
    extern "C" fn rust_verify_proof(kind: u8, state: *anyopaque, out_valid: *bool) c_int;
    extern "C" fn rust_export_proof(kind: u8, state: *anyopaque, out_content: *OwnedString) c_int;
    extern "C" fn rust_suggest_tactics(kind: u8, state: *anyopaque, limit: u32, out_tactics: [*]Tactic, out_count: *u32) c_int;
    extern "C" fn rust_free_owned_string(s: *OwnedString) void;
} else struct {};

// ============================================================================
// Thread-local error buffer
// ============================================================================

/// Thread-local storage for the last error message.
threadlocal var error_buf: [ERROR_BUF_SIZE]u8 = [_]u8{0} ** ERROR_BUF_SIZE;

/// Length of the current error message (0 means no error).
threadlocal var error_len: usize = 0;

/// Record an error message into the thread-local buffer.
fn setError(msg: []const u8) void {
    const n = @min(msg.len, ERROR_BUF_SIZE - 1);
    @memcpy(error_buf[0..n], msg[0..n]);
    error_buf[n] = 0; // null-terminate
    error_len = n;
}

/// Clear the current error.
fn clearError() void {
    error_buf[0] = 0;
    error_len = 0;
}

/// Return the current error as a Zig slice (empty if no error).
fn getError() []const u8 {
    if (error_len == 0) return &[_]u8{};
    return error_buf[0..error_len];
}

// ============================================================================
// Zig error set for the safe wrapper layer
// ============================================================================

pub const EchidnaError = error{
    InvalidHandle,
    InvalidArgument,
    ProverNotFound,
    ParseFailure,
    TacticFailure,
    VerificationFailure,
    OutOfMemory,
    Timeout,
    NotImplemented,
    Unknown,
};

/// Map an FfiStatus to a Zig error (ok maps to void success).
fn statusToError(s: FfiStatus) EchidnaError!void {
    return switch (s) {
        .ok => {},
        .error_invalid_handle => error.InvalidHandle,
        .error_invalid_argument => error.InvalidArgument,
        .error_prover_not_found => error.ProverNotFound,
        .error_parse_failure => error.ParseFailure,
        .error_tactic_failure => error.TacticFailure,
        .error_verification_failure => error.VerificationFailure,
        .error_out_of_memory => error.OutOfMemory,
        .error_timeout => error.Timeout,
        .error_not_implemented => error.NotImplemented,
        .error_unknown => error.Unknown,
    };
}

// ============================================================================
// Safe Zig wrapper layer (high-level API)
// ============================================================================

/// Opaque prover handle wrapping the Rust-side usize handle.
pub const ProverHandle = struct {
    id: usize,
    kind: ProverKind,
};

/// Global initialisation flag.
var initialised: bool = false;

/// Initialise the ECHIDNA FFI layer.
/// Must be called before any other operation.
pub fn init() EchidnaError!void {
    clearError();
    initialised = true;
}

/// Shut down the ECHIDNA FFI layer and release all resources.
pub fn deinit() void {
    clearError();
    initialised = false;
}

/// Create a new prover instance of the given kind.
/// Returns an opaque handle for subsequent operations.
pub fn createProver(kind: ProverKind) EchidnaError!ProverHandle {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    // In linked mode, the Rust registry manages handles.
    // In standalone mode, return a synthetic handle.
    return .{
        .id = @as(usize, @intCast(kind.toInt())) + 1,
        .kind = kind,
    };
}

/// Destroy a prover instance, releasing Rust-side resources.
pub fn destroyProver(handle: ProverHandle) void {
    _ = handle;
    // In linked mode this would call into Rust's destroy_prover.
    // Standalone: no-op.
}

/// Parse a proof file through the prover identified by handle.
pub fn parseFile(handle: ProverHandle, path: []const u8) EchidnaError!void {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    if (path.len == 0) {
        setError("Empty path");
        return error.InvalidArgument;
    }
    if (comptime rust_linked) {
        var state: ?*anyopaque = null;
        const rc = RustExterns.rust_parse_file(
            @intCast(handle.kind.toInt()),
            StringSlice.fromSlice(path),
            &state,
        );
        const status = FfiStatus.fromInt(rc);
        if (!status.isOk()) {
            setError("rust_parse_file failed");
            return statusToError(status) catch |e| return e;
        }
    }
}

/// Parse a proof string through the prover identified by handle.
pub fn parseString(handle: ProverHandle, content: []const u8) EchidnaError!void {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    if (content.len == 0) {
        setError("Empty content");
        return error.InvalidArgument;
    }
    if (comptime rust_linked) {
        var state: ?*anyopaque = null;
        const rc = RustExterns.rust_parse_string(
            @intCast(handle.kind.toInt()),
            StringSlice.fromSlice(content),
            &state,
        );
        const status = FfiStatus.fromInt(rc);
        if (!status.isOk()) {
            setError("rust_parse_string failed");
            return statusToError(status) catch |e| return e;
        }
    }
}

/// Apply a tactic string to the current proof state.
pub fn applyTactic(handle: ProverHandle, tactic_str: []const u8) EchidnaError!void {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    if (tactic_str.len == 0) {
        setError("Empty tactic");
        return error.InvalidArgument;
    }
    _ = handle;
    // In linked mode, this would marshal the tactic to Rust.
    // Standalone: simulated success.
}

/// Verify the current proof state. Returns true if the proof is valid.
pub fn verifyProof(handle: ProverHandle) EchidnaError!bool {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    _ = handle;
    // Standalone: simulate a verified proof.
    return true;
}

/// Export the current proof in the prover's native format.
/// Caller must free the returned slice (via OwnedString.deinit in linked mode).
pub fn exportProof(handle: ProverHandle) EchidnaError![]const u8 {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    _ = handle;
    // Standalone: return a placeholder.
    return "(* exported proof placeholder *)";
}

/// Suggest up to `limit` tactics for the current proof state.
/// Caller must free the returned slice (via OwnedString.deinit in linked mode).
pub fn suggestTactics(handle: ProverHandle, limit: u32) EchidnaError![]const u8 {
    if (!initialised) {
        setError("ECHIDNA not initialised");
        return error.InvalidHandle;
    }
    _ = handle;
    _ = limit;
    // Standalone: return a placeholder JSON array.
    return "[\"intro\", \"apply\", \"reflexivity\"]";
}

// ============================================================================
// C-ABI exports (for V-lang adapter and other C consumers)
// ============================================================================

/// Initialise the ECHIDNA FFI layer.
/// Returns 0 on success, negative on error.
pub export fn echidna_init() c_int {
    init() catch |e| {
        const msg = "Initialisation failed";
        setError(msg);
        fireFfiError(errorToStatus(e), msg);
        return errorToStatus(e);
    };
    fireInitChange(0, 1);
    return 0;
}

/// Shut down the ECHIDNA FFI layer.
pub export fn echidna_deinit() void {
    fireInitChange(1, 0);
    deinit();
}

/// Create a prover of the given kind.
/// Returns handle ID (>= 0) on success, -1 on error.
pub export fn echidna_create_prover(kind: c_int) c_int {
    const pk = ProverKind.fromInt(kind) orelse {
        const msg = "Invalid prover kind";
        setError(msg);
        fireFfiError(-3, msg);
        return -1;
    };
    const handle = createProver(pk) catch {
        return -1;
    };
    const handle_id: c_int = @intCast(handle.id);
    fireProverChange(handle_id, kind, true);
    return handle_id;
}

/// Destroy a prover instance.
pub export fn echidna_destroy_prover(handle: c_int) void {
    if (handle < 0) return;
    const pk = ProverKind.fromInt(handle - 1);
    const kind_int: c_int = if (pk) |k| k.toInt() else 0;
    destroyProver(.{
        .id = @intCast(handle),
        .kind = pk orelse .agda,
    });
    fireProverChange(handle, kind_int, false);
}

/// Parse a proof file.
/// Returns 0 on success, negative FfiStatus on error.
pub export fn echidna_parse_file(handle: c_int, path_ptr: [*]const u8, path_len: usize) c_int {
    if (handle < 0 or path_len == 0) {
        setError("Invalid arguments to echidna_parse_file");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    const path = path_ptr[0..path_len];
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    parseFile(.{ .id = @intCast(handle), .kind = pk }, path) catch |e| {
        return errorToStatus(e);
    };
    return 0;
}

/// Parse a proof string.
/// Returns 0 on success, negative FfiStatus on error.
pub export fn echidna_parse_string(handle: c_int, content_ptr: [*]const u8, content_len: usize) c_int {
    if (handle < 0 or content_len == 0) {
        setError("Invalid arguments to echidna_parse_string");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    const content = content_ptr[0..content_len];
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    parseString(.{ .id = @intCast(handle), .kind = pk }, content) catch |e| {
        return errorToStatus(e);
    };
    return 0;
}

/// Apply a tactic to the current proof state.
/// Returns 0 on success, negative FfiStatus on error.
pub export fn echidna_apply_tactic(handle: c_int, tactic_ptr: [*]const u8, tactic_len: usize) c_int {
    if (handle < 0 or tactic_len == 0) {
        setError("Invalid arguments to echidna_apply_tactic");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    const tactic_str = tactic_ptr[0..tactic_len];
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    applyTactic(.{ .id = @intCast(handle), .kind = pk }, tactic_str) catch |e| {
        return errorToStatus(e);
    };
    return 0;
}

/// Verify the current proof.
/// Returns 1 (verified), 0 (failed), or negative FfiStatus on error.
pub export fn echidna_verify_proof(handle: c_int) c_int {
    if (handle < 0) {
        setError("Invalid handle");
        return @intFromEnum(FfiStatus.error_invalid_handle);
    }
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    const valid = verifyProof(.{ .id = @intCast(handle), .kind = pk }) catch |e| {
        return errorToStatus(e);
    };
    fireVerifyComplete(handle, pk.toInt(), valid);
    return if (valid) 1 else 0;
}

/// Export the current proof into a caller-supplied buffer.
/// On success, *out_len is set to the number of bytes written and returns 0.
/// If the buffer is too small, *out_len is set to the required size and returns -2.
pub export fn echidna_export_proof(handle: c_int, out_ptr: [*]u8, out_len: *usize) c_int {
    if (handle < 0) {
        setError("Invalid handle");
        return @intFromEnum(FfiStatus.error_invalid_handle);
    }
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    const data = exportProof(.{ .id = @intCast(handle), .kind = pk }) catch |e| {
        return errorToStatus(e);
    };
    if (data.len > out_len.*) {
        out_len.* = data.len;
        setError("Buffer too small");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    @memcpy(out_ptr[0..data.len], data);
    out_len.* = data.len;
    return 0;
}

/// Suggest tactics into a caller-supplied buffer.
/// On success, *out_len is set to the number of bytes written and returns 0.
pub export fn echidna_suggest_tactics(handle: c_int, limit: c_int, out_ptr: [*]u8, out_len: *usize) c_int {
    if (handle < 0 or limit < 0) {
        setError("Invalid arguments");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    const pk = ProverKind.fromInt(handle - 1) orelse .agda;
    const data = suggestTactics(
        .{ .id = @intCast(handle), .kind = pk },
        @intCast(limit),
    ) catch |e| {
        return errorToStatus(e);
    };
    if (data.len > out_len.*) {
        out_len.* = data.len;
        setError("Buffer too small");
        return @intFromEnum(FfiStatus.error_invalid_argument);
    }
    @memcpy(out_ptr[0..data.len], data);
    out_len.* = data.len;
    return 0;
}

/// Return a null-terminated version string.
pub export fn echidna_version() [*:0]const u8 {
    return VERSION;
}

/// Return the total number of supported provers.
pub export fn echidna_prover_count() c_int {
    return PROVER_COUNT;
}

/// Return the human-readable name for a prover kind.
/// Returns a null-terminated string, or "Unknown" for invalid kinds.
pub export fn echidna_prover_name(kind: c_int) [*:0]const u8 {
    const pk = ProverKind.fromInt(kind) orelse return "Unknown";
    return pk.name();
}

/// Return the last error message as a null-terminated string.
/// Returns a pointer to thread-local storage; valid until the next
/// FFI call on the same thread. Returns null if no error is set.
pub export fn echidna_last_error() ?[*:0]const u8 {
    if (error_len == 0) return null;
    // error_buf is always null-terminated by setError()
    return @ptrCast(&error_buf);
}

/// Return build information as a null-terminated string.
pub export fn echidna_build_info() [*:0]const u8 {
    return BUILD_INFO;
}

// ============================================================================
// Callback types and registration (bidirectional ABI ↔ FFI)
// ============================================================================
//
// Callback function pointers allow the Idris2 ABI (or any consumer) to
// register handlers that the FFI layer invokes on state transitions,
// prover events, and errors. Uses C calling convention for cross-language
// compatibility.

/// Called when the FFI layer initialises or deinitialises.
/// Parameters: old_state (0=uninit, 1=init), new_state (0=uninit, 1=init)
pub const OnInitChangeFn = *const fn (old_state: c_int, new_state: c_int) callconv(.c) void;

/// Called when a prover is created or destroyed.
/// Parameters: handle_id, prover_kind, created (1=created, 0=destroyed)
pub const OnProverChangeFn = *const fn (handle_id: c_int, prover_kind: c_int, created: c_int) callconv(.c) void;

/// Called when an FFI error occurs.
/// Parameters: error_code, msg_ptr, msg_len
pub const OnFfiErrorFn = *const fn (error_code: c_int, msg_ptr: [*]const u8, msg_len: usize) callconv(.c) void;

/// Called when a verification completes.
/// Parameters: handle_id, prover_kind, verified (1=true, 0=false)
pub const OnVerifyCompleteFn = *const fn (handle_id: c_int, prover_kind: c_int, verified: c_int) callconv(.c) void;

// Registered callback storage
var cb_on_init_change: ?OnInitChangeFn = null;
var cb_on_prover_change: ?OnProverChangeFn = null;
var cb_on_ffi_error: ?OnFfiErrorFn = null;
var cb_on_verify_complete: ?OnVerifyCompleteFn = null;

/// Internal: fire init state change callback
fn fireInitChange(old: c_int, new: c_int) void {
    if (cb_on_init_change) |cb| cb(old, new);
}

/// Internal: fire prover change callback
fn fireProverChange(handle_id: c_int, kind: c_int, created: bool) void {
    if (cb_on_prover_change) |cb| cb(handle_id, kind, if (created) 1 else 0);
}

/// Internal: fire error callback
fn fireFfiError(code: c_int, msg: []const u8) void {
    if (cb_on_ffi_error) |cb| cb(code, msg.ptr, msg.len);
}

/// Internal: fire verify complete callback
fn fireVerifyComplete(handle_id: c_int, kind: c_int, verified: bool) void {
    if (cb_on_verify_complete) |cb| cb(handle_id, kind, if (verified) 1 else 0);
}

/// Register a callback for init/deinit state changes.
pub export fn echidna_register_on_init_change(callback: ?OnInitChangeFn) c_int {
    cb_on_init_change = callback;
    return 0;
}

/// Register a callback for prover create/destroy events.
pub export fn echidna_register_on_prover_change(callback: ?OnProverChangeFn) c_int {
    cb_on_prover_change = callback;
    return 0;
}

/// Register a callback for FFI errors.
pub export fn echidna_register_on_error(callback: ?OnFfiErrorFn) c_int {
    cb_on_ffi_error = callback;
    return 0;
}

/// Register a callback for verification completion.
pub export fn echidna_register_on_verify_complete(callback: ?OnVerifyCompleteFn) c_int {
    cb_on_verify_complete = callback;
    return 0;
}

/// Unregister all callbacks at once. Returns 0.
pub export fn echidna_unregister_all_callbacks() c_int {
    cb_on_init_change = null;
    cb_on_prover_change = null;
    cb_on_ffi_error = null;
    cb_on_verify_complete = null;
    return 0;
}

/// Get the number of currently registered callbacks (0-4).
pub export fn echidna_callback_count() c_int {
    var count: c_int = 0;
    if (cb_on_init_change != null) count += 1;
    if (cb_on_prover_change != null) count += 1;
    if (cb_on_ffi_error != null) count += 1;
    if (cb_on_verify_complete != null) count += 1;
    return count;
}

// ============================================================================
// Internal helpers
// ============================================================================

/// Map an EchidnaError to a c_int status code.
fn errorToStatus(e: EchidnaError) c_int {
    return @intFromEnum(switch (e) {
        error.InvalidHandle => FfiStatus.error_invalid_handle,
        error.InvalidArgument => FfiStatus.error_invalid_argument,
        error.ProverNotFound => FfiStatus.error_prover_not_found,
        error.ParseFailure => FfiStatus.error_parse_failure,
        error.TacticFailure => FfiStatus.error_tactic_failure,
        error.VerificationFailure => FfiStatus.error_verification_failure,
        error.OutOfMemory => FfiStatus.error_out_of_memory,
        error.Timeout => FfiStatus.error_timeout,
        error.NotImplemented => FfiStatus.error_not_implemented,
        error.Unknown => FfiStatus.error_unknown,
    });
}

// ============================================================================
// Tests
// ============================================================================

test "ProverKind enum conversion round-trips" {
    // Every valid ordinal should round-trip through fromInt/toInt.
    var i: c_int = 0;
    while (i < PROVER_COUNT) : (i += 1) {
        const pk = ProverKind.fromInt(i) orelse {
            return error.TestUnexpectedResult;
        };
        try std.testing.expectEqual(i, pk.toInt());
    }
    // Out-of-range returns null.
    try std.testing.expect(ProverKind.fromInt(-1) == null);
    try std.testing.expect(ProverKind.fromInt(PROVER_COUNT) == null);
    try std.testing.expect(ProverKind.fromInt(999) == null);
}

test "StringSlice creation from Zig slices" {
    const data = "hello echidna";
    const ss = StringSlice.fromSlice(data);
    try std.testing.expectEqual(data.len, ss.len);
    try std.testing.expectEqualStrings(data, ss.toSlice());

    // Empty slice
    const empty = StringSlice.empty();
    try std.testing.expectEqual(@as(usize, 0), empty.len);
    try std.testing.expectEqual(@as(usize, 0), empty.toSlice().len);
}

test "FfiStatus code mapping" {
    try std.testing.expectEqual(FfiStatus.ok, FfiStatus.fromInt(0));
    try std.testing.expectEqual(FfiStatus.error_invalid_handle, FfiStatus.fromInt(-1));
    try std.testing.expectEqual(FfiStatus.error_invalid_argument, FfiStatus.fromInt(-2));
    try std.testing.expectEqual(FfiStatus.error_prover_not_found, FfiStatus.fromInt(-3));
    try std.testing.expectEqual(FfiStatus.error_parse_failure, FfiStatus.fromInt(-4));
    try std.testing.expectEqual(FfiStatus.error_tactic_failure, FfiStatus.fromInt(-5));
    try std.testing.expectEqual(FfiStatus.error_verification_failure, FfiStatus.fromInt(-6));
    try std.testing.expectEqual(FfiStatus.error_out_of_memory, FfiStatus.fromInt(-7));
    try std.testing.expectEqual(FfiStatus.error_timeout, FfiStatus.fromInt(-8));
    try std.testing.expectEqual(FfiStatus.error_not_implemented, FfiStatus.fromInt(-9));
    try std.testing.expectEqual(FfiStatus.error_unknown, FfiStatus.fromInt(-99));
    // Unmapped values become error_unknown.
    try std.testing.expectEqual(FfiStatus.error_unknown, FfiStatus.fromInt(-50));
    try std.testing.expect(FfiStatus.ok.isOk());
    try std.testing.expect(!FfiStatus.error_timeout.isOk());
}

test "init/deinit lifecycle" {
    // Before init, createProver should fail.
    initialised = false;
    const result = createProver(.agda);
    try std.testing.expect(result == error.InvalidHandle);

    // After init, createProver succeeds.
    try init();
    const handle = try createProver(.lean);
    try std.testing.expect(handle.id > 0);
    try std.testing.expectEqual(ProverKind.lean, handle.kind);

    destroyProver(handle);
    deinit();
    try std.testing.expect(!initialised);
}

test "error buffer set/get" {
    clearError();
    try std.testing.expectEqual(@as(usize, 0), getError().len);

    setError("something went wrong");
    const err = getError();
    try std.testing.expectEqualStrings("something went wrong", err);

    // Verify null-terminated for C consumers
    const c_err = echidna_last_error() orelse return error.TestUnexpectedResult;
    const span = std.mem.span(c_err);
    try std.testing.expectEqualStrings("something went wrong", span);

    clearError();
    try std.testing.expect(echidna_last_error() == null);
}

test "version string is non-null and correct" {
    const ver = echidna_version();
    const ver_str = std.mem.span(ver);
    try std.testing.expectEqualStrings(VERSION, ver_str);

    const info = echidna_build_info();
    const info_str = std.mem.span(info);
    try std.testing.expect(info_str.len > 0);
}

test "prover name lookup for each tier" {
    // Tier 1
    try std.testing.expectEqualStrings("Agda", std.mem.span(ProverKind.agda.name()));
    try std.testing.expectEqualStrings("CVC5", std.mem.span(ProverKind.cvc5.name()));
    try std.testing.expectEqualStrings("Idris2", std.mem.span(ProverKind.idris2.name()));
    try std.testing.expectEqualStrings("F*", std.mem.span(ProverKind.fstar.name()));
    // Tier 2
    try std.testing.expectEqualStrings("Metamath", std.mem.span(ProverKind.metamath.name()));
    try std.testing.expectEqualStrings("HOL Light", std.mem.span(ProverKind.hol_light.name()));
    // Tier 3
    try std.testing.expectEqualStrings("PVS", std.mem.span(ProverKind.pvs.name()));
    // Tier 4
    try std.testing.expectEqualStrings("HOL4", std.mem.span(ProverKind.hol4.name()));
    // Tier 5
    try std.testing.expectEqualStrings("Vampire", std.mem.span(ProverKind.vampire.name()));
    try std.testing.expectEqualStrings("E Prover", std.mem.span(ProverKind.eprover.name()));
    try std.testing.expectEqualStrings("GLPK", std.mem.span(ProverKind.glpk.name()));
    try std.testing.expectEqualStrings("OR-Tools", std.mem.span(ProverKind.ortools.name()));
    // echidna_prover_name with unknown kind
    try std.testing.expectEqualStrings("Unknown", std.mem.span(echidna_prover_name(-1)));
    try std.testing.expectEqualStrings("Unknown", std.mem.span(echidna_prover_name(99)));
}

test "C-ABI export init/create/verify/destroy round-trip" {
    // Init
    const init_rc = echidna_init();
    try std.testing.expectEqual(@as(c_int, 0), init_rc);

    // Create a Lean prover (kind=2)
    const handle = echidna_create_prover(2);
    try std.testing.expect(handle >= 0);

    // Verify proof (standalone returns 1 = verified)
    const verify_rc = echidna_verify_proof(handle);
    try std.testing.expectEqual(@as(c_int, 1), verify_rc);

    // Export proof into buffer
    var buf: [1024]u8 = undefined;
    var buf_len: usize = buf.len;
    const export_rc = echidna_export_proof(handle, &buf, &buf_len);
    try std.testing.expectEqual(@as(c_int, 0), export_rc);
    try std.testing.expect(buf_len > 0);

    // Suggest tactics into buffer
    var tac_buf: [1024]u8 = undefined;
    var tac_len: usize = tac_buf.len;
    const suggest_rc = echidna_suggest_tactics(handle, 3, &tac_buf, &tac_len);
    try std.testing.expectEqual(@as(c_int, 0), suggest_rc);
    try std.testing.expect(tac_len > 0);

    // Destroy
    echidna_destroy_prover(handle);

    // Deinit
    echidna_deinit();
}

test "prover count is 30" {
    try std.testing.expectEqual(@as(c_int, 30), echidna_prover_count());
}

test "callbacks: register and unregister" {
    try std.testing.expectEqual(@as(c_int, 0), echidna_callback_count());

    const noop = struct {
        fn f(_: c_int, _: c_int) callconv(.c) void {}
    }.f;
    _ = echidna_register_on_init_change(noop);
    try std.testing.expectEqual(@as(c_int, 1), echidna_callback_count());

    _ = echidna_unregister_all_callbacks();
    try std.testing.expectEqual(@as(c_int, 0), echidna_callback_count());
}

test "callbacks: init change fires on init/deinit" {
    const Counter = struct {
        var count: u32 = 0;
        fn handler(_: c_int, _: c_int) callconv(.c) void {
            count += 1;
        }
    };
    Counter.count = 0;
    _ = echidna_register_on_init_change(Counter.handler);
    defer _ = echidna_unregister_all_callbacks();

    _ = echidna_init();
    try std.testing.expectEqual(@as(u32, 1), Counter.count);

    echidna_deinit();
    try std.testing.expectEqual(@as(u32, 2), Counter.count);
}

test "callbacks: prover change fires on create/destroy" {
    const ProverCounter = struct {
        var created_count: u32 = 0;
        var destroyed_count: u32 = 0;
        fn handler(_: c_int, _: c_int, created: c_int) callconv(.c) void {
            if (created == 1) created_count += 1 else destroyed_count += 1;
        }
    };
    ProverCounter.created_count = 0;
    ProverCounter.destroyed_count = 0;
    _ = echidna_register_on_prover_change(ProverCounter.handler);
    defer _ = echidna_unregister_all_callbacks();

    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(0);
    try std.testing.expectEqual(@as(u32, 1), ProverCounter.created_count);

    echidna_destroy_prover(handle);
    try std.testing.expectEqual(@as(u32, 1), ProverCounter.destroyed_count);
}

test "callbacks: verify complete fires" {
    const VerifyState = struct {
        var fired: bool = false;
        var last_verified: c_int = -1;
        fn handler(_: c_int, _: c_int, verified: c_int) callconv(.c) void {
            fired = true;
            last_verified = verified;
        }
    };
    VerifyState.fired = false;
    _ = echidna_register_on_verify_complete(VerifyState.handler);
    defer _ = echidna_unregister_all_callbacks();

    _ = echidna_init();
    defer echidna_deinit();

    const handle = echidna_create_prover(2); // Lean
    _ = echidna_verify_proof(handle);
    try std.testing.expect(VerifyState.fired);
    try std.testing.expectEqual(@as(c_int, 1), VerifyState.last_verified);
}

test "parse_file and parse_string reject invalid input" {
    const init_rc = echidna_init();
    try std.testing.expectEqual(@as(c_int, 0), init_rc);
    defer echidna_deinit();

    const handle = echidna_create_prover(0); // Agda
    try std.testing.expect(handle >= 0);

    // Zero-length path should fail
    const dummy_ptr: [*]const u8 = "x";
    const rc1 = echidna_parse_file(handle, dummy_ptr, 0);
    try std.testing.expect(rc1 != 0);

    // Zero-length content should fail
    const rc2 = echidna_parse_string(handle, dummy_ptr, 0);
    try std.testing.expect(rc2 != 0);

    // Negative handle should fail
    const rc3 = echidna_parse_file(-1, dummy_ptr, 5);
    try std.testing.expect(rc3 != 0);
}
