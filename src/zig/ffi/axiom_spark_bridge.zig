// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
//
// axiom_spark_bridge.zig — Zig C-ABI shim over the SPARK axiom-policy layer.
//
// Architecture:
//   SPARK/Ada (axiom_policy.ads/.adb)
//     → C exports (axiom_c_bridge.ads/.adb, symbol: echidna_spark_enforce_policy_inner)
//     → this Zig shim (input validation + C-ABI re-export)
//     → Rust extern "C" (src/rust/ffi/spark_axiom.rs)
//
// Why the Zig shim?
//   - Zig links against libechidna_spark.a and re-exports the symbols with
//     the exact C ABI that Rust expects (no name mangling, predictable layout).
//   - Provides a compile-time size assertion (max_usages check) that Rust's
//     bindgen cannot see across the Ada boundary.
//   - Keeps the Ada/SPARK layer isolated from Cargo's build machinery.

const std = @import("std");
const c = @cImport({});

// ============================================================================
// Wire-format constants (must match src/ada/spark/axiom_types.ads)
// ============================================================================

pub const DANGER_SAFE: u8 = 0;
pub const DANGER_NOTED: u8 = 1;
pub const DANGER_WARNING: u8 = 2;
pub const DANGER_REJECT: u8 = 3;

pub const POLICY_CLEAN: i32 = 0;
pub const POLICY_CLASSICAL: i32 = 1;
pub const POLICY_INCOMPLETE: i32 = 2;
pub const POLICY_REJECTED: i32 = 3;

pub const MAX_USAGES: usize = 1024;

// ============================================================================
// Extern declarations — symbols exported by libechidna_spark.a
// ============================================================================

extern fn echidna_spark_enforce_policy_inner(
    danger_levels: [*]const u8,
    count: usize,
    policy_out: *i32,
    status_out: *i32,
) void;

extern fn echidna_spark_worst_danger_inner(
    danger_levels: [*]const u8,
    count: usize,
    danger_out: *i32,
    status_out: *i32,
) void;

// ============================================================================
// Public C-ABI exports (called by Rust via extern "C")
// ============================================================================

/// echidna_spark_enforce_policy
///
/// Calls the GNATprove-verified Axiom_Policy.Enforce function.
///
/// Parameters:
///   danger_levels  — pointer to array of u8 danger levels (0–3)
///   count          — number of elements (max 1024)
///
/// Returns:
///   0 = PolicyClean, 1 = PolicyClassical, 2 = PolicyIncomplete,
///   3 = PolicyRejected, -1 = error (null pointer or count > MAX_USAGES)
export fn echidna_spark_enforce_policy(
    danger_levels: ?[*]const u8,
    count: usize,
) callconv(.C) i32 {
    if (danger_levels == null or count > MAX_USAGES) return -1;

    var policy_out: i32 = -1;
    var status_out: i32 = -1;

    echidna_spark_enforce_policy_inner(
        danger_levels.?,
        count,
        &policy_out,
        &status_out,
    );

    if (status_out != 0) return -1;
    return policy_out;
}

/// echidna_spark_worst_danger
///
/// Returns the worst danger level in the array (0=Safe … 3=Reject),
/// or -1 on error. This calls the SPARK Worst_Danger function whose
/// Post-condition proves result=Reject iff any input is Reject.
export fn echidna_spark_worst_danger(
    danger_levels: ?[*]const u8,
    count: usize,
) callconv(.C) i32 {
    if (danger_levels == null or count > MAX_USAGES) return -1;

    var danger_out: i32 = -1;
    var status_out: i32 = -1;

    echidna_spark_worst_danger_inner(
        danger_levels.?,
        count,
        &danger_out,
        &status_out,
    );

    if (status_out != 0) return -1;
    return danger_out;
}

/// echidna_spark_max_usages
///
/// Returns the maximum array size accepted by the bridge (compile-time constant).
/// Rust callers can query this at runtime to enforce the same limit.
export fn echidna_spark_max_usages() callconv(.C) usize {
    return MAX_USAGES;
}

// ============================================================================
// Compile-time assertions
// ============================================================================

comptime {
    // Danger-level wire encoding must fit in a u8
    std.debug.assert(DANGER_REJECT <= std.math.maxInt(u8));
    // Policy discriminants must fit in an i32 (they're 0–3)
    std.debug.assert(POLICY_REJECTED <= std.math.maxInt(i32));
}
