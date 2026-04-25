// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
//
//! Rust bindings to the SPARK-verified axiom-policy layer.
//!
//! Call path:
//!   Rust (this file)
//!     → Zig shim (src/zig/ffi/axiom_spark_bridge.zig, extern "C")
//!     → Ada/SPARK (src/ada/spark/axiom_c_bridge.adb → axiom_policy.adb)
//!
//! GNATprove formally verifies two invariants in axiom_policy.ads:
//!   1. Soundness  — any Reject-level input → PolicyRejected output
//!   2. Precision  — no Reject-level input  → never PolicyRejected
//!
//! The functions here are only compiled when `--features spark` is active;
//! callers guard with `#[cfg(feature = "spark")]`.
//!
//! # Safety justification
//!
//! The two `extern "C"` raw FFI calls below are the only unsafe sites.
//! Each call:
//!   - passes a pointer that is valid for `count` bytes (slice guarantee)
//!   - never passes null (slice.as_ptr() is always non-null)
//!   - count is bounded by MAX_USAGES (validated in the safe wrapper)
//!
//! The underlying SPARK/Ada code has been formally verified correct; the
//! Zig shim adds a null-pointer guard and a count-bounds check redundantly.

use crate::verification::axiom_tracker::{AxiomPolicy, AxiomUsage, DangerLevel};
#[cfg(test)]
use crate::provers::ProverKind;

// ────────────────────────────────────────────────────────────────────────────
// Wire-format constants (must match src/ada/spark/axiom_types.ads)
// ────────────────────────────────────────────────────────────────────────────

const DANGER_SAFE: u8 = 0;
const DANGER_NOTED: u8 = 1;
const DANGER_WARNING: u8 = 2;
const DANGER_REJECT: u8 = 3;

const POLICY_CLEAN: i32 = 0;
const POLICY_CLASSICAL: i32 = 1;
const POLICY_INCOMPLETE: i32 = 2;
const POLICY_REJECTED: i32 = 3;

/// Maximum usages the SPARK bridge accepts (matches Ada Max_Usages = 1024)
pub const SPARK_MAX_USAGES: usize = 1024;

// ────────────────────────────────────────────────────────────────────────────
// extern "C" declarations — resolved from libechidna_spark_zig.a at link time
// ────────────────────────────────────────────────────────────────────────────

extern "C" {
    /// SPARK-verified enforce_policy.
    /// Returns 0–3 on success, -1 on invalid input.
    fn echidna_spark_enforce_policy(danger_levels: *const u8, count: usize) -> i32;

    /// SPARK-verified worst_danger.
    /// Returns 0–3 on success, -1 on invalid input.
    fn echidna_spark_worst_danger(danger_levels: *const u8, count: usize) -> i32;

    /// Returns the maximum array size the bridge accepts (compile-time constant).
    fn echidna_spark_max_usages() -> usize;
}

// ────────────────────────────────────────────────────────────────────────────
// Conversion helpers
// ────────────────────────────────────────────────────────────────────────────

fn danger_to_u8(d: DangerLevel) -> u8 {
    match d {
        DangerLevel::Safe => DANGER_SAFE,
        DangerLevel::Noted => DANGER_NOTED,
        DangerLevel::Warning => DANGER_WARNING,
        DangerLevel::Reject => DANGER_REJECT,
    }
}

fn i32_to_policy(n: i32) -> Option<AxiomPolicy> {
    match n {
        POLICY_CLEAN => Some(AxiomPolicy::Clean),
        POLICY_CLASSICAL => Some(AxiomPolicy::ClassicalAxioms(vec![])),
        POLICY_INCOMPLETE => Some(AxiomPolicy::IncompleteProof(vec![])),
        POLICY_REJECTED => Some(AxiomPolicy::Rejected(vec![])),
        _ => None,
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Public safe wrappers
// ────────────────────────────────────────────────────────────────────────────

/// Error type for SPARK bridge failures.
#[derive(Debug, thiserror::Error)]
pub enum SparkError {
    #[error("too many usages: {0} > 1024 (SPARK_MAX_USAGES)")]
    TooManyUsages(usize),
    #[error("SPARK bridge returned unexpected value: {0}")]
    UnexpectedReturn(i32),
    #[error("SPARK bridge not available (built without --features spark)")]
    NotAvailable,
}

/// Call the SPARK-verified `Enforce` function.
///
/// Converts `usages` to a u8 wire array and calls through the Zig shim
/// into the Ada/SPARK body.  The usages vector is reconstructed on return
/// (the SPARK layer only operates on DangerLevel discriminants, not the
/// full AxiomUsage structs — that is by design: the policy decision
/// is independent of prover identity or line number).
pub fn spark_enforce_policy(usages: &[AxiomUsage]) -> Result<AxiomPolicy, SparkError> {
    if usages.len() > SPARK_MAX_USAGES {
        return Err(SparkError::TooManyUsages(usages.len()));
    }

    let wire: Vec<u8> = usages.iter().map(|u| danger_to_u8(u.danger_level)).collect();

    // SAFETY: wire is non-empty only when usages is non-empty;
    // wire.as_ptr() is always non-null; wire.len() is bounded above.
    let raw = unsafe { echidna_spark_enforce_policy(wire.as_ptr(), wire.len()) };

    match raw {
        POLICY_CLEAN => Ok(AxiomPolicy::Clean),
        POLICY_CLASSICAL => {
            let noted: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level == DangerLevel::Noted)
                .cloned()
                .collect();
            Ok(AxiomPolicy::ClassicalAxioms(noted))
        },
        POLICY_INCOMPLETE => {
            let warnings: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level >= DangerLevel::Warning)
                .cloned()
                .collect();
            Ok(AxiomPolicy::IncompleteProof(warnings))
        },
        POLICY_REJECTED => {
            let rejects: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level == DangerLevel::Reject)
                .cloned()
                .collect();
            Ok(AxiomPolicy::Rejected(rejects))
        },
        other => Err(SparkError::UnexpectedReturn(other)),
    }
}

/// Call the SPARK-verified `Worst_Danger` function.
///
/// Returns the highest danger level in `usages`, or `DangerLevel::Safe` for
/// an empty slice.  The SPARK Post-condition guarantees:
///   result = Reject  iff  any usage carries DangerLevel::Reject
pub fn spark_worst_danger(usages: &[AxiomUsage]) -> Result<DangerLevel, SparkError> {
    if usages.len() > SPARK_MAX_USAGES {
        return Err(SparkError::TooManyUsages(usages.len()));
    }

    let wire: Vec<u8> = usages.iter().map(|u| danger_to_u8(u.danger_level)).collect();

    // SAFETY: same reasoning as spark_enforce_policy above.
    let raw = unsafe { echidna_spark_worst_danger(wire.as_ptr(), wire.len()) };

    match raw {
        0 => Ok(DangerLevel::Safe),
        1 => Ok(DangerLevel::Noted),
        2 => Ok(DangerLevel::Warning),
        3 => Ok(DangerLevel::Reject),
        other => Err(SparkError::UnexpectedReturn(other)),
    }
}

/// Query the bridge's compile-time upper limit on usages per call.
pub fn spark_capacity() -> usize {
    // SAFETY: pure function with no mutable state.
    unsafe { echidna_spark_max_usages() }
}

// ────────────────────────────────────────────────────────────────────────────
// Cross-check: run both Rust and SPARK paths and compare.
// Intended for CI / debug builds to catch any drift.
// ────────────────────────────────────────────────────────────────────────────

/// Compare the Rust `enforce_policy` result to the SPARK result.
///
/// Returns `Ok(policy)` if both agree, `Err` if they diverge.
/// Call this in tests or via the `just verify-spark-crosscheck` recipe.
pub fn crosscheck_enforce_policy(
    usages: &[AxiomUsage],
    rust_result: &AxiomPolicy,
) -> Result<(), String> {
    let spark_result = spark_enforce_policy(usages)
        .map_err(|e| format!("SPARK bridge error: {e}"))?;

    let rust_disc = policy_discriminant(rust_result);
    let spark_disc = policy_discriminant(&spark_result);

    if rust_disc != spark_disc {
        Err(format!(
            "SPARK/Rust enforce_policy divergence: \
             Rust={rust_disc} SPARK={spark_disc} (usages count={})",
            usages.len()
        ))
    } else {
        Ok(())
    }
}

fn policy_discriminant(p: &AxiomPolicy) -> i32 {
    match p {
        AxiomPolicy::Clean => POLICY_CLEAN,
        AxiomPolicy::ClassicalAxioms(_) => POLICY_CLASSICAL,
        AxiomPolicy::IncompleteProof(_) => POLICY_INCOMPLETE,
        AxiomPolicy::Rejected(_) => POLICY_REJECTED,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::provers::ProverKind;

    fn make_usage(level: DangerLevel) -> AxiomUsage {
        AxiomUsage {
            prover: ProverKind::Lean,
            construct: "test".to_string(),
            danger_level: level,
            explanation: String::new(),
            line: None,
        }
    }

    #[test]
    fn spark_empty_usages_gives_clean() {
        let result = spark_enforce_policy(&[]).expect("SPARK bridge call");
        assert!(matches!(result, AxiomPolicy::Clean));
    }

    #[test]
    fn spark_reject_gives_rejected() {
        let usages = vec![make_usage(DangerLevel::Reject)];
        let result = spark_enforce_policy(&usages).expect("SPARK bridge call");
        assert!(matches!(result, AxiomPolicy::Rejected(_)));
        assert!(!result.is_acceptable());
    }

    #[test]
    fn spark_safe_only_gives_clean() {
        let usages = vec![make_usage(DangerLevel::Safe), make_usage(DangerLevel::Safe)];
        let result = spark_enforce_policy(&usages).expect("SPARK bridge call");
        assert!(matches!(result, AxiomPolicy::Clean));
    }

    #[test]
    fn spark_warning_no_reject_gives_incomplete() {
        let usages = vec![make_usage(DangerLevel::Warning)];
        let result = spark_enforce_policy(&usages).expect("SPARK bridge call");
        assert!(matches!(result, AxiomPolicy::IncompleteProof(_)));
        assert!(result.is_acceptable());
    }

    #[test]
    fn spark_reject_beats_warning() {
        let usages = vec![make_usage(DangerLevel::Warning), make_usage(DangerLevel::Reject)];
        let result = spark_enforce_policy(&usages).expect("SPARK bridge call");
        assert!(matches!(result, AxiomPolicy::Rejected(_)));
    }

    #[test]
    fn spark_worst_danger_empty_is_safe() {
        let result = spark_worst_danger(&[]).expect("SPARK bridge call");
        assert_eq!(result, DangerLevel::Safe);
    }

    #[test]
    fn spark_worst_danger_with_reject() {
        let usages = vec![make_usage(DangerLevel::Noted), make_usage(DangerLevel::Reject)];
        let result = spark_worst_danger(&usages).expect("SPARK bridge call");
        assert_eq!(result, DangerLevel::Reject);
    }

    #[test]
    fn spark_capacity_is_1024() {
        assert_eq!(spark_capacity(), 1024);
    }
}
