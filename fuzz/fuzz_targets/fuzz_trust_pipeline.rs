// SPDX-License-Identifier: PMPL-1.0-or-later
//!
//! Fuzz target: `compute_trust_level` invariant
//!
//! Checks that for *any* combination of trust factor inputs the function
//! always returns a TrustLevel whose numeric value is in the range `1..=5`.
//! A result outside that range would be a logic bug in the trust pipeline.
//!
//! Input is generated via the `arbitrary` crate so cargo-fuzz / AFL++ can
//! structure the byte stream into a valid Rust struct automatically.
//!
//! Coverage goals:
//! - All five TrustLevel variants are reachable
//! - The `is_small_kernel_prover` predicate branch (ProverKind::Z3 is not)
//! - DangerLevel ordering (Safe < Noted < Warning < Reject)
//! - The portfolio_confidence `None` path (held fixed for simplicity)

#![no_main]

use arbitrary::Arbitrary;
use echidna::provers::ProverKind;
use echidna::verification::axiom_tracker::DangerLevel;
use echidna::verification::confidence::{TrustFactors, compute_trust_level};
use libfuzzer_sys::fuzz_target;

/// Fuzz-friendly mirror of the trust factor inputs.
///
/// We use a fixed prover (`ProverKind::Z3`) so the arbitrary derivation only
/// needs to cover the remaining orthogonal axes.  Z3 is not a small-kernel
/// prover, which means the Level-4/5 paths are reachable only via
/// `confirming_provers >= 2`.  To also exercise the small-kernel paths, the
/// `use_small_kernel` flag switches to `ProverKind::Lean` when set.
#[derive(Arbitrary, Debug)]
struct FuzzTrustFactors {
    /// Whether to use a small-kernel prover (Lean) instead of Z3.
    use_small_kernel: bool,
    /// Number of independent provers that confirmed the result.
    confirming_provers: u32,
    /// Whether a proof certificate was produced.
    has_certificate: bool,
    /// Whether the certificate was independently verified.
    certificate_verified: bool,
    /// Maps to a DangerLevel: 0=Safe, 1=Noted, 2=Warning, 3+=Reject.
    worst_axiom_danger_index: u8,
    /// Whether the solver binary passed its integrity check.
    solver_integrity_ok: bool,
}

/// Map an arbitrary byte index to a `DangerLevel` value.
///
/// The mapping is modular so no input byte is "dead" — every value exercises
/// at least one branch.
fn index_to_danger(idx: u8) -> DangerLevel {
    match idx % 4 {
        0 => DangerLevel::Safe,
        1 => DangerLevel::Noted,
        2 => DangerLevel::Warning,
        _ => DangerLevel::Reject,
    }
}

fuzz_target!(|fuzz: FuzzTrustFactors| {
    let prover = if fuzz.use_small_kernel {
        ProverKind::Lean
    } else {
        ProverKind::Z3
    };

    let factors = TrustFactors {
        prover,
        confirming_provers: fuzz.confirming_provers,
        has_certificate: fuzz.has_certificate,
        certificate_verified: fuzz.certificate_verified,
        worst_axiom_danger: index_to_danger(fuzz.worst_axiom_danger_index),
        solver_integrity_ok: fuzz.solver_integrity_ok,
        // Hold portfolio confidence fixed; the field does not participate in
        // the current decision logic (compute_trust_level ignores it), so
        // fuzzing it adds no coverage and would only inflate input entropy.
        portfolio_confidence: None,
    };

    let level = compute_trust_level(&factors);
    let value = level.value();

    // INVARIANT: the trust pipeline must always produce a level in 1..=5.
    // A result outside this range indicates a bug in the matching logic.
    assert!(
        (1..=5).contains(&value),
        "compute_trust_level returned out-of-range value {value} for factors {factors:?}"
    );

    // Exercise the description and Display impls while we have a live value.
    let _ = level.description();
    let _ = level.to_string();
});
