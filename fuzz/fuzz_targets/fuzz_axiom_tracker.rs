// SPDX-License-Identifier: PMPL-1.0-or-later
//!
//! Fuzz target: `AxiomTracker::scan` — no panic on arbitrary UTF-8 input
//!
//! Verifies that `AxiomTracker::scan` is robust against arbitrary proof-file
//! content.  The tracker must:
//!
//! 1. Never panic, regardless of input content or prover kind.
//! 2. Return only `AxiomUsage` values whose `danger_level` is a valid
//!    `DangerLevel` variant.
//! 3. Leave `enforce_policy` and `analyze` consistent with each other.
//!
//! `ProverKind` has many variants; we map the arbitrary `u8` modulo the
//! number of interesting provers so that all well-known dangerous patterns
//! (Lean sorry, Coq Admitted, Agda postulate, Idris2 believe_me, HOL4
//! mk_thm, …) are reachable within a reasonable fuzz campaign.

#![no_main]

use arbitrary::Arbitrary;
use echidna::provers::ProverKind;
use echidna::verification::axiom_tracker::{AxiomTracker, DangerLevel};
use libfuzzer_sys::fuzz_target;

/// Fuzz input: arbitrary UTF-8 string + prover index.
///
/// We derive `Arbitrary` on a wrapper rather than on `String` directly so
/// cargo-fuzz can use structured mutation on the two fields independently.
#[derive(Arbitrary, Debug)]
struct FuzzInput {
    /// Proof content — `arbitrary::Arbitrary` for `String` guarantees valid UTF-8.
    content: String,
    /// Selects the prover via modular indexing over PROVERS below.
    prover_index: u8,
}

/// The subset of ProverKind variants that have registered patterns in
/// AxiomTracker.  Provers not in this list still exercise the "no patterns"
/// branch of scan(), which must also be panic-free.
const PROVERS: &[ProverKind] = &[
    ProverKind::Lean,
    ProverKind::Coq,
    ProverKind::Agda,
    ProverKind::Isabelle,
    ProverKind::HOL4,
    ProverKind::Idris2,
    ProverKind::FStar,
    // Provers with no registered patterns — tests the empty-map fast-path.
    ProverKind::Z3,
    ProverKind::CVC5,
    ProverKind::Vampire,
    ProverKind::Metamath,
    ProverKind::Dafny,
];

fuzz_target!(|input: FuzzInput| {
    let prover = PROVERS[input.prover_index as usize % PROVERS.len()];
    let tracker = AxiomTracker::new();

    // scan() must not panic on any UTF-8 string for any ProverKind.
    let usages = tracker.scan(prover, &input.content);

    // INVARIANT: every returned usage must have a valid DangerLevel.
    // We validate by exhaustive match — an unknown discriminant would panic here.
    for usage in &usages {
        let _ = match usage.danger_level {
            DangerLevel::Safe => 0u8,
            DangerLevel::Noted => 1,
            DangerLevel::Warning => 2,
            DangerLevel::Reject => 3,
        };
        // Also touch every field so dead-code stripping doesn't hide bugs.
        let _ = usage.prover;
        let _ = usage.construct.len();
        let _ = usage.explanation.len();
        let _ = usage.line;
    }

    // enforce_policy must also be panic-free.
    let policy = tracker.enforce_policy(&usages);
    let _ = policy.is_acceptable();
    let _ = policy.worst_danger();
    let _ = policy.all_usages();

    // CONSISTENCY: analyze() must agree with scan() + enforce_policy().
    let policy2 = tracker.analyze(prover, &input.content);
    // Both paths must agree on acceptability.
    assert_eq!(
        policy.is_acceptable(),
        policy2.is_acceptable(),
        "analyze() and scan()+enforce_policy() disagree for prover {prover:?}"
    );
    // Worst danger must match too.
    assert_eq!(
        policy.worst_danger(),
        policy2.worst_danger(),
        "worst_danger() mismatch for prover {prover:?}"
    );
});
