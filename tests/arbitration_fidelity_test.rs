// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! ECH-05 acceptance tests: the arbiter's level is set by fidelity
//! evidence, not by how many backends agree.
//!
//! - A synonym collision (lexically aligned, formally distinct
//!   statements) never reaches `sound`, under any policy, even though the
//!   numeric fusion still reports a cross-checked proof.
//! - A MiniF2F-aligned pair with kernel-checked translations to one term
//!   reaches `sound` (positive control), and a one-token mistranslation
//!   of the same pair does not (negative control).
//! - Retracting a backend lowers every verdict that rested on it and
//!   leaves the others alone (residual-evidence-types `dependent-holds`).
//!
//! What this does not test: that a `KernelTranslation` certificate can be
//! produced. The exchange-layer terms below are the translation targets,
//! written by hand; no bridge in `src/rust/exchange/` emits them yet
//! (ROADMAP stage 6). The tests check the arbiter's policy given
//! certificates, not the certificates.

use echidna::exchange::{term_hash, ExchangeFormat};
use echidna::provers::outcome::ProverOutcome;
use echidna::provers::ProverKind;
use echidna::verification::portfolio::PortfolioConfidence;
use echidna::verification::{
    ArbitratedVerdict, ArbitrationPolicy, EpistemicLevel, FidelityEvidence, ProverAttempt,
    ResultArbiter,
};

const TIMEOUT_MS: u64 = 300_000;

/// `mathd_numbertheory_3` from MiniF2F (test split), checked against
/// openai/miniF2F@4e433ff. Lean (`lean/src/test.lean`):
///   `(∑ x in finset.range 10, ((x + 1)^2)) % 10 = 5`
/// Isabelle (`isabelle/test/mathd_numbertheory_3.thy`):
///   `(\<Sum> x < 10. ((x + 1)^2)) mod 10 = (5::nat)`
/// Both sum over {0, …, 9}, so both translate to this λΠ term.
const NT3_TERM: &str = "eq nat (mod (sum (range 10) (x : nat => pow (add x 1) 2)) 10) 5";

/// The same pair with Isabelle's `x < 10` mistranslated as `x ≤ 10`.
const NT3_OFF_BY_ONE: &str = "eq nat (mod (sum (range_le 10) (x : nat => pow (add x 1) 2)) 10) 5";

/// Constructed collision (not a MiniF2F problem): "for every natural
/// number n, 2 divides n(n+1)". A synonym table that aligns Lean's `ℕ`
/// (which contains 0) with set.mm's `NN` (positive integers; `NN0` is the
/// one with 0) lets both backends prove "it", but the Metamath statement
/// says nothing about n = 0.
const NAT_TERM: &str = "forall (n : nat), divides 2 (mul n (add n 1))";
const NN_TERM: &str = "forall (n : nat), lt 0 n -> divides 2 (mul n (add n 1))";

fn proved(prover: ProverKind, ms: u64) -> ProverAttempt {
    ProverAttempt::new(prover, ProverOutcome::Proved { elapsed_ms: ms }, ms)
}

/// A Dedukti translation of `term`, checked by the Dedukti kernel.
fn kernel(term: &str) -> FidelityEvidence {
    FidelityEvidence::KernelTranslation {
        format: ExchangeFormat::Dedukti,
        checked_by: ProverKind::Dedukti,
        term_hash: term_hash(ExchangeFormat::Dedukti, term),
    }
}

fn policies() -> [ArbitrationPolicy; 3] {
    [
        ArbitrationPolicy::Portfolio,
        ArbitrationPolicy::Bayesian { prior_p_true: 0.5 },
        ArbitrationPolicy::DempsterShafer,
    ]
}

fn arbitrate(policy: ArbitrationPolicy, attempts: &[ProverAttempt]) -> ArbitratedVerdict {
    ResultArbiter::new(policy, TIMEOUT_MS).arbitrate(attempts)
}

#[test]
fn synonym_collision_cannot_reach_sound() {
    let lean = || proved(ProverKind::Lean, 1_400);
    let metamath = || proved(ProverKind::Metamath, 300);

    let variants: [(&str, Vec<ProverAttempt>); 4] = [
        ("lexical alignment only", vec![lean(), metamath()]),
        (
            "kernel translations to different terms",
            vec![
                lean().with_fidelity(kernel(NAT_TERM)),
                metamath().with_fidelity(kernel(NN_TERM)),
            ],
        ),
        (
            // Consequence testing instantiates the source claim at n = 0;
            // the Metamath statement does not entail that instance.
            "declared correspondence with a failed consequence test",
            vec![
                lean().with_fidelity(kernel(NAT_TERM)),
                metamath().with_fidelity(FidelityEvidence::DeclaredCorrespondence {
                    consequence_tests: 8,
                    failures: 1,
                }),
            ],
        ),
        (
            "declared correspondence that was never tested",
            vec![
                lean().with_fidelity(kernel(NAT_TERM)),
                metamath().with_fidelity(FidelityEvidence::DeclaredCorrespondence {
                    consequence_tests: 0,
                    failures: 0,
                }),
            ],
        ),
    ];

    for policy in policies() {
        for (label, attempts) in &variants {
            let v = arbitrate(policy, attempts);
            // The numbers still say "both proved it" ...
            assert_eq!(v.verified, Some(true), "{label} / {policy:?}");
            assert_eq!(v.confidence, PortfolioConfidence::CrossChecked);
            // ... and the level says that is belief, not a warrant.
            assert_eq!(v.level, EpistemicLevel::Belief, "{label} / {policy:?}");
            assert_eq!(v.warranted_term, None);
        }
    }
}

#[test]
fn minif2f_aligned_pair_reaches_sound() {
    let attempts = [
        proved(ProverKind::Lean, 2_100).with_fidelity(kernel(NT3_TERM)),
        proved(ProverKind::Isabelle, 3_300).with_fidelity(kernel(NT3_TERM)),
    ];
    for policy in policies() {
        let v = arbitrate(policy, &attempts);
        assert_eq!(v.verified, Some(true), "{policy:?}");
        assert!(!v.needs_review, "{policy:?}");
        assert_eq!(v.level, EpistemicLevel::Sound, "{policy:?}");
        assert_eq!(
            v.warranted_term.as_deref(),
            Some(term_hash(ExchangeFormat::Dedukti, NT3_TERM).as_str())
        );
    }
}

#[test]
fn minif2f_mistranslated_pair_does_not_reach_sound() {
    let attempts = [
        proved(ProverKind::Lean, 2_100).with_fidelity(kernel(NT3_TERM)),
        proved(ProverKind::Isabelle, 3_300).with_fidelity(kernel(NT3_OFF_BY_ONE)),
    ];
    for policy in policies() {
        let v = arbitrate(policy, &attempts);
        assert_eq!(v.verified, Some(true), "{policy:?}");
        assert_eq!(v.level, EpistemicLevel::Belief, "{policy:?}");
    }
}

#[test]
fn retracted_backend_lowers_every_dependent_verdict() {
    const TERM_B: &str = "forall (a b : nat), eq nat (add a b) (add b a)";
    const TERM_C: &str = "forall (n : nat), le n (mul n n)";
    let goals: [(&str, Vec<ProverAttempt>); 3] = [
        (
            "A (Lean + Isabelle)",
            vec![
                proved(ProverKind::Lean, 2_100).with_fidelity(kernel(NT3_TERM)),
                proved(ProverKind::Isabelle, 3_300).with_fidelity(kernel(NT3_TERM)),
            ],
        ),
        (
            "B (Lean + Coq)",
            vec![
                proved(ProverKind::Lean, 900).with_fidelity(kernel(TERM_B)),
                proved(ProverKind::Coq, 1_200).with_fidelity(kernel(TERM_B)),
            ],
        ),
        (
            "C (Isabelle + HOL Light)",
            vec![
                proved(ProverKind::Isabelle, 1_000).with_fidelity(kernel(TERM_C)),
                proved(ProverKind::HOLLight, 1_800).with_fidelity(kernel(TERM_C)),
            ],
        ),
    ];

    for policy in policies() {
        let mut arbiter = ResultArbiter::new(policy, TIMEOUT_MS);
        let before: Vec<ArbitratedVerdict> =
            goals.iter().map(|(_, a)| arbiter.arbitrate(a)).collect();
        for (v, (label, _)) in before.iter().zip(&goals) {
            assert_eq!(v.level, EpistemicLevel::Sound, "{label} / {policy:?}");
        }

        arbiter.retract(ProverKind::Lean);
        let after: Vec<ArbitratedVerdict> =
            goals.iter().map(|(_, a)| arbiter.arbitrate(a)).collect();

        for ((b, a), (label, _)) in before.iter().zip(&after).zip(&goals) {
            // Numeric fusion is untouched by retraction.
            assert_eq!(a.verified, b.verified, "{label} / {policy:?}");
            assert_eq!(a.confidence, b.confidence, "{label} / {policy:?}");
            assert_eq!(a.conflict, b.conflict, "{label} / {policy:?}");
        }
        // A and B rested on Lean: lowered, and say why.
        for (v, (label, _)) in after.iter().zip(&goals).take(2) {
            assert_eq!(v.level, EpistemicLevel::Belief, "{label} / {policy:?}");
            assert_eq!(v.retracted, vec![ProverKind::Lean], "{label}");
        }
        // C did not: it keeps its level (negative control).
        assert_eq!(after[2].level, EpistemicLevel::Sound, "C / {policy:?}");
        assert!(after[2].retracted.is_empty());

        // Dropping the retracted attempt and re-arbitrating fuses without it.
        let a_without_lean = [goals[0].1[1].clone()];
        let v = arbiter.arbitrate(&a_without_lean);
        assert_eq!(v.confidence, PortfolioConfidence::SingleSolver);
        assert_eq!(v.level, EpistemicLevel::Sound, "{policy:?}");
    }
}
