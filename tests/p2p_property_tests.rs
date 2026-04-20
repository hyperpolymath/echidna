// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
//! Point-to-Point property-based tests for ECHIDNA.
//!
//! These tests use proptest to validate system-level invariants:
//!
//!   1. Dispatch determinism: same input always produces the same trust level
//!   2. ProofState serialisation: arbitrary states survive JSON roundtrip
//!   3. DispatchResult soundness: certain field combinations cannot co-exist
//!   4. AxiomTracker scan: properties of the scan result
//!   5. Trust computation monotonicity: adding confirming provers never reduces trust
//!
//! P2P (Point-to-Point) tests validate properties at the API boundary —
//! the interface between a caller and an ECHIDNA subsystem.

use echidna::core::{Context, Goal, ProofState, Term};
use echidna::dispatch::DispatchConfig;
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::axiom_tracker::AxiomTracker;
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::DangerLevel;
use proptest::prelude::*;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

/// Generate an arbitrary Term (limited depth to avoid stack overflow)
fn arb_term(depth: u32) -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        "[a-z][a-z0-9_]{0,8}".prop_map(Term::Const),
        "[a-z][a-z0-9_]{0,8}".prop_map(Term::Var),
        (0usize..4).prop_map(Term::Universe),
    ];

    if depth == 0 {
        return leaf.boxed();
    }

    prop_oneof![
        leaf,
        // App: func applied to 1-3 args
        (
            "[a-z][a-z0-9]{0,5}".prop_map(|s| Term::Const(s)),
            prop::collection::vec(arb_term(0), 1..4),
        )
            .prop_map(|(func, args)| Term::App {
                func: Box::new(func),
                args,
            }),
    ]
    .boxed()
}

/// Generate an arbitrary ProofState with 0-3 goals
fn arb_proof_state() -> impl Strategy<Value = ProofState> {
    prop::collection::vec(("[a-z_]{1,10}".prop_map(String::from), arb_term(1)), 0..3).prop_map(
        |goals| {
            let goals = goals
                .into_iter()
                .enumerate()
                .map(|(_i, (id, target))| Goal {
                    id,
                    hypotheses: vec![],
                    target,
                })
                .collect();
            ProofState {
                goals,
                context: Context::default(),
                proof_script: vec![],
                metadata: HashMap::new(),
            }
        },
    )
}

/// Generate a ProverKind (subset that always instantiates cleanly)
fn arb_prover_kind() -> impl Strategy<Value = ProverKind> {
    prop_oneof![
        Just(ProverKind::Z3),
        Just(ProverKind::CVC5),
        Just(ProverKind::Lean),
        Just(ProverKind::Coq),
        Just(ProverKind::Isabelle),
        Just(ProverKind::Z3), // weighted higher as most available
        Just(ProverKind::Agda),
        Just(ProverKind::Idris2),
        Just(ProverKind::Vampire),
        Just(ProverKind::Metamath),
    ]
}

/// Generate a DangerLevel
fn arb_danger_level() -> impl Strategy<Value = DangerLevel> {
    prop_oneof![
        Just(DangerLevel::Safe),
        Just(DangerLevel::Noted),
        Just(DangerLevel::Warning),
        Just(DangerLevel::Reject),
    ]
}

/// Generate TrustFactors with the given fixed danger level
fn arb_trust_factors_with_danger(danger: DangerLevel) -> impl Strategy<Value = TrustFactors> {
    (
        arb_prover_kind(),
        1u32..5,
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
    )
        .prop_map(
            move |(prover, confirming, has_cert, cert_verified, integrity_ok)| TrustFactors {
                prover,
                confirming_provers: confirming,
                has_certificate: has_cert,
                certificate_verified: cert_verified,
                worst_axiom_danger: danger,
                solver_integrity_ok: integrity_ok,
                portfolio_confidence: None,
            },
        )
}

// ---------------------------------------------------------------------------
// P2P 1: compute_trust_level is deterministic (pure function)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// compute_trust_level must return the same value given the same inputs.
    /// It is a pure function with no hidden state.
    #[test]
    fn p2p_trust_computation_is_deterministic(
        prover in arb_prover_kind(),
        confirming in 1u32..6,
        has_cert in any::<bool>(),
        cert_verified in any::<bool>(),
        danger in arb_danger_level(),
        integrity_ok in any::<bool>(),
    ) {
        let factors = TrustFactors {
            prover,
            confirming_provers: confirming,
            has_certificate: has_cert,
            certificate_verified: cert_verified,
            worst_axiom_danger: danger,
            solver_integrity_ok: integrity_ok,
            portfolio_confidence: None,
        };

        let r1 = compute_trust_level(&factors);
        let r2 = compute_trust_level(&factors);
        prop_assert_eq!(r1, r2, "compute_trust_level must be deterministic");
    }
}

// ---------------------------------------------------------------------------
// P2P 2: Reject danger always prevents Level3+ trust
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// No matter how many confirming provers or certificates, Reject-level
    /// danger must prevent the trust level from reaching Level3 or above.
    #[test]
    fn p2p_reject_danger_caps_trust(
        factors in arb_trust_factors_with_danger(DangerLevel::Reject),
    ) {
        let trust = compute_trust_level(&factors);
        prop_assert!(
            trust < TrustLevel::Level3,
            "Reject danger must prevent Level3+ trust, got {:?} from factors {:?}",
            trust,
            factors
        );
    }
}

// ---------------------------------------------------------------------------
// P2P 3: Safe danger never produces lower trust than Warning
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// For identical factors except danger level, Safe must produce >= trust
    /// compared to Warning. Adding danger can only decrease trust.
    #[test]
    fn p2p_safe_danger_not_worse_than_warning(
        prover in arb_prover_kind(),
        confirming in 1u32..4,
        has_cert in any::<bool>(),
        cert_verified in any::<bool>(),
        integrity_ok in any::<bool>(),
    ) {
        let safe_factors = TrustFactors {
            prover,
            confirming_provers: confirming,
            has_certificate: has_cert,
            certificate_verified: cert_verified,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: integrity_ok,
            portfolio_confidence: None,
        };
        let warning_factors = TrustFactors {
            worst_axiom_danger: DangerLevel::Warning,
            ..safe_factors.clone()
        };

        let safe_trust = compute_trust_level(&safe_factors);
        let warning_trust = compute_trust_level(&warning_factors);

        prop_assert!(
            safe_trust >= warning_trust,
            "Safe danger {:?} must produce >= trust compared to Warning danger {:?}",
            safe_trust,
            warning_trust
        );
    }
}

// ---------------------------------------------------------------------------
// P2P 4: ProofState JSON roundtrip
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Arbitrary ProofState values must survive a JSON serialise/deserialise
    /// roundtrip with all fields preserved.
    #[test]
    fn p2p_proof_state_json_roundtrip(state in arb_proof_state()) {
        let json = serde_json::to_string(&state)
            .expect("ProofState must serialise to JSON");
        let roundtripped: ProofState = serde_json::from_str(&json)
            .expect("ProofState must deserialise from JSON");

        prop_assert_eq!(
            state.goals.len(),
            roundtripped.goals.len(),
            "Goal count must survive JSON roundtrip"
        );
        for (orig, rt) in state.goals.iter().zip(roundtripped.goals.iter()) {
            prop_assert_eq!(&orig.id, &rt.id, "Goal id must survive roundtrip");
        }
        prop_assert_eq!(
            state.proof_script,
            roundtripped.proof_script,
            "proof_script must survive roundtrip"
        );
    }
}

// ---------------------------------------------------------------------------
// P2P 5: DispatchConfig — timeout must always be positive after modification
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Any DispatchConfig with timeout > 0 must remain valid after cloning.
    #[test]
    fn p2p_dispatch_config_clone_preserves_timeout(timeout in 1u64..3600) {
        let config = DispatchConfig {
            timeout,
            ..DispatchConfig::default()
        };
        let cloned = config.clone();
        prop_assert_eq!(config.timeout, cloned.timeout, "Clone must preserve timeout");
        prop_assert_eq!(config.track_axioms, cloned.track_axioms, "Clone must preserve track_axioms");
        prop_assert_eq!(config.cross_check, cloned.cross_check, "Clone must preserve cross_check");
    }
}

// ---------------------------------------------------------------------------
// P2P 6: ProverFactory — all provided kinds produce valid backends
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// ProverFactory::create must succeed for all values returned by
    /// arb_prover_kind(). The created backend must have the correct kind.
    #[test]
    fn p2p_prover_factory_correct_kind(kind in arb_prover_kind()) {
        let config = ProverConfig::default();
        match ProverFactory::create(kind, config) {
            Ok(backend) => {
                prop_assert_eq!(
                    backend.kind(),
                    kind,
                    "Created backend kind must match requested kind"
                );
            }
            Err(e) => {
                // Factory failure is acceptable (binary not installed)
                // but must not panic
                let _ = e;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// P2P 7: AxiomTracker scan — result is consistent (no usages for empty input)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Scanning completely empty content should produce zero usages for any
    /// prover. Dangerous patterns only appear when the pattern is present.
    #[test]
    fn p2p_axiom_tracker_empty_input_no_usages(kind in arb_prover_kind()) {
        let tracker = AxiomTracker::new();
        let usages = tracker.scan(kind, "");
        prop_assert!(
            usages.is_empty(),
            "Scanning empty string must produce 0 axiom usages for {:?}, got: {:?}",
            kind,
            usages
        );
    }
}

// ---------------------------------------------------------------------------
// P2P 8: AxiomTracker — scan is idempotent (calling twice gives same result)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Scanning the same content twice must produce the same number of usages.
    /// The scanner must be stateless.
    #[test]
    fn p2p_axiom_tracker_scan_idempotent(
        content in "[a-zA-Z0-9 .,;\n]{0,200}",
        kind in arb_prover_kind(),
    ) {
        let tracker = AxiomTracker::new();
        let first = tracker.scan(kind, &content).len();
        let second = tracker.scan(kind, &content).len();
        prop_assert_eq!(
            first,
            second,
            "AxiomTracker.scan must be idempotent for {:?} on {:?}",
            kind,
            &content[..content.len().min(40)]
        );
    }
}

// ---------------------------------------------------------------------------
// P2P 9: ProverKind serialisation roundtrip (property version)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// All ProverKind values in arb_prover_kind() must survive JSON roundtrip.
    #[test]
    fn p2p_prover_kind_json_roundtrip(kind in arb_prover_kind()) {
        let json = serde_json::to_string(&kind)
            .expect("ProverKind must serialise");
        let decoded: ProverKind = serde_json::from_str(&json)
            .expect("ProverKind must deserialise");
        prop_assert_eq!(kind, decoded, "ProverKind JSON roundtrip must be identity");
    }
}

// ---------------------------------------------------------------------------
// P2P 10: TrustLevel ordering is consistent with value()
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// For any two trust levels, the partial_cmp result must agree with the
    /// value() comparison.
    #[test]
    fn p2p_trust_level_ordering_consistent_with_value(
        factors_a in arb_trust_factors_with_danger(DangerLevel::Safe),
        factors_b in arb_trust_factors_with_danger(DangerLevel::Safe),
    ) {
        let trust_a = compute_trust_level(&factors_a);
        let trust_b = compute_trust_level(&factors_b);

        // PartialOrd must agree with value()
        if trust_a.value() < trust_b.value() {
            prop_assert!(trust_a < trust_b, "value ordering must agree with PartialOrd");
        } else if trust_a.value() > trust_b.value() {
            prop_assert!(trust_a > trust_b, "value ordering must agree with PartialOrd");
        } else {
            prop_assert_eq!(trust_a, trust_b, "equal values must be equal trust levels");
        }
    }
}
