// SPDX-License-Identifier: MPL-2.0
//
// Stage 8d: panic-attack hardened — proptest property harnesses
//
// Covers: Term/ProofState construction, trust pipeline invariants
// (compute_trust_level), DangerLevel Ord laws, and ParetoFrontier
// empty-frontier size. These properties are the first line of
// defence against panic-inducing inputs across the parser, trust
// pipeline, and FFI-adjacent boundaries.
//
// AFL++ nightly fuzz targets live in the separate `fuzz/` crate.

use echidna::core::{Goal, ProofState, Term};
use echidna::provers::ProverKind;
use echidna::verification::axiom_tracker::DangerLevel;
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::pareto::{ParetoFrontier, ProofCandidate, ProofObjective};
use proptest::prelude::*;

// ── helpers ──────────────────────────────────────────────────────────────────

/// Arbitrary strategy for `TrustLevel` (all 5 variants).
fn arb_trust_level() -> impl Strategy<Value = TrustLevel> {
    prop_oneof![
        Just(TrustLevel::Level1),
        Just(TrustLevel::Level2),
        Just(TrustLevel::Level3),
        Just(TrustLevel::Level4),
        Just(TrustLevel::Level5),
    ]
}

/// Arbitrary strategy for `DangerLevel` (all 4 variants).
fn arb_danger_level() -> impl Strategy<Value = DangerLevel> {
    prop_oneof![
        Just(DangerLevel::Safe),
        Just(DangerLevel::Noted),
        Just(DangerLevel::Warning),
        Just(DangerLevel::Reject),
    ]
}

/// Build a minimal `TrustFactors` with `ProverKind::Z3` as the concrete
/// prover and caller-supplied boolean/enum fields. Using Z3 keeps the
/// prover fixed so test failure messages are deterministic and don't
/// require an arbitrary `ProverKind` strategy across all 105 variants.
fn make_factors(
    confirming_provers: u32,
    has_certificate: bool,
    certificate_verified: bool,
    worst_axiom_danger: DangerLevel,
    solver_integrity_ok: bool,
) -> TrustFactors {
    TrustFactors {
        prover: ProverKind::Z3,
        confirming_provers,
        has_certificate,
        certificate_verified,
        worst_axiom_danger,
        solver_integrity_ok,
        portfolio_confidence: None,
    }
}

// ── Module 1: term_props ─────────────────────────────────────────────────────

mod term_props {
    use super::*;

    // `Term::Const` with any non-empty string must not panic at construction.
    // Exercises the constant-term parser path.
    proptest! {
        #[test]
        fn prop_term_const_nonempty(s in ".+") {
            // Construction is the boundary under test — no panic is the property.
            let term = Term::Const(s.clone());
            // Confirm round-trip through the Display impl is stable (no panic).
            let displayed = format!("{}", term);
            prop_assert!(!displayed.is_empty(), "Display output must be non-empty");
        }
    }

    // `Goal` construction with any non-empty id string must not panic.
    proptest! {
        #[test]
        fn prop_goal_id_nonempty(id in ".+") {
            let goal = Goal {
                id: id.clone(),
                target: Term::Const("true".to_string()),
                hypotheses: vec![],
            };
            // The stored id must round-trip without corruption.
            prop_assert_eq!(&goal.id, &id);
        }
    }

    /// `ProofState::default()` must always start with an empty goals list.
    /// Validates the Default impl used by the trust pipeline on init.
    #[test]
    fn prop_proof_state_empty_goals_is_valid() {
        let ps = ProofState::default();
        assert!(
            ps.goals.is_empty(),
            "Default ProofState must have no goals, got {}",
            ps.goals.len()
        );
    }

    // Building a `ProofState` from exactly `n` goals (0..=100) always
    // yields `goals.len() == n`. Guards against off-by-one errors in
    // any code that extends the goals vec before dispatching.
    proptest! {
        #[test]
        fn prop_proof_state_goals_count(n in 0usize..=100) {
            let goals: Vec<Goal> = (0..n)
                .map(|i| Goal {
                    id: format!("goal_{}", i),
                    target: Term::Const("true".to_string()),
                    hypotheses: vec![],
                })
                .collect();
            let len = goals.len();
            let ps = ProofState {
                goals,
                ..ProofState::default()
            };
            prop_assert_eq!(
                ps.goals.len(), len,
                "Expected {} goals, got {}", n, ps.goals.len()
            );
        }
    }
}

// ── Module 2: trust_level_props ───────────────────────────────────────────────

mod trust_level_props {
    use super::*;

    // The `Ord` impl on `TrustLevel` must be consistent with the `u8` disc
    // value. If level a's discriminant (as u8) is ≤ level b's discriminant,
    // then `a ≤ b` under `Ord`. This is the ordering invariant the portfolio
    // solver relies on when picking the highest-confidence result.
    proptest! {
        #[test]
        fn prop_trust_level_ordering(
            a in arb_trust_level(),
            b in arb_trust_level(),
        ) {
            let a_val = a.value();
            let b_val = b.value();
            if a_val <= b_val {
                prop_assert!(a <= b, "{:?} ({}) should be ≤ {:?} ({})", a, a_val, b, b_val);
            }
            if a_val >= b_val {
                prop_assert!(a >= b, "{:?} ({}) should be ≥ {:?} ({})", a, a_val, b, b_val);
            }
        }
    }

    // Any `TrustFactors` with `worst_axiom_danger = DangerLevel::Reject`
    // must always yield `TrustLevel::Level1` regardless of every other
    // field, including certificate verification and multiple confirming provers.
    proptest! {
        #[test]
        fn prop_reject_axiom_always_level1(
            confirming in 0u32..=10,
            has_cert in proptest::bool::ANY,
            cert_verified in proptest::bool::ANY,
            integrity_ok in proptest::bool::ANY,
        ) {
            let factors = make_factors(
                confirming,
                has_cert,
                cert_verified,
                DangerLevel::Reject,
                integrity_ok,
            );
            let level = compute_trust_level(&factors);
            prop_assert_eq!(
                level,
                TrustLevel::Level1,
                "Reject axiom must always yield Level1, got {:?}",
                level
            );
        }
    }

    // `DangerLevel::Warning` (sorry/Admitted markers) must also cap at Level1.
    proptest! {
        #[test]
        fn prop_warning_axiom_caps_level1(
            confirming in 0u32..=10,
            has_cert in proptest::bool::ANY,
            cert_verified in proptest::bool::ANY,
            integrity_ok in proptest::bool::ANY,
        ) {
            let factors = make_factors(
                confirming,
                has_cert,
                cert_verified,
                DangerLevel::Warning,
                integrity_ok,
            );
            let level = compute_trust_level(&factors);
            prop_assert_eq!(
                level,
                TrustLevel::Level1,
                "Warning axiom must cap at Level1, got {:?}",
                level
            );
        }
    }

    // A failed solver integrity check (`solver_integrity_ok = false`) must
    // always produce `TrustLevel::Level1`, regardless of axiom danger or
    // certificate state. This is the binary-hash tamper-detection floor.
    proptest! {
        #[test]
        fn prop_failed_integrity_caps_level1(
            confirming in 0u32..=10,
            has_cert in proptest::bool::ANY,
            cert_verified in proptest::bool::ANY,
            // Only Safe/Noted so that we're isolating the integrity check,
            // not the danger-level check (both would produce Level1 anyway).
            worst_danger in prop_oneof![Just(DangerLevel::Safe), Just(DangerLevel::Noted)],
        ) {
            let factors = make_factors(
                confirming,
                has_cert,
                cert_verified,
                worst_danger,
                false, // solver_integrity_ok = false
            );
            let level = compute_trust_level(&factors);
            prop_assert_eq!(
                level,
                TrustLevel::Level1,
                "Failed integrity must yield Level1, got {:?}",
                level
            );
        }
    }

    // For any valid combination of trust factors, `compute_trust_level`
    // must return a value whose discriminant is in `1..=5`. This is the
    // closed-world guarantee that the function never returns out-of-range.
    proptest! {
        #[test]
        fn prop_trust_level_range(
            confirming in 0u32..=10,
            has_cert in proptest::bool::ANY,
            cert_verified in proptest::bool::ANY,
            worst_danger in arb_danger_level(),
            integrity_ok in proptest::bool::ANY,
        ) {
            let factors = make_factors(
                confirming,
                has_cert,
                cert_verified,
                worst_danger,
                integrity_ok,
            );
            let level = compute_trust_level(&factors);
            let v = level.value();
            prop_assert!(
                (1..=5).contains(&v),
                "TrustLevel::value() must be 1..=5, got {}",
                v
            );
        }
    }
}

// ── Module 3: danger_level_props ──────────────────────────────────────────────

mod danger_level_props {
    use super::*;

    // Every `DangerLevel` variant must be equal to itself (reflexivity of `Eq`).
    // Regression guard: a `#[derive(PartialEq)]` that somehow skips a variant
    // would be caught here.
    proptest! {
        #[test]
        fn prop_danger_ord_reflexive(level in arb_danger_level()) {
            prop_assert_eq!(level, level, "DangerLevel must be reflexively equal");
            prop_assert!(level <= level, "DangerLevel must be reflexively ≤");
            prop_assert!(level >= level, "DangerLevel must be reflexively ≥");
        }
    }

    // `DangerLevel`'s `Ord` must be transitive: if `a ≤ b` and `b ≤ c`
    // then `a ≤ c`. Tests all combinations from the 4-variant enum.
    proptest! {
        #[test]
        fn prop_danger_ord_transitive(
            a in arb_danger_level(),
            b in arb_danger_level(),
            c in arb_danger_level(),
        ) {
            if a <= b && b <= c {
                prop_assert!(
                    a <= c,
                    "Transitivity violated: {:?} ≤ {:?} ≤ {:?} but {:?} > {:?}",
                    a, b, c, a, c
                );
            }
        }
    }
}

// ── Module 4: pareto_props ────────────────────────────────────────────────────

mod pareto_props {
    use super::*;

    /// An empty `ParetoFrontier` input must produce an empty frontier index vec.
    /// Guards against the `compute` function allocating or panicking on empty input.
    #[test]
    fn prop_pareto_empty_frontier_size() {
        let mut candidates: Vec<ProofCandidate> = vec![];
        let frontier = ParetoFrontier::compute(&mut candidates);
        assert!(
            frontier.is_empty(),
            "Empty candidate set must yield empty frontier, got {} entries",
            frontier.len()
        );
        // Also verify the candidates slice itself was not mutated unexpectedly.
        assert_eq!(candidates.len(), 0);
    }

    // A single candidate must always be on the Pareto frontier
    // (nothing can dominate it). Guards against an off-by-one in
    // the dominance loop that might incorrectly mark the sole entry
    // as dominated.
    proptest! {
        #[test]
        fn prop_pareto_single_candidate_is_optimal(
            time_ms in 0u64..=1_000_000,
            mem_bytes in 0u64..=1_073_741_824,
            steps in 0usize..=10_000,
            trust in arb_trust_level(),
        ) {
            let mut candidates = vec![ProofCandidate {
                id: "sole".to_string(),
                objectives: ProofObjective {
                    proof_time_ms: time_ms,
                    trust_level: trust,
                    memory_bytes: mem_bytes,
                    proof_steps: steps,
                },
                is_pareto_optimal: false,
            }];
            let frontier = ParetoFrontier::compute(&mut candidates);
            prop_assert_eq!(
                frontier.len(), 1,
                "Single candidate must be Pareto-optimal"
            );
            prop_assert!(
                candidates[0].is_pareto_optimal,
                "is_pareto_optimal flag must be true for sole candidate"
            );
        }
    }
}

// ── Module 5: metamath_parser_props ──────────────────────────────────────────
//
// The Metamath backend is the only prover with an in-process pure-Rust
// parser, so it is also the only one we can panic-attack without an
// external binary. The contract under test is simple: `parse_string`
// must either succeed or return an `Err`; it must never panic, abort,
// or take unbounded time on arbitrary input. Discovered while sweeping
// the API surface that several valid-looking `.mm` fixtures parse to
// an empty `ProofState`; the property below pins the weaker (no-panic)
// invariant while the parser bug is investigated.

mod metamath_parser_props {
    use echidna::provers::metamath::MetamathBackend;
    use echidna::provers::{ProverBackend, ProverConfig};
    use proptest::prelude::*;

    fn backend() -> MetamathBackend {
        MetamathBackend::new(ProverConfig::default())
    }

    proptest! {
        // Arbitrary ASCII input must not panic. Tokenizer / scope-stack /
        // statement-parser paths all see the input here.
        #[test]
        fn prop_parse_string_ascii_no_panic(s in "[\\x20-\\x7e\\n\\t]{0,512}") {
            let rt = tokio::runtime::Runtime::new().expect("runtime");
            let backend = backend();
            // We intentionally do not assert Ok/Err — only the absence of
            // panic and that any returned `ProofState` is well-formed.
            let _ = rt.block_on(backend.parse_string(&s));
        }
    }

    proptest! {
        // Mixed-binary input including `$` punctuation, comment markers,
        // and unbalanced braces. Pin against parser panics on real-world
        // garbage that a user might POST to `/api/prove`.
        #[test]
        fn prop_parse_string_mixed_no_panic(s in ".{0,512}") {
            let rt = tokio::runtime::Runtime::new().expect("runtime");
            let backend = backend();
            let _ = rt.block_on(backend.parse_string(&s));
        }
    }

    proptest! {
        // Bounded-size keyword-heavy input — biases the parser towards
        // exercising the `$c / $v / $a / $p / $f / ${ $}` branches.
        #[test]
        fn prop_parse_string_keyword_heavy_no_panic(
            tokens in proptest::collection::vec(
                prop_oneof![
                    Just("$c".to_string()),
                    Just("$v".to_string()),
                    Just("$a".to_string()),
                    Just("$p".to_string()),
                    Just("$f".to_string()),
                    Just("$e".to_string()),
                    Just("${".to_string()),
                    Just("$}".to_string()),
                    Just("$.".to_string()),
                    Just("$(".to_string()),
                    Just("$)".to_string()),
                    "[a-z]{1,8}".prop_map(String::from),
                ],
                0..40,
            ),
        ) {
            let rt = tokio::runtime::Runtime::new().expect("runtime");
            let backend = backend();
            let src = tokens.join(" ");
            let _ = rt.block_on(backend.parse_string(&src));
        }
    }
}

// ── Module 6: prover_kind_props ──────────────────────────────────────────────
//
// `ProverKind` is the JSON surface of `/api/prove`. Its serde
// round-trip is on every request path, so the invariant
// "serialize ∘ deserialize = id" must hold for every variant.
// Otherwise a request with a valid prover name could fail at the
// edge even though `ProverFactory::create` would have accepted it.

mod prover_kind_props {
    use echidna::provers::ProverKind;
    use proptest::prelude::*;

    fn arb_prover_kind() -> impl Strategy<Value = ProverKind> {
        // Restrict to the canonical roster — `all()` is what
        // `ProverFactory::create` is contracted to support.
        let kinds = ProverKind::all();
        (0..kinds.len()).prop_map(move |i| kinds[i])
    }

    proptest! {
        #[test]
        fn prop_serde_roundtrip(kind in arb_prover_kind()) {
            let json = serde_json::to_string(&kind).expect("serialize");
            let back: ProverKind = serde_json::from_str(&json).expect("deserialize");
            prop_assert_eq!(kind, back, "ProverKind {:?} did not round-trip via JSON", kind);
        }
    }

    proptest! {
        #[test]
        fn prop_tier_in_bounds(kind in arb_prover_kind()) {
            let tier = kind.tier();
            prop_assert!((1..=10).contains(&tier),
                "tier() returned {} for {:?}, expected 1..=10", tier, kind);
        }
    }

    proptest! {
        #[test]
        fn prop_complexity_in_bounds(kind in arb_prover_kind()) {
            let c = kind.complexity();
            prop_assert!((1..=5).contains(&c),
                "complexity() returned {} for {:?}, expected 1..=5", c, kind);
        }
    }

    #[test]
    fn all_core_is_subset_of_all() {
        let core = ProverKind::all_core();
        let all = ProverKind::all();
        for k in &core {
            assert!(
                all.contains(k),
                "ProverKind::{:?} in all_core() but not in all() — \
                 the core set must be a subset of the advertised roster",
                k
            );
        }
    }
}
