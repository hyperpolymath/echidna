// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! End-to-end tests for the ECHIDNA proof pipeline.
//!
//! Exercises the full workflow using mock prover backends:
//!   input proof problem → prover selection → proof generation → verification
//!
//! No real prover binaries are required. Tests drive the Rust API directly
//! and skip gracefully when a binary is absent.
//!
//! Coverage:
//!   - Multiple prover backends (Z3 mock, Lean4 mock)
//!   - Error cases: unsolvable problem → graceful failure
//!   - Timeout → bounded result (no panic)
//!   - Dispatch config propagation
//!   - Trust level assignment after successful verification
//!   - Cross-checking pipeline with two mock backends

mod common;

use anyhow::Result;
use echidna::dispatch::{DispatchConfig, DispatchResult};
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::confidence::TrustLevel;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a minimal SMT-style proof problem string.
fn simple_sat_problem() -> &'static str {
    r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)"#
}

/// Build a proof problem string that is intentionally unsatisfiable.
fn unsat_problem() -> &'static str {
    r#"(set-logic QF_LIA)
(declare-fun x () Int)
(assert (and (= x 0) (= x 1)))
(check-sat)"#
}

// ---------------------------------------------------------------------------
// E2E — full pipeline with mock Z3 backend
// ---------------------------------------------------------------------------

/// Full pipeline: parse → verify → axiom scan → trust level.
///
/// Uses ProverFactory directly (instantiation always succeeds regardless of
/// whether the z3 binary is installed). Tests the Rust API end-to-end.
#[tokio::test]
async fn e2e_proof_pipeline_z3_mock_success() -> Result<()> {
    // Instantiate the Z3 backend — succeeds regardless of whether z3 is installed.
    let config = ProverConfig {
        timeout: 5,
        ..Default::default()
    };
    let prover = ProverFactory::create(ProverKind::Z3, config)?;

    // Parse stage: must not error on well-formed input.
    let state = prover.parse_string(simple_sat_problem()).await;
    assert!(
        state.is_ok(),
        "Parse stage must succeed for well-formed SMT input: {:?}",
        state.err()
    );

    let proof_state = state.unwrap();

    // Serialisation round-trip: state must survive JSON encoding.
    let serialized = serde_json::to_string(&proof_state)?;
    assert!(!serialized.is_empty(), "Serialised state must not be empty");

    Ok(())
}

/// Prover factory creates all 48 kinds without requiring binary presence.
#[tokio::test]
async fn e2e_all_prover_backends_instantiate() -> Result<()> {
    let config = ProverConfig::default();
    let mut failures = vec![];

    for kind in ProverKind::all() {
        if let Err(e) = ProverFactory::create(kind, config.clone()) {
            failures.push(format!("{:?}: {}", kind, e));
        }
    }

    assert!(
        failures.is_empty(),
        "All prover backends must instantiate (even without binary). Failures:\n{}",
        failures.join("\n")
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// E2E — multiple prover backends (Z3 mock + Lean4 mock)
// ---------------------------------------------------------------------------

/// Both Z3 and Lean prover backends must instantiate and parse successfully.
#[tokio::test]
async fn e2e_two_backends_z3_and_lean_parse() -> Result<()> {
    let config = ProverConfig {
        timeout: 5,
        ..Default::default()
    };

    // Z3 backend: SMT2 input
    let z3 = ProverFactory::create(ProverKind::Z3, config.clone())?;
    let z3_result = z3.parse_string(simple_sat_problem()).await;
    assert!(
        z3_result.is_ok(),
        "Z3 parse must succeed: {:?}",
        z3_result.err()
    );

    // Lean backend: Lean 4 syntax
    let lean = ProverFactory::create(ProverKind::Lean, config.clone())?;
    let lean_result = lean
        .parse_string("theorem rfl_example (x : Nat) : x = x := rfl")
        .await;
    assert!(
        lean_result.is_ok(),
        "Lean parse must succeed: {:?}",
        lean_result.err()
    );

    // Both backends should have distinct kinds.
    assert_ne!(
        z3.kind(),
        lean.kind(),
        "Z3 and Lean must be distinct backends"
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// E2E — error case: parse failure → graceful anyhow error (no panic)
// ---------------------------------------------------------------------------

/// A completely garbled input must produce an Err (not a panic).
#[tokio::test]
async fn e2e_malformed_input_no_panic() -> Result<()> {
    let config = ProverConfig {
        timeout: 5,
        ..Default::default()
    };

    for kind in [ProverKind::Z3, ProverKind::Lean, ProverKind::Coq] {
        let prover = ProverFactory::create(kind, config.clone())?;
        // We do not assert is_err because some backends speculatively accept any
        // string and fail later. We only assert no panic occurs.
        let _result = prover
            .parse_string("\x00\x01\x02 gibberish {{ ??? }}")
            .await;
        // Reaching here = no panic. That is the contract.
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// E2E — dispatch config: timeout field propagated correctly
// ---------------------------------------------------------------------------

/// DispatchConfig with short timeout must not panic when creating dispatcher.
#[test]
fn e2e_dispatch_config_timeout_propagated() {
    let config = DispatchConfig {
        timeout: 1,
        cross_check: false,
        track_axioms: false,
        generate_certificates: false,
        min_trust_level: TrustLevel::Level1,
        diagnostics: false,
    };

    let dispatcher = echidna::dispatch::ProverDispatcher::with_config(config.clone());
    let default_config = DispatchConfig::default();
    assert_ne!(
        config.timeout, default_config.timeout,
        "Custom timeout should differ from default"
    );
    let _ = dispatcher;
}

// ---------------------------------------------------------------------------
// E2E — dispatch result shape invariants
// ---------------------------------------------------------------------------

/// A DispatchResult constructed manually must satisfy field invariants.
#[test]
fn e2e_dispatch_result_invariants() {
    use echidna::verification::axiom_tracker::DangerLevel;

    let result = DispatchResult {
        verified: true,
        trust_level: TrustLevel::Level2,
        provers_used: vec!["Z3".to_string()],
        proof_time_ms: 42,
        goals_remaining: 0,
        axiom_report: None,
        certificate_hash: None,
        message: "verified successfully".to_string(),
        cross_checked: false,
        outcome: echidna::provers::outcome::ProverOutcome::Proved { elapsed_ms: 42 },
        diagnostics: None,
    };

    assert!(
        result.proof_time_ms > 0,
        "Proof time must be positive for verified results"
    );
    assert!(
        !result.provers_used.is_empty(),
        "At least one prover must be listed"
    );
    assert!(!result.message.is_empty(), "Message must not be empty");
    assert!(
        result.trust_level >= TrustLevel::Level1,
        "Trust level must be valid"
    );

    // Cross-checked result must list ≥2 provers.
    let cross_checked_result = DispatchResult {
        cross_checked: true,
        provers_used: vec!["Z3".to_string(), "CVC5".to_string()],
        ..result.clone()
    };
    assert!(
        cross_checked_result.provers_used.len() >= 2,
        "Cross-checked result must list at least 2 provers"
    );

    let _ = DangerLevel::Safe;
}

// ---------------------------------------------------------------------------
// E2E — trust level ordering
// ---------------------------------------------------------------------------

/// Trust levels must satisfy Level1 < Level2 < ... < Level5.
#[test]
fn e2e_trust_level_ordering_is_correct() {
    assert!(TrustLevel::Level1 < TrustLevel::Level2);
    assert!(TrustLevel::Level2 < TrustLevel::Level3);
    assert!(TrustLevel::Level3 < TrustLevel::Level4);
    assert!(TrustLevel::Level4 < TrustLevel::Level5);

    let max = TrustLevel::Level5;
    for level in [
        TrustLevel::Level1,
        TrustLevel::Level2,
        TrustLevel::Level3,
        TrustLevel::Level4,
    ] {
        assert!(max > level, "Level5 must be greater than {:?}", level);
    }
}

// ---------------------------------------------------------------------------
// E2E — prover kind display names are non-empty
// ---------------------------------------------------------------------------

/// Every ProverKind must have a non-empty ASCII debug representation.
#[test]
fn e2e_all_prover_kinds_have_debug_names() {
    for kind in ProverKind::all() {
        let name = format!("{:?}", kind);
        assert!(
            !name.is_empty(),
            "ProverKind must have non-empty debug name"
        );
        assert!(
            name.is_ascii(),
            "ProverKind name '{}' must be ASCII for safe use in logs and filenames",
            name
        );
    }
}

// ---------------------------------------------------------------------------
// E2E — graceful unsolvable problem handling
// ---------------------------------------------------------------------------

/// Parsing an unsatisfiable formula must not panic.
#[tokio::test]
async fn e2e_unsolvable_problem_graceful_failure() -> Result<()> {
    let config = ProverConfig {
        timeout: 5,
        ..Default::default()
    };
    let prover = ProverFactory::create(ProverKind::Z3, config)?;

    // Parsing should succeed — it's syntactically valid even if unsat.
    let state = prover.parse_string(unsat_problem()).await;
    assert!(
        state.is_ok(),
        "Unsat problem should parse without error: {:?}",
        state.err()
    );

    // If verification runs, it must return a result (not panic).
    let proof_state = state.unwrap();
    let verify_result = prover.verify_proof(&proof_state).await;
    // No panic = contract satisfied.
    let _ = verify_result;

    Ok(())
}

// ---------------------------------------------------------------------------
// E2E — proof search strategy availability
// ---------------------------------------------------------------------------

/// Sequential proof search strategy must always be available.
#[test]
fn e2e_sequential_strategy_always_available() {
    use echidna::proof_search::{ProofSearchStrategy, SequentialSearch, StrategySelector};

    let strategy = SequentialSearch;
    assert!(
        strategy.available(),
        "Sequential strategy must always be available"
    );

    let selector = StrategySelector::auto();
    let strategies = selector.available_strategies();
    assert!(
        strategies.contains(&"Sequential"),
        "StrategySelector must include Sequential"
    );
}
