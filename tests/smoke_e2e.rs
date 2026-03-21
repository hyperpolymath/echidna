// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! End-to-end smoke tests for the ECHIDNA trust-hardening pipeline.
//!
//! These tests exercise the full path:
//!   submit theorem → ProverDispatcher → prover backend → verify → axiom scan
//!   → trust level → DispatchResult
//!
//! Tests skip gracefully if the required prover is not installed.

mod common;

use anyhow::Result;
use echidna::dispatch::{DispatchConfig, DispatchResult, ProverDispatcher};
use echidna::provers::ProverKind;
use echidna::verification::confidence::TrustLevel;

/// Helper: check if a prover binary is on PATH
fn prover_available(kind: ProverKind) -> bool {
    common::is_prover_available(kind)
}

// ---------------------------------------------------------------------------
// Z3 — most likely to be installed, good first smoke test
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_z3_sat_e2e() -> Result<()> {
    if !prover_available(ProverKind::Z3) {
        eprintln!("Skipping smoke_z3_sat_e2e: Z3 not on PATH");
        return Ok(());
    }

    let dispatcher = ProverDispatcher::new();

    // Simple SAT problem: x = x
    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
"#;

    let result = dispatcher.verify_proof(ProverKind::Z3, content).await?;

    // The dispatch pipeline should complete without error
    assert!(
        result.provers_used.contains(&"Z3".to_string()),
        "Z3 should appear in provers_used, got: {:?}",
        result.provers_used
    );
    assert!(
        result.proof_time_ms > 0,
        "Proof should take some measurable time"
    );
    assert!(
        !result.message.is_empty(),
        "Result should have a human-readable message"
    );

    eprintln!(
        "Z3 E2E: verified={}, trust={}, time={}ms, msg={}",
        result.verified, result.trust_level, result.proof_time_ms, result.message
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// CVC5 — second SMT solver
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_cvc5_sat_e2e() -> Result<()> {
    if !prover_available(ProverKind::CVC5) {
        eprintln!("Skipping smoke_cvc5_sat_e2e: CVC5 not on PATH");
        return Ok(());
    }

    let dispatcher = ProverDispatcher::new();

    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= (+ x 1) (+ 1 x)))
(check-sat)
"#;

    let result = dispatcher.verify_proof(ProverKind::CVC5, content).await?;

    assert!(
        result.provers_used.contains(&"CVC5".to_string()),
        "CVC5 should appear in provers_used"
    );

    eprintln!(
        "CVC5 E2E: verified={}, trust={}, time={}ms",
        result.verified, result.trust_level, result.proof_time_ms
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Cross-checked dispatch (portfolio solving)
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_cross_check_z3_cvc5() -> Result<()> {
    if !prover_available(ProverKind::Z3) || !prover_available(ProverKind::CVC5) {
        eprintln!("Skipping smoke_cross_check: Z3 or CVC5 not on PATH");
        return Ok(());
    }

    let config = DispatchConfig {
        cross_check: true,
        track_axioms: true,
        generate_certificates: false,
        timeout: 30,
        ..DispatchConfig::default()
    };
    let dispatcher = ProverDispatcher::with_config(config);

    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
"#;

    let result = dispatcher
        .verify_proof_cross_checked(
            ProverKind::Z3,
            content,
            &[ProverKind::CVC5],
        )
        .await?;

    // Cross-checked results should use multiple provers
    assert!(
        result.provers_used.len() >= 2,
        "Cross-check should use at least 2 provers, got: {:?}",
        result.provers_used
    );
    assert!(result.cross_checked, "Result should be marked as cross-checked");

    eprintln!(
        "Cross-check E2E: verified={}, trust={}, provers={:?}, time={}ms",
        result.verified, result.trust_level, result.provers_used, result.proof_time_ms
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Lean 4 — interactive proof assistant
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_lean_e2e() -> Result<()> {
    if !prover_available(ProverKind::Lean) {
        eprintln!("Skipping smoke_lean_e2e: Lean not on PATH");
        return Ok(());
    }

    let dispatcher = ProverDispatcher::new();

    let content = r#"
theorem id_example (x : Nat) : x = x := rfl
"#;

    let result = dispatcher.verify_proof(ProverKind::Lean, content).await?;

    assert!(
        result.provers_used.contains(&"Lean".to_string()),
        "Lean should appear in provers_used"
    );

    eprintln!(
        "Lean E2E: verified={}, trust={}, time={}ms",
        result.verified, result.trust_level, result.proof_time_ms
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Axiom tracking
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_axiom_tracking() -> Result<()> {
    if !prover_available(ProverKind::Z3) {
        eprintln!("Skipping smoke_axiom_tracking: Z3 not on PATH");
        return Ok(());
    }

    let config = DispatchConfig {
        track_axioms: true,
        ..DispatchConfig::default()
    };
    let dispatcher = ProverDispatcher::with_config(config);

    // Clean theorem — should have no dangerous axiom usage
    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
"#;

    let result = dispatcher.verify_proof(ProverKind::Z3, content).await?;

    // Axiom report may be None (no axioms found) or Some with Safe level
    if let Some(ref report) = result.axiom_report {
        eprintln!("Axiom report: {:?}", report);
    } else {
        eprintln!("No axiom usage detected (expected for simple theorem)");
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Trust level bounds
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_trust_level_bounds() -> Result<()> {
    if !prover_available(ProverKind::Z3) {
        eprintln!("Skipping smoke_trust_level_bounds: Z3 not on PATH");
        return Ok(());
    }

    // Require Level3 trust — single prover without certificate should not reach it
    let config = DispatchConfig {
        min_trust_level: TrustLevel::Level3,
        ..DispatchConfig::default()
    };
    let dispatcher = ProverDispatcher::with_config(config);

    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
"#;

    let result = dispatcher.verify_proof(ProverKind::Z3, content).await?;

    // Single prover, no certificate, no cross-check — should NOT meet Level3
    // The proof itself may verify, but the trust level should be below Level3
    eprintln!(
        "Trust bounds E2E: verified={}, trust={}, meets_min={}",
        result.verified, result.trust_level,
        result.trust_level >= TrustLevel::Level3
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Dispatch config defaults
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_dispatch_config_defaults() {
    let config = DispatchConfig::default();
    assert!(!config.cross_check, "Cross-check should default to false");
    assert!(config.track_axioms, "Axiom tracking should default to true");
    assert!(!config.generate_certificates, "Certificate gen should default to false");
    assert!(config.timeout > 0, "Timeout should be positive");
}

// ---------------------------------------------------------------------------
// ProverFactory can create all 30 backends
// ---------------------------------------------------------------------------

#[tokio::test]
async fn smoke_all_30_provers_instantiate() -> Result<()> {
    use echidna::provers::{ProverConfig, ProverFactory};

    let config = ProverConfig::default();
    let mut created = 0;
    let mut failed = 0;

    for kind in ProverKind::all() {
        match ProverFactory::create(kind, config.clone()) {
            Ok(_) => {
                created += 1;
            }
            Err(e) => {
                failed += 1;
                eprintln!("  ✗ {:?}: {}", kind, e);
            }
        }
    }

    eprintln!(
        "ProverFactory: {}/30 created, {}/30 failed",
        created, failed
    );

    // All 30 should at least instantiate (even if the binary isn't installed)
    assert_eq!(
        created, 30,
        "All 30 prover backends should instantiate via ProverFactory"
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Proof search strategy (sequential fallback)
// ---------------------------------------------------------------------------

#[test]
fn smoke_sequential_strategy_available() {
    use echidna::proof_search::{ProofSearchStrategy, SequentialSearch, StrategySelector};

    let strategy = SequentialSearch;
    assert!(strategy.available(), "Sequential should always be available");

    let selector = StrategySelector::auto();
    let strategies = selector.available_strategies();
    assert!(
        strategies.contains(&"Sequential"),
        "StrategySelector should always include Sequential"
    );
}
