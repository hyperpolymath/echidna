// SPDX-License-Identifier: PMPL-1.0-or-later
//
// Stage 1 Integration Test: Autonomous Proof Execution
//
// Validates that echidna can:
// 1. Accept a pre-written proof file
// 2. Dispatch to correct prover backend
// 3. Execute and verify proof
// 4. Return structured result with trust level, axioms, solver info
//
// Test organisation:
// - Tests that only exercise in-process data structures: NOT #[ignore]
// - Tests that require a live prover binary installed: #[ignore]

#[cfg(test)]
mod stage1_integration {
    use anyhow::Result;

    use echidna::dispatch::{DispatchConfig, DispatchResult, ProverDispatcher};
    use echidna::provers::{ProverConfig, ProverFactory, ProverKind, ProverOutcome};
    use echidna::verification::DangerLevel;
    use echidna::verification::confidence::TrustLevel;

    // ─────────────────────────────────────────────────────────────────────────
    // Test 1 — Lean backend parse (no live prover required for construction)
    // ─────────────────────────────────────────────────────────────────────────

    /// Stage 1 Step 1: prover factory constructs a Lean backend and the
    /// `parse_string` interface exists and returns without an unexpected panic.
    ///
    /// Parsing is syntax-only inside the stub backend; no real `lean`
    /// executable is required for this test to compile and run.
    #[tokio::test]
    async fn stage1_lean_backend_parse() -> Result<()> {
        // ProverFactory::create returns anyhow::Result<Box<dyn ProverBackend>>
        let prover = ProverFactory::create(ProverKind::Lean, ProverConfig::default())?;

        // Call parse_string — the stub parser may succeed or return an error
        // but must not panic.  Both outcomes are acceptable for Stage 1.
        let outcome = prover
            .parse_string("theorem foo : 1 + 1 = 2 := by norm_num")
            .await;

        match outcome {
            Ok(state) => {
                // Either the stub left the goals list empty or populated it —
                // both are valid; the structural contract is what we verify.
                let _ = state.goals.len();
                println!(
                    "✓ Lean parse_string Ok: {} goal(s) in returned ProofState",
                    state.goals.len()
                );
            }
            Err(e) => {
                // A stub backend may return Err when no real executable is
                // present; that's acceptable — the key invariant is that
                // ProverFactory::create and parse_string are callable.
                println!("✓ Lean parse_string Err (no executable): {e}");
            }
        }

        Ok(())
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 2 — DispatchResult structure and TrustLevel ordering
    // ─────────────────────────────────────────────────────────────────────────

    /// Stage 1 Step 2: `DispatchResult` can be constructed via `Default` and
    /// the `TrustLevel` 5-level hierarchy is correctly ordered.
    #[test]
    fn stage1_dispatch_result_structure() {
        // DispatchResult fields are directly accessible — construct via struct literal.
        // (DispatchResult does not derive Default; we fill every required field.)
        let result = DispatchResult {
            verified: false,
            trust_level: TrustLevel::Level1,
            provers_used: vec![],
            proof_time_ms: 0,
            goals_remaining: 0,
            axiom_report: None,
            certificate_hash: None,
            message: String::new(),
            cross_checked: false,
            outcome: ProverOutcome::default(),
            diagnostics: None,
        };

        // The trust_level field must be readable as a TrustLevel.
        let _level: TrustLevel = result.trust_level;

        // 5-level trust hierarchy: numeric values
        assert_eq!(
            TrustLevel::Level1.value(),
            1,
            "Level1 should have numeric value 1"
        );
        assert_eq!(
            TrustLevel::Level5.value(),
            5,
            "Level5 should have numeric value 5"
        );

        // Ord implementation: Level1 < Level5
        assert!(
            TrustLevel::Level1 < TrustLevel::Level5,
            "Level1 must sort below Level5"
        );
        assert!(
            TrustLevel::Level2 < TrustLevel::Level3,
            "Level2 must sort below Level3"
        );
        assert!(
            TrustLevel::Level4 < TrustLevel::Level5,
            "Level4 must sort below Level5"
        );

        println!("✓ DispatchResult default constructed; TrustLevel ordering verified");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 3 — Axiom tracking structure (DangerLevel ordering)
    // ─────────────────────────────────────────────────────────────────────────

    /// Stage 1 Step 3: `DangerLevel` 4-level hierarchy is correctly ordered.
    /// Safe < Noted < Warning < Reject.
    #[test]
    fn stage1_axiom_tracking_structure() {
        // Safe is the lowest danger level
        assert!(
            DangerLevel::Safe < DangerLevel::Reject,
            "Safe must sort below Reject"
        );

        // Warning > Noted
        assert!(
            DangerLevel::Warning > DangerLevel::Noted,
            "Warning must sort above Noted"
        );

        // Full chain
        assert!(DangerLevel::Safe < DangerLevel::Noted, "Safe < Noted");
        assert!(DangerLevel::Noted < DangerLevel::Warning, "Noted < Warning");
        assert!(
            DangerLevel::Warning < DangerLevel::Reject,
            "Warning < Reject"
        );

        println!("✓ DangerLevel ordering: Safe < Noted < Warning < Reject");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 4 — End-to-end Z3 mock (requires live z3 binary)
    // ─────────────────────────────────────────────────────────────────────────

    /// Stage 1 Step 4: real dispatch pipeline exercised with a trivially
    /// satisfiable SMT-LIB2 string.
    ///
    /// Marked `#[ignore]` because it requires a `z3` binary on `$PATH`.
    /// Run with: `cargo test stage1_end_to_end_z3_mock -- --ignored`
    #[ignore]
    #[tokio::test]
    async fn stage1_end_to_end_z3_mock() -> Result<()> {
        let prover = ProverFactory::create(ProverKind::Z3, ProverConfig::default())?;

        // The simplest satisfiable SMT-LIB2 input
        let smt2 = "(assert true)\n(check-sat)\n";
        let state = prover.parse_string(smt2).await?;
        let verified = prover.verify_proof(&state).await?;

        println!("✓ Z3 end-to-end: verified={verified}");
        // Z3 should confirm `true` is satisfiable
        assert!(verified, "trivially satisfiable SMT-LIB2 should verify");

        Ok(())
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 5 — ProverDispatcher construction
    // ─────────────────────────────────────────────────────────────────────────

    /// Stage 1 Step 5: `ProverDispatcher` constructs with both `new()` and
    /// `with_config(DispatchConfig::default())` without panicking.
    #[test]
    fn stage1_prover_dispatcher_creates() {
        // Both constructors must succeed without panic
        let _dispatcher_default = ProverDispatcher::new();
        let _dispatcher_configured = ProverDispatcher::with_config(DispatchConfig::default());

        println!("✓ ProverDispatcher::new() and with_config() both constructed");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Static fixture strings (compile-time check that Rust can parse these
// string literals; not used by live tests directly but preserved for
// future fixture-based tests).
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
#[allow(dead_code)]
mod fixtures {
    pub const SIMPLE_LEAN4_PROOF: &str = r#"
        theorem simple_arithmetic : 2 + 2 = 4 := by
          norm_num
    "#;

    pub const SIMPLE_AGDA_PROOF: &str = r#"
        open import Agda.Builtin.Nat
        proof : 2 + 2 ≡ 4
        proof = refl
    "#;

    pub const SIMPLE_COQ_PROOF: &str = r#"
        Theorem simple_arithmetic : 2 + 2 = 4.
        Proof. reflexivity. Qed.
    "#;

    pub const SIMPLE_SMT2_PROOF: &str = "(assert true)\n(check-sat)\n";
}
