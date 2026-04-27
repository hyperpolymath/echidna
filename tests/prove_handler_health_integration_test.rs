// SPDX-License-Identifier: PMPL-1.0-or-later
// Integration test: prove_handler records health metrics on proof attempts

#[cfg(test)]
mod prove_handler_health_tests {
    use echidna::dispatch::ProverDispatcher;
    use echidna::diagnostics::DegradationMode;
    use echidna::ProverKind;
    use std::sync::Arc;

    /// Test: Prove handler integration with health recording
    /// Verifies that calling record_prover_result updates HealthStatus
    #[test]
    fn test_prover_result_recording_updates_health() {
        let dispatcher = Arc::new(ProverDispatcher::new());

        // Initial health: no provers tracked
        let initial_health = dispatcher.health_status();
        assert_eq!(initial_health.prover_health.len(), 0);
        // GNN is not loaded by default, so degradation is CosineOnly
        assert_eq!(initial_health.system_degradation, DegradationMode::CosineOnly);

        // Record a successful proof for Z3
        use echidna::provers::ProverOutcome;
        let z3_success = ProverOutcome::Proved {
            elapsed_ms: 45,
        };
        dispatcher.record_prover_result(ProverKind::Z3, &z3_success, 45);

        // After recording, health should track Z3
        let updated_health = dispatcher.health_status();
        assert_eq!(updated_health.prover_health.len(), 1);
        assert!(updated_health.prover_health.contains_key("Z3"));

        let z3_health = &updated_health.prover_health["Z3"];
        assert!(z3_health.is_available, "Z3 should be available after success");
        assert_eq!(z3_health.total_invocations, 1);
        assert_eq!(z3_health.consecutive_failures, 0);
        assert!(z3_health.last_successful_proof.is_some());

        // Record a failed proof for Coq
        let coq_failure = ProverOutcome::NoProofFound {
            elapsed_ms: 120,
            reason: Some("No proof found".to_string()),
        };
        dispatcher.record_prover_result(ProverKind::Coq, &coq_failure, 120);

        // After second recording, health tracks both
        let final_health = dispatcher.health_status();
        assert_eq!(final_health.prover_health.len(), 2);

        let coq_health = &final_health.prover_health["Coq"];
        assert!(coq_health.is_available, "Coq should be available after single NoProofFound");
        assert_eq!(coq_health.total_invocations, 1);
        assert_eq!(coq_health.total_failures, 1, "NoProofFound counts as a failure");
        assert_eq!(coq_health.consecutive_failures, 0, "NoProofFound doesn't increment consecutive (only real errors do)");

        // Verify Z3 metrics unchanged
        let z3_health_final = &final_health.prover_health["Z3"];
        assert_eq!(z3_health_final.total_invocations, 1);
    }

    /// Test: Prover failures trigger degradation
    /// After 3+ consecutive failures, prover is marked unavailable
    #[test]
    fn test_accumulated_failures_trigger_unavailability() {
        let dispatcher = Arc::new(ProverDispatcher::new());

        use echidna::provers::ProverOutcome;

        // Simulate 3 failures for Lean
        for i in 1..=3 {
            let failure = ProverOutcome::ProverError {
                detail: format!("Prover crash {}", i),
                exit_code: Some(1),
            };
            dispatcher.record_prover_result(ProverKind::Lean, &failure, 30);
        }

        let health = dispatcher.health_status();
        let lean_health = &health.prover_health["Lean"];
        
        // After 3 failures, is_available should be false
        assert!(!lean_health.is_available, "Lean should be unavailable after 3 failures");
        assert_eq!(lean_health.consecutive_failures, 3);
        assert_eq!(lean_health.total_failures, 3);
        assert_eq!(lean_health.total_invocations, 3);
    }

    /// Test: Latency tracking with EMA
    /// Verifies exponential moving average latency calculation
    #[test]
    fn test_latency_ema_tracking() {
        let dispatcher = Arc::new(ProverDispatcher::new());

        use echidna::provers::ProverOutcome;

        // First invocation: 50ms
        let outcome1 = ProverOutcome::Proved { elapsed_ms: 50 };
        dispatcher.record_prover_result(ProverKind::Isabelle, &outcome1, 50);

        let health1 = dispatcher.health_status();
        let isabelle1 = &health1.prover_health["Isabelle"];
        // EMA: 0.8 * 0.0 + 0.2 * 50.0 = 10.0
        assert!((isabelle1.avg_latency_ms - 10.0).abs() < 0.1);

        // Second invocation: 100ms
        let outcome2 = ProverOutcome::Proved { elapsed_ms: 100 };
        dispatcher.record_prover_result(ProverKind::Isabelle, &outcome2, 100);

        let health2 = dispatcher.health_status();
        let isabelle2 = &health2.prover_health["Isabelle"];
        // EMA: 0.8 * 10.0 + 0.2 * 100.0 = 8.0 + 20.0 = 28.0
        assert!((isabelle2.avg_latency_ms - 28.0).abs() < 0.1);
        assert_eq!(isabelle2.total_invocations, 2);
    }

    /// Test: Health percentage reflects prover availability
    #[test]
    fn test_health_percentage_with_failures() {
        let dispatcher = Arc::new(ProverDispatcher::new());

        use echidna::provers::ProverOutcome;

        // Add 5 healthy provers
        for i in 0..5 {
            let kind = match i {
                0 => ProverKind::Z3,
                1 => ProverKind::CVC5,
                2 => ProverKind::Coq,
                3 => ProverKind::Lean,
                4 => ProverKind::Isabelle,
                _ => ProverKind::Z3,
            };
            let outcome = ProverOutcome::Proved { elapsed_ms: 50 };
            dispatcher.record_prover_result(kind, &outcome, 50);
        }

        let health = dispatcher.health_status();
        let health_pct = health.health_percentage();

        // With all provers available and success_rate ~0.5 default, health should be good
        assert!(health_pct > 40.0, "Expected >40% health, got {}%", health_pct);
    }
}
