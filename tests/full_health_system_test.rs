// SPDX-License-Identifier: PMPL-1.0-or-later
// Comprehensive health monitoring system end-to-end test

#[cfg(test)]
mod full_health_system_tests {
    use echidna::diagnostics::*;

    /// Test 1: Initial health state
    #[test]
    fn test_initial_health_state() {
        let health = HealthStatus::new();

        // Verify all systems initialized correctly
        assert_eq!(health.prover_health.len(), 0, "No provers tracked yet");
        assert!(!health.gnn_model_health.is_loaded, "GNN not loaded by default");
        assert!(health.gnn_model_health.fallback_active, "Fallback active by default");
        assert_eq!(health.system_degradation, DegradationMode::Normal);
        assert_eq!(health.health_percentage(), 100.0, "Empty state is 100% health");

        // Verify fallback monitor initialized
        assert!(health.gnn_model_health.fallback_monitor.is_some());
        let monitor = health.gnn_model_health.fallback_monitor.as_ref().unwrap();
        assert_eq!(monitor.total_invocations, 0);
        assert!(monitor.is_healthy(), "Empty monitor is healthy");
    }

    /// Test 2: Prover failure tracking → circuit breaker → degradation
    #[test]
    fn test_prover_failure_cascade() {
        let mut health = HealthStatus::new();

        // Load GNN so it doesn't trigger CosineOnly
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;

        // Simulate 3 consecutive failures on Z3
        let name = "Z3".to_string();
        health.prover_health.insert(
            name.clone(),
            ProverHealth {
                name: name.clone(),
                is_available: true,
                circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                last_successful_proof: None,
                consecutive_failures: 3,
                avg_latency_ms: 100.0,
                success_rate: 0.2,
                total_invocations: 3,
                total_failures: 3,
            },
        );

        // Mark as unavailable after circuit breaker opens
        health.prover_health.get_mut("Z3").unwrap().is_available = false;
        health.prover_health.get_mut("Z3").unwrap().circuit_breaker_state = CircuitBreakerStateSnapshot::Open;

        health.compute_degradation_mode();

        // With 1 prover and none available: ReadOnly (fewer than 3 provers available)
        assert_eq!(health.system_degradation, DegradationMode::ReadOnly);
        assert!(!health.prover_health["Z3"].is_available);
        assert_eq!(health.prover_health["Z3"].consecutive_failures, 3);
    }

    /// Test 3: NeSy agreement validation → fallback activation
    #[test]
    fn test_nesy_agreement_gates_fallback() {
        let mut health = HealthStatus::new();

        // Load GNN model
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;

        // Set poor NeSy agreement (< 0.75)
        health.gnn_model_health.nesy_metrics = Some(NeSyMetrics {
            total_contracts: 100,
            total_agreements: 70, // 70% agreement
            agreement_rate: 0.70,
            false_positive_rate: 0.15,
            false_negative_rate: 0.08,
            provers_tested: vec!["Coq".to_string()],
        });

        // Add enough provers to avoid ReadOnly trigger
        for i in 0..5 {
            health.prover_health.insert(
                format!("Prover{}", i),
                ProverHealth {
                    name: format!("Prover{}", i),
                    is_available: true,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                    last_successful_proof: None,
                    consecutive_failures: 0,
                    avg_latency_ms: 50.0,
                    success_rate: 0.9,
                    total_invocations: 10,
                    total_failures: 1,
                },
            );
        }

        health.compute_degradation_mode();

        // Poor NeSy agreement should trigger CosineOnly
        assert_eq!(health.system_degradation, DegradationMode::CosineOnly);
        assert!(health.gnn_model_health.fallback_active);
    }

    /// Test 4: Fallback SLA violations → degradation
    #[test]
    fn test_fallback_sla_violation_triggers_degradation() {
        let mut health = HealthStatus::new();

        // Create a fallback monitor with violations
        let mut monitor = FallbackMonitor::new(Default::default());
        for _ in 0..9 {
            monitor.record_invocation(FallbackInvocation {
                latency_ms: 30.0,
                cache_hit: true,
                premises_scored: 100,
                met_sla: true,
            });
        }
        // Add one violation
        monitor.record_invocation(FallbackInvocation {
            latency_ms: 100.0,
            cache_hit: false,
            premises_scored: 100,
            met_sla: false,
        });

        health.gnn_model_health.fallback_monitor = Some(monitor);
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;

        // Add provers
        for i in 0..5 {
            health.prover_health.insert(
                format!("Prover{}", i),
                ProverHealth {
                    name: format!("Prover{}", i),
                    is_available: true,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                    last_successful_proof: None,
                    consecutive_failures: 0,
                    avg_latency_ms: 50.0,
                    success_rate: 0.95,
                    total_invocations: 10,
                    total_failures: 0,
                },
            );
        }

        health.compute_degradation_mode();

        // Fallback SLA violations (10%) → IncreasingFallback
        assert_eq!(health.system_degradation, DegradationMode::IncreasingFallback);
    }

    /// Test 5: Healthy state with good metrics
    #[test]
    fn test_healthy_system_state() {
        let mut health = HealthStatus::new();

        // Good GNN health
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;
        health.gnn_model_health.last_validation_nDCG = 0.85;
        health.gnn_model_health.nesy_metrics = Some(NeSyMetrics {
            total_contracts: 100,
            total_agreements: 90, // 90% agreement
            agreement_rate: 0.90,
            false_positive_rate: 0.05,
            false_negative_rate: 0.03,
            provers_tested: vec!["Coq".to_string(), "Lean".to_string()],
        });

        // Good fallback monitor
        let mut fallback = FallbackMonitor::new(Default::default());
        for _ in 0..10 {
            fallback.record_invocation(FallbackInvocation {
                latency_ms: 25.0,
                cache_hit: true,
                premises_scored: 100,
                met_sla: true,
            });
        }
        health.gnn_model_health.fallback_monitor = Some(fallback);
        health.gnn_model_health.fallback_cache_hit_rate = 0.95;

        // All provers healthy
        for i in 0..5 {
            health.prover_health.insert(
                format!("Prover{}", i),
                ProverHealth {
                    name: format!("Prover{}", i),
                    is_available: true,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                    last_successful_proof: Some(chrono::Utc::now()),
                    consecutive_failures: 0,
                    avg_latency_ms: 40.0,
                    success_rate: 0.98,
                    total_invocations: 100,
                    total_failures: 2,
                },
            );
        }

        health.compute_degradation_mode();

        // All systems healthy → Normal
        assert_eq!(health.system_degradation, DegradationMode::Normal);
        assert!(!health.is_degraded());

        // Health percentage should be high
        let health_pct = health.health_percentage();
        assert!(health_pct > 90.0, "Expected >90% health, got {}%", health_pct);
    }

    /// Test 6: Circuit breaker state transitions
    #[test]
    fn test_multiple_circuit_breakers_open() {
        let mut health = HealthStatus::new();

        // Load GNN so it doesn't trigger CosineOnly
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;

        // Multiple provers with open circuit breakers
        for i in 0..2 {
            health.prover_health.insert(
                format!("Prover{}", i),
                ProverHealth {
                    name: format!("Prover{}", i),
                    is_available: false,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Open,
                    last_successful_proof: None,
                    consecutive_failures: 3,
                    avg_latency_ms: 100.0,
                    success_rate: 0.0,
                    total_invocations: 10,
                    total_failures: 10,
                },
            );
        }

        // Add a few healthy provers to avoid ReadOnly
        for i in 2..5 {
            health.prover_health.insert(
                format!("Prover{}", i),
                ProverHealth {
                    name: format!("Prover{}", i),
                    is_available: true,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                    last_successful_proof: None,
                    consecutive_failures: 0,
                    avg_latency_ms: 50.0,
                    success_rate: 0.9,
                    total_invocations: 10,
                    total_failures: 1,
                },
            );
        }

        health.compute_degradation_mode();

        // Multiple open circuits (≥2) → IncreasingFallback
        assert_eq!(health.system_degradation, DegradationMode::IncreasingFallback);

        // Critical provers identified
        let critical = health.critical_provers();
        assert_eq!(critical.len(), 2, "Expected 2 critical provers");
    }

    /// Test 7: Health summary reporting
    #[test]
    fn test_health_summary() {
        let mut health = HealthStatus::new();

        // Setup mixed health state
        health.prover_health.insert(
            "Coq".to_string(),
            ProverHealth {
                name: "Coq".to_string(),
                is_available: true,
                circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                last_successful_proof: None,
                consecutive_failures: 0,
                avg_latency_ms: 50.0,
                success_rate: 0.95,
                total_invocations: 20,
                total_failures: 1,
            },
        );

        health.prover_health.insert(
            "Lean".to_string(),
            ProverHealth {
                name: "Lean".to_string(),
                is_available: false,
                circuit_breaker_state: CircuitBreakerStateSnapshot::Open,
                last_successful_proof: None,
                consecutive_failures: 3,
                avg_latency_ms: 100.0,
                success_rate: 0.0,
                total_invocations: 5,
                total_failures: 5,
            },
        );

        health.compute_degradation_mode();

        // Get summary string
        let summary = health.summary();

        // Verify summary contains expected information
        assert!(summary.contains("echidna health"), "Summary should start with echidna health");
        assert!(summary.contains("2 provers"), "Should report 2 provers");
        assert!(summary.contains("1 failed"), "Should report 1 failed prover");
        assert!(summary.contains("1 critical"), "Should report 1 critical prover");
        assert!(summary.contains("degradation:"), "Should include degradation mode");
    }

    /// Test 8: Corpus health tracking
    #[test]
    fn test_corpus_health_tracking() {
        let mut health = HealthStatus::new();

        health.corpus_health.total_proofs = 1000;
        health.corpus_health.total_premises = 5000;
        health.corpus_health.size_mb = 100.5;
        health.corpus_health.size_change_percent = 5.2;

        assert_eq!(health.corpus_health.total_proofs, 1000);
        assert_eq!(health.corpus_health.total_premises, 5000);
        assert!((health.corpus_health.size_mb - 100.5).abs() < 0.01);
    }

    /// Test 9: Cache fullness detection in fallback monitor
    #[test]
    fn test_fallback_cache_fullness() {
        let config = FallbackSLAConfig {
            max_cache_size: 10_000,
            ..Default::default()
        };
        let mut monitor = FallbackMonitor::new(config);

        // Empty cache
        monitor.set_cache_size(0);
        assert!(!monitor.cache_full());

        // 90% full (below threshold)
        monitor.set_cache_size(9000);
        assert!(!monitor.cache_full());

        // 95% full (at threshold)
        monitor.set_cache_size(9500);
        assert!(monitor.cache_full());

        // Overfull
        monitor.set_cache_size(10_500);
        assert!(monitor.cache_full());
    }

    /// Test 10: NeSy verification gate
    #[test]
    fn test_nesy_verification_gate() {
        let metrics_good = NeSyMetrics {
            total_contracts: 100,
            total_agreements: 80,
            agreement_rate: 0.80,
            false_positive_rate: 0.05,
            false_negative_rate: 0.02,
            provers_tested: vec!["Coq".to_string()],
        };

        let metrics_bad = NeSyMetrics {
            total_contracts: 100,
            total_agreements: 70,
            agreement_rate: 0.70,
            false_positive_rate: 0.15,
            false_negative_rate: 0.08,
            provers_tested: vec!["Coq".to_string()],
        };

        // Good metrics: can claim verified
        assert!(
            can_claim_gnn_verified(&metrics_good),
            "Good metrics should pass verification gate"
        );

        // Bad agreement: fails gate
        assert!(
            !can_claim_gnn_verified(&metrics_bad),
            "Low agreement should fail gate"
        );
    }
}
