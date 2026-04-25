// SPDX-License-Identifier: PMPL-1.0-or-later
// Integration test: fallback_monitor wired to health status tracking

use echidna::core::{Context, Goal, ProofState, Theorem, Term};
use echidna::diagnostics::HealthStatus;
use echidna::gnn::{FallbackMonitor, FallbackSlaConfig, GnnGuidedSearch};

#[tokio::test]
async fn test_fallback_monitor_records_latency() {
    let monitor = FallbackMonitor::new();

    // Simulate cosine similarity fallback operations
    monitor.record_fallback(100, true);   // Cache hit
    monitor.record_fallback(150, true);   // Cache hit
    monitor.record_fallback(200, false);  // Cache miss

    let metrics = monitor.metrics();
    assert_eq!(metrics.total_invocations, 3);
    assert_eq!(metrics.cache_hits, 2);
    assert!(metrics.avg_latency_ms > 100.0 && metrics.avg_latency_ms < 200.0);
}

#[tokio::test]
async fn test_fallback_monitor_sla_compliance() {
    let config = FallbackSlaConfig {
        max_latency_ms: 500,
        min_success_rate: 0.70,
        max_cache_size: 10000,
    };
    let monitor = FallbackMonitor::with_config(config);

    // Simulate normal operations (meeting SLA)
    for _ in 0..10 {
        monitor.record_fallback(150, true);
    }

    assert!(monitor.meets_sla());
    assert!(monitor.cache_hit_rate() >= 0.7);
}

#[tokio::test]
async fn test_guided_search_integrates_fallback_monitor() {
    let mut search = GnnGuidedSearch::new();

    // Create a simple proof state
    let state = ProofState {
        goals: vec![Goal {
            id: "g0".to_string(),
            target: Term::Const("P".to_string()),
            hypotheses: vec![],
        }],
        context: Context {
            theorems: Vec::new(),
            axioms: Vec::new(),
            definitions: Vec::new(),
            variables: Vec::new(),
        },
        proof_script: Vec::new(),
        metadata: std::collections::HashMap::new(),
    };

    // Create test premises
    let premises = vec![
        Theorem {
            name: "lemma_a".to_string(),
            statement: Term::Const("P".to_string()),
            proof: None,
            aspects: vec![],
        },
        Theorem {
            name: "lemma_b".to_string(),
            statement: Term::Const("Q".to_string()),
            proof: None,
            aspects: vec![],
        },
    ];

    // Run guided search (will use fallback since no GNN server)
    let ranked = search.rank_premises(&state, &premises).await;

    // Verify search produced results
    assert!(!ranked.is_empty(), "Guided search should produce ranked premises");

    // Verify fallback monitor recorded activity
    let monitor = search.fallback_monitor();
    let metrics = monitor.metrics();
    assert!(metrics.total_invocations > 0, "Fallback should be invoked");
    // Verify cache size is tracked (may be 0 if embeddings are not cached yet)
    assert!(metrics.cache_size <= 10000, "Cache size should be reasonable");
}

#[tokio::test]
async fn test_fallback_metrics_update_health_status() {
    let mut health = HealthStatus::new();

    // Initially, fallback is not tracked
    assert_eq!(health.gnn_model_health.fallback_cache_hit_rate, 0.0);

    // Simulate fallback monitor recording operations
    let monitor = FallbackMonitor::new();
    for _ in 0..8 {
        monitor.record_fallback(100, true);   // 80% hit rate
    }
    for _ in 0..2 {
        monitor.record_fallback(150, false);  // 20% miss rate
    }
    monitor.set_cache_size(256);

    let metrics = monitor.metrics();

    // Update health status with fallback metrics
    health.gnn_model_health.fallback_active = true;
    health.gnn_model_health.fallback_cache_hit_rate = metrics.cache_hit_rate();
    health.gnn_model_health.fallback_cache_size = metrics.cache_size;
    health.gnn_model_health.fallback_max_latency_ms = metrics.max_latency_ms as f64;

    // Verify health status reflects fallback metrics
    assert!(health.gnn_model_health.fallback_active);
    assert!(health.gnn_model_health.fallback_cache_hit_rate > 0.7);
    assert_eq!(health.gnn_model_health.fallback_cache_size, 256);
    assert!(health.gnn_model_health.fallback_max_latency_ms > 100.0);
}

#[tokio::test]
async fn test_fallback_monitor_cache_growth() {
    let monitor = FallbackMonitor::new();

    // Simulate cache growing over time
    monitor.set_cache_size(100);
    assert_eq!(monitor.metrics().cache_size, 100);

    monitor.set_cache_size(500);
    assert_eq!(monitor.metrics().cache_size, 500);

    monitor.set_cache_size(2000);
    assert_eq!(monitor.metrics().cache_size, 2000);
}

#[tokio::test]
async fn test_fallback_sla_violation_triggers_degradation() {
    let config = FallbackSlaConfig {
        max_latency_ms: 200,
        min_success_rate: 0.80,
        max_cache_size: 10000,
    };
    let monitor = FallbackMonitor::with_config(config);

    // Simulate high-latency fallback operations
    for _ in 0..5 {
        monitor.record_fallback(300, false);  // Exceeds max_latency_ms
    }

    let metrics = monitor.metrics();
    assert!(!metrics.meets_sla);
    assert!(metrics.avg_latency_ms > 200.0);
    assert!(metrics.cache_hit_rate() < 0.8);
}

#[test]
fn test_fallback_metrics_serialization() {
    use echidna::gnn::FallbackMetrics;
    use serde_json;

    let metrics = FallbackMetrics {
        total_invocations: 100,
        cache_hits: 75,
        avg_latency_ms: 125.5,
        max_latency_ms: 300,
        min_latency_ms: 50,
        cache_size: 500,
        meets_sla: true,
    };

    // Verify metrics can be serialized to JSON
    let json = serde_json::to_string(&metrics).expect("Should serialize");
    assert!(json.contains("total_invocations"));
    assert!(json.contains("100"));

    // Verify round-trip
    let deserialized: FallbackMetrics =
        serde_json::from_str(&json).expect("Should deserialize");
    assert_eq!(deserialized.total_invocations, 100);
    assert_eq!(deserialized.cache_hits, 75);
}
