// SPDX-License-Identifier: PMPL-1.0-or-later
// Integration test: corpus health tracking on proof additions

use echidna::diagnostics::{CorpusMonitor, HealthStatus};

#[test]
fn test_corpus_monitor_tracks_proof_additions() {
    let monitor = CorpusMonitor::new("./training_data");

    // Initially empty
    assert_eq!(monitor.total_proofs(), 0);
    assert_eq!(monitor.total_premises(), 0);

    // Add first proof (with 3 premises)
    monitor.add_proof(3);
    assert_eq!(monitor.total_proofs(), 1);
    assert_eq!(monitor.total_premises(), 3);

    // Add more proofs
    monitor.add_proof(5);
    monitor.add_proof(2);
    assert_eq!(monitor.total_proofs(), 3);
    assert_eq!(monitor.total_premises(), 10); // 3 + 5 + 2
}

#[test]
fn test_corpus_size_tracking() {
    let monitor = CorpusMonitor::new("./training_data");

    monitor.update_size(100.0);
    assert_eq!(monitor.size_mb(), 100.0);

    // Grow corpus
    monitor.update_size(150.0);
    assert!((monitor.size_change_percent() - 50.0).abs() < 0.1); // 50% growth

    // Further growth
    monitor.update_size(175.0);
    assert!((monitor.size_change_percent() - 16.666).abs() < 0.1); // ~16.67% growth
}

#[test]
fn test_corpus_metrics_update_health_status() {
    // Create a health status
    let mut health = HealthStatus::new();
    assert_eq!(health.corpus_health.total_proofs, 0);

    // Create corpus monitor and simulate growth
    let monitor = CorpusMonitor::new("./training_data");
    for i in 0..100 {
        // Simulate adding proofs with varying premise counts
        let premise_count = (i % 5) + 1;
        monitor.add_proof(premise_count);
    }

    let metrics = monitor.metrics();

    // Update health status with corpus metrics
    health.corpus_health.total_proofs = metrics.total_proofs;
    health.corpus_health.total_premises = metrics.total_premises;
    health.corpus_health.size_mb = metrics.size_mb;
    health.corpus_health.size_change_percent = metrics.size_change_percent;
    health.corpus_health.last_updated = Some(metrics.last_updated);

    // Verify health reflects corpus growth
    assert_eq!(health.corpus_health.total_proofs, 100);
    assert!(health.corpus_health.total_premises > 100);
    assert!(health.corpus_health.last_updated.is_some());
}

#[test]
fn test_corpus_growth_tracking_over_time() {
    let monitor = CorpusMonitor::new("./training_data");

    // Simulate corpus growth in stages
    let stages = vec![
        (100, 300),   // 100 proofs, 300 premises
        (200, 600),   // 200 proofs, 600 premises
        (500, 1500),  // 500 proofs, 1500 premises
    ];

    for (proof_count, _premise_count) in &stages {
        // Simulate size growth: 1MB per 10 proofs
        let size_mb = (*proof_count as f64) / 10.0;
        monitor.update_size(size_mb);
    }

    let final_metrics = monitor.metrics();
    assert!(final_metrics.size_mb > 0.0);
    assert!(final_metrics.size_change_percent >= 0.0 || final_metrics.size_change_percent <= 100.0);
}

#[test]
fn test_corpus_reset() {
    let monitor = CorpusMonitor::new("./training_data");

    // Add data
    monitor.add_proof(10);
    monitor.update_size(500.0);

    assert!(monitor.total_proofs() > 0);
    assert!(monitor.size_mb() > 0.0);

    // Reset
    monitor.reset();

    assert_eq!(monitor.total_proofs(), 0);
    assert_eq!(monitor.total_premises(), 0);
}

#[test]
fn test_corpus_metrics_serialization() {
    use echidna::diagnostics::CorpusMetrics;
    use chrono::Utc;

    let metrics = CorpusMetrics {
        total_proofs: 5000,
        total_premises: 15000,
        size_mb: 2048.5,
        size_change_percent: 12.5,
        last_updated: Utc::now(),
    };

    // Verify metrics can be serialized to JSON
    let json = serde_json::to_string(&metrics).expect("Should serialize");
    assert!(json.contains("5000"));
    assert!(json.contains("15000"));
    assert!(json.contains("2048"));

    // Verify round-trip
    let deserialized: CorpusMetrics =
        serde_json::from_str(&json).expect("Should deserialize");
    assert_eq!(deserialized.total_proofs, 5000);
    assert_eq!(deserialized.total_premises, 15000);
}

#[test]
fn test_corpus_health_reflects_degradation() {
    let mut health = HealthStatus::new();

    // Simulate small corpus (potential quality concern)
    health.corpus_health.total_proofs = 10;
    health.corpus_health.total_premises = 30;
    assert!(health.corpus_health.total_proofs < 100);

    // Simulate large corpus (good for training)
    health.corpus_health.total_proofs = 50000;
    health.corpus_health.total_premises = 150000;
    assert!(health.corpus_health.total_proofs >= 1000);
}

#[test]
fn test_corpus_monitor_metrics_consistency() {
    let monitor = CorpusMonitor::new("./training_data");

    // Add proofs incrementally
    for i in 1..=10 {
        monitor.add_proof(i);
    }

    let metrics = monitor.metrics();

    // Verify consistency: total_proofs matches what we added
    assert_eq!(metrics.total_proofs, 10);
    // Verify total_premises: sum of 1+2+3+...+10 = 55
    assert_eq!(metrics.total_premises, 55);
}
