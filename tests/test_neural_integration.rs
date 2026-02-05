// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Integration tests for Rust↔Julia neural API
//!
//! These tests require the Julia test server to be running:
//! ```bash
//! julia src/julia/test_server.jl 8081
//! ```

use echidna::core::{ProofState, Term};
use echidna::neural::{NeuralConfig, NeuralSuggester};

/// Test health check against Julia server
#[tokio::test]
#[ignore = "requires Julia test server running on port 8081"]
async fn test_julia_health_check() {
    let config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 5000,
        top_k: 10,
        use_diversity: true,
        estimate_uncertainty: false,
        min_confidence: 0.1,
        use_cache: true,
    };

    let mut suggester = NeuralSuggester::with_config(config);
    let healthy = suggester.check_health().await.unwrap();

    assert!(healthy, "Julia server should report healthy");
    assert!(suggester.is_connected(), "Suggester should be connected after health check");
}

/// Test premise prediction against Julia server
#[tokio::test]
#[ignore = "requires Julia test server running on port 8081"]
async fn test_julia_predict_premises() {
    let config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 5000,
        top_k: 5,
        use_diversity: true,
        estimate_uncertainty: false,
        min_confidence: 0.1,
        use_cache: false,
    };

    let mut suggester = NeuralSuggester::with_config(config);

    // First connect
    let healthy = suggester.check_health().await.unwrap();
    assert!(healthy);

    // Test premise suggestion
    let goal = Term::Const("test_goal".to_string());
    let premises: Vec<(String, Term)> = vec![
        ("lemma_1".to_string(), Term::Const("P → Q".to_string())),
        ("lemma_2".to_string(), Term::Const("Q → R".to_string())),
    ];

    let results = suggester
        .suggest_premises(&goal, &premises, "agda")
        .await
        .unwrap();

    assert!(!results.is_empty(), "Should return some premises");

    // Check scores are in valid range
    for (name, score) in &results {
        assert!(!name.is_empty(), "Premise name should not be empty");
        assert!(*score >= 0.0 && *score <= 1.0, "Score should be in [0, 1]");
    }
}

/// Test tactic suggestion against Julia server
#[tokio::test]
#[ignore = "requires Julia test server running on port 8081"]
async fn test_julia_suggest_tactics() {
    let config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 5000,
        top_k: 10,
        use_diversity: true,
        estimate_uncertainty: false,
        min_confidence: 0.1,
        use_cache: true,
    };

    let mut suggester = NeuralSuggester::with_config(config);

    // First connect
    let healthy = suggester.check_health().await.unwrap();
    assert!(healthy);

    // Create proof state
    let goal = Term::Const("∀x. P(x) → Q(x)".to_string());
    let state = ProofState::new(goal);

    // Get suggestions
    let tactics = suggester.suggest_tactics(&state).await;

    assert!(!tactics.is_empty(), "Should return some tactics");
}

/// Test scored tactic suggestion
#[tokio::test]
#[ignore = "requires Julia test server running on port 8081"]
async fn test_julia_suggest_tactics_scored() {
    let config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 5000,
        top_k: 5,
        use_diversity: true,
        estimate_uncertainty: true,
        min_confidence: 0.0,
        use_cache: false,
    };

    let mut suggester = NeuralSuggester::with_config(config);

    // First connect
    suggester.check_health().await.unwrap();

    // Create proof state
    let goal = Term::Const("goal".to_string());
    let state = ProofState::new(goal);

    // Get scored suggestions
    let scored_tactics = suggester.suggest_tactics_scored(&state).await;

    assert!(!scored_tactics.is_empty(), "Should return scored tactics");

    // Verify scores are reasonable
    for st in &scored_tactics {
        assert!(st.score >= 0.0, "Score should be non-negative");
        assert!(st.score <= 1.0, "Score should not exceed 1.0");
    }
}

/// Test connection failure handling
#[tokio::test]
async fn test_connection_failure_graceful() {
    let config = NeuralConfig {
        api_url: "http://localhost:59999".to_string(), // Non-existent server
        timeout_ms: 1000,
        top_k: 10,
        use_diversity: false,
        estimate_uncertainty: false,
        min_confidence: 0.1,
        use_cache: false,
    };

    let mut suggester = NeuralSuggester::with_config(config);

    // Health check should fail gracefully
    let healthy = suggester.check_health().await.unwrap();
    assert!(!healthy, "Should report unhealthy for non-existent server");
    assert!(!suggester.is_connected());

    // Suggestions should return empty, not error
    let goal = Term::Const("test".to_string());
    let state = ProofState::new(goal);
    let tactics = suggester.suggest_tactics(&state).await;

    assert!(tactics.is_empty(), "Should return empty for disconnected suggester");
}

/// Test configuration updates
#[tokio::test]
async fn test_config_update() {
    let initial_config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 1000,
        top_k: 5,
        use_diversity: false,
        estimate_uncertainty: false,
        min_confidence: 0.5,
        use_cache: true,
    };

    let mut suggester = NeuralSuggester::with_config(initial_config);

    assert_eq!(suggester.config().top_k, 5);
    assert_eq!(suggester.config().timeout_ms, 1000);

    // Update config
    let new_config = NeuralConfig {
        api_url: "http://localhost:8082".to_string(),
        timeout_ms: 3000,
        top_k: 20,
        use_diversity: true,
        estimate_uncertainty: true,
        min_confidence: 0.1,
        use_cache: false,
    };

    suggester.set_config(new_config);

    assert_eq!(suggester.config().top_k, 20);
    assert_eq!(suggester.config().timeout_ms, 3000);
    assert_eq!(suggester.config().api_url, "http://localhost:8082");
}

/// Test multiple prover support
#[tokio::test]
#[ignore = "requires Julia test server running on port 8081"]
async fn test_multiple_provers() {
    let config = NeuralConfig {
        api_url: "http://localhost:8081".to_string(),
        timeout_ms: 5000,
        top_k: 3,
        use_diversity: false,
        estimate_uncertainty: false,
        min_confidence: 0.0,
        use_cache: false,
    };

    let mut suggester = NeuralSuggester::with_config(config);
    suggester.check_health().await.unwrap();

    let goal = Term::Const("test".to_string());
    let premises: Vec<(String, Term)> = vec![
        ("lem1".to_string(), Term::Const("A".to_string())),
    ];

    // Test with different provers
    let provers = ["agda", "coq", "lean", "isabelle", "z3", "hol4"];

    for prover in provers {
        let results = suggester
            .suggest_premises(&goal, &premises, prover)
            .await
            .unwrap();

        // Should return results for all provers
        assert!(
            !results.is_empty(),
            "Should return results for prover: {}",
            prover
        );
    }
}
