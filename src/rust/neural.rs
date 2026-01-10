// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Neural premise selection and tactic suggestion
//!
//! This module provides integration with the Julia-based ECHIDNA ML system.
//! It communicates with the EchidnaML API server for neural inference.
//!
//! Architecture:
//! - Julia server (EchidnaML) runs on configurable port (default: 8081)
//! - Rust server calls Julia API for neural suggestions
//! - Results converted to Rust types for prover backends

use crate::core::{ProofState, Tactic, Term};
use anyhow::{bail, Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use tracing::{debug, info, warn};

/// Configuration for neural suggester connection
#[derive(Debug, Clone)]
pub struct NeuralConfig {
    /// Julia ML server URL
    pub api_url: String,
    /// Request timeout in milliseconds
    pub timeout_ms: u64,
    /// Number of suggestions to request
    pub top_k: usize,
    /// Whether to use diversity-aware ranking
    pub use_diversity: bool,
    /// Enable uncertainty estimation (slower but more accurate)
    pub estimate_uncertainty: bool,
    /// Minimum confidence threshold
    pub min_confidence: f32,
    /// Enable caching on Julia side
    pub use_cache: bool,
}

impl Default for NeuralConfig {
    fn default() -> Self {
        Self {
            api_url: "http://localhost:8081".to_string(),
            timeout_ms: 5000,
            top_k: 10,
            use_diversity: true,
            estimate_uncertainty: false,
            min_confidence: 0.1,
            use_cache: true,
        }
    }
}

/// Request to Julia ML server for premise prediction
#[derive(Debug, Serialize)]
struct PredictRequest {
    goal: String,
    context: Vec<String>,
    hypotheses: Vec<String>,
    available_premises: Vec<PremiseInfo>,
    prover: String,
    top_k: usize,
    min_confidence: f32,
    use_cache: bool,
}

/// Premise information for ML request
#[derive(Debug, Serialize)]
struct PremiseInfo {
    name: String,
    statement: String,
    frequency_score: f32,
    relevance_score: f32,
}

/// Request to Julia ML server for interactive suggestion
#[derive(Debug, Serialize)]
struct SuggestRequest {
    goal: String,
    context: Vec<String>,
    hypotheses: Vec<String>,
    available_premises: Vec<PremiseInfo>,
    prover: String,
    top_k: usize,
    use_diversity: bool,
    estimate_uncertainty: bool,
}

/// Response from Julia ML server
#[derive(Debug, Deserialize)]
struct PredictResponse {
    success: bool,
    premises: Vec<ScoredPremise>,
    scores: Vec<f32>,
    confidence: f32,
    prover: String,
    #[serde(default)]
    cached: bool,
    #[serde(default)]
    inference_time_ms: f32,
}

/// Scored premise from ML response
#[derive(Debug, Deserialize)]
struct ScoredPremise {
    name: String,
    statement: String,
    score: f32,
    #[serde(default)]
    frequency_score: f32,
    #[serde(default)]
    relevance_score: f32,
}

/// Health check response
#[derive(Debug, Deserialize)]
struct HealthResponse {
    status: String,
    model_loaded: bool,
    uptime_seconds: f64,
    request_count: u64,
}

/// Tactic suggestion with score
#[derive(Debug, Clone)]
pub struct ScoredTactic {
    pub tactic: Tactic,
    pub score: f32,
    pub premise_name: Option<String>,
}

/// Neural premise selection and tactic suggestion
///
/// Integrates with Julia-based EchidnaML for neural inference.
pub struct NeuralSuggester {
    config: NeuralConfig,
    client: Client,
    connected: bool,
}

impl NeuralSuggester {
    /// Create a new neural suggester with default configuration
    pub fn new() -> Self {
        Self::with_config(NeuralConfig::default())
    }

    /// Create a new neural suggester with custom configuration
    pub fn with_config(config: NeuralConfig) -> Self {
        let client = Client::builder()
            .timeout(Duration::from_millis(config.timeout_ms))
            .build()
            .expect("Failed to create HTTP client");

        Self {
            config,
            client,
            connected: false,
        }
    }

    /// Check if Julia ML server is available
    pub async fn check_health(&mut self) -> Result<bool> {
        let url = format!("{}/health", self.config.api_url);

        match self.client.get(&url).send().await {
            Ok(response) => {
                if response.status().is_success() {
                    let health: HealthResponse = response.json().await?;
                    self.connected = health.model_loaded;
                    info!(
                        "Julia ML server connected: status={}, model_loaded={}, uptime={}s",
                        health.status, health.model_loaded, health.uptime_seconds
                    );
                    Ok(health.model_loaded)
                } else {
                    warn!("Julia ML server returned error: {}", response.status());
                    self.connected = false;
                    Ok(false)
                }
            }
            Err(e) => {
                debug!("Julia ML server not available: {}", e);
                self.connected = false;
                Ok(false)
            }
        }
    }

    /// Get suggested tactics based on proof state
    ///
    /// Calls Julia ML server for neural premise selection,
    /// then converts suggestions to Tactic objects.
    pub async fn suggest_tactics(&self, state: &ProofState) -> Vec<Tactic> {
        self.suggest_tactics_scored(state)
            .await
            .into_iter()
            .map(|st| st.tactic)
            .collect()
    }

    /// Get suggested tactics with scores
    pub async fn suggest_tactics_scored(&self, state: &ProofState) -> Vec<ScoredTactic> {
        if !self.connected {
            debug!("Neural suggester not connected, returning empty suggestions");
            return Vec::new();
        }

        match self.call_suggest_api(state).await {
            Ok(suggestions) => suggestions,
            Err(e) => {
                warn!("Neural suggestion failed: {}", e);
                Vec::new()
            }
        }
    }

    /// Get suggested premises for a proof goal
    pub async fn suggest_premises(
        &self,
        goal: &Term,
        available_premises: &[(String, Term)],
        prover: &str,
    ) -> Result<Vec<(String, f32)>> {
        if !self.connected {
            return Ok(Vec::new());
        }

        let request = PredictRequest {
            goal: format!("{:?}", goal),
            context: Vec::new(),
            hypotheses: Vec::new(),
            available_premises: available_premises
                .iter()
                .map(|(name, term)| PremiseInfo {
                    name: name.clone(),
                    statement: format!("{:?}", term),
                    frequency_score: 0.0,
                    relevance_score: 0.0,
                })
                .collect(),
            prover: prover.to_lowercase(),
            top_k: self.config.top_k,
            min_confidence: self.config.min_confidence,
            use_cache: self.config.use_cache,
        };

        let url = format!("{}/predict", self.config.api_url);
        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await
            .context("Failed to send predict request")?;

        if !response.status().is_success() {
            bail!("Predict request failed: {}", response.status());
        }

        let result: PredictResponse = response.json().await?;

        if !result.success {
            bail!("Predict request returned failure");
        }

        Ok(result
            .premises
            .into_iter()
            .map(|p| (p.name, p.score))
            .collect())
    }

    /// Call the Julia suggest API
    async fn call_suggest_api(&self, state: &ProofState) -> Result<Vec<ScoredTactic>> {
        let request = SuggestRequest {
            goal: state
                .goals
                .first()
                .map(|g| format!("{:?}", g.target))
                .unwrap_or_default(),
            context: state
                .context
                .variables
                .iter()
                .map(|v| format!("{}: {:?}", v.name, v.ty))
                .collect(),
            hypotheses: state
                .context
                .theorems
                .iter()
                .map(|t| format!("{}: {:?}", t.name, t.statement))
                .collect(),
            available_premises: Vec::new(), // Would come from theorem database
            prover: "agda".to_string(),     // Default prover
            top_k: self.config.top_k,
            use_diversity: self.config.use_diversity,
            estimate_uncertainty: self.config.estimate_uncertainty,
        };

        let url = format!("{}/suggest", self.config.api_url);
        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await
            .context("Failed to send suggest request")?;

        if !response.status().is_success() {
            bail!("Suggest request failed: {}", response.status());
        }

        let result: PredictResponse = response.json().await?;

        if !result.success {
            bail!("Suggest request returned failure");
        }

        // Convert premises to tactics (Apply is an enum variant)
        let tactics = result
            .premises
            .into_iter()
            .map(|p| ScoredTactic {
                tactic: Tactic::Apply(p.name.clone()),
                score: p.score,
                premise_name: Some(p.name),
            })
            .collect();

        Ok(tactics)
    }

    /// Get current configuration
    pub fn config(&self) -> &NeuralConfig {
        &self.config
    }

    /// Update configuration
    pub fn set_config(&mut self, config: NeuralConfig) {
        self.config = config;
        // Rebuild client with new timeout
        self.client = Client::builder()
            .timeout(Duration::from_millis(self.config.timeout_ms))
            .build()
            .expect("Failed to create HTTP client");
    }

    /// Check if connected to Julia ML server
    pub fn is_connected(&self) -> bool {
        self.connected
    }
}

impl Default for NeuralSuggester {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_neural_config_default() {
        let config = NeuralConfig::default();
        assert_eq!(config.api_url, "http://localhost:8081");
        assert_eq!(config.top_k, 10);
        assert!(config.use_diversity);
    }

    #[test]
    fn test_neural_suggester_creation() {
        let suggester = NeuralSuggester::new();
        assert!(!suggester.is_connected());
        assert_eq!(suggester.config().top_k, 10);
    }

    #[tokio::test]
    async fn test_suggest_tactics_no_connection() {
        let suggester = NeuralSuggester::new();
        // Create a simple goal term for the proof state
        let goal = Term::Const("test_goal".to_string());
        let state = ProofState::new(goal);
        let tactics = suggester.suggest_tactics(&state).await;
        assert!(tactics.is_empty()); // No connection, empty result
    }
}
