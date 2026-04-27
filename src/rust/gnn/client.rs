// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

#![forbid(unsafe_code)]

//! GNN inference client for the Julia ML server
//!
//! Serialises a [`ProofGraph`] and sends it to the Julia EchidnaML server
//! for GNN-based premise ranking. The server runs the full GNN pipeline:
//! GCN/GAT message passing -> cross-attention -> MLP scoring.
//!
//! Protocol:
//! - POST `/gnn/rank` — send proof graph, receive ranked premise scores
//! - POST `/gnn/embed` — send proof graph, receive node embeddings
//! - GET  `/gnn/health` — check GNN model availability
//!
//! The client gracefully degrades: if the Julia server is unavailable,
//! it returns empty results rather than failing, allowing the proof search
//! to continue with other heuristics (neural text-based, symbolic).

use anyhow::{bail, Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use tracing::{debug, info, warn};

use crate::gnn::graph::ProofGraph;

/// Configuration for the GNN inference client.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GnnConfig {
    /// Julia ML server URL (default: http://localhost:8081)
    pub api_url: String,
    /// Request timeout in milliseconds
    pub timeout_ms: u64,
    /// Maximum number of premises to rank (top-k)
    pub top_k: usize,
    /// Minimum score threshold for returned premises
    pub min_score: f32,
    /// Whether to request full node embeddings (larger response)
    pub request_embeddings: bool,
    /// Number of GNN message-passing layers to use (server-side config hint)
    pub num_gnn_layers: usize,
    /// Whether to use Graph Attention (GAT) vs plain GCN (server-side hint)
    pub use_attention: bool,
}

impl Default for GnnConfig {
    fn default() -> Self {
        Self {
            api_url: "http://localhost:8081".to_string(),
            timeout_ms: 10_000,
            top_k: 20,
            min_score: 0.05,
            request_embeddings: false,
            num_gnn_layers: 4,
            use_attention: true,
        }
    }
}

/// Request payload sent to the Julia GNN endpoint.
#[derive(Debug, Serialize)]
struct GnnRankRequest {
    /// The proof graph in JSON format
    graph: GnnGraphPayload,
    /// Number of top premises to return
    top_k: usize,
    /// Minimum score threshold
    min_score: f32,
    /// Whether to include node embeddings in response
    include_embeddings: bool,
    /// GNN configuration hints for the server
    config: GnnServerHints,
    /// Optional domain-aspect tags for the goal (e.g. `["arithmetic.factorisation"]`).
    /// When non-empty, Julia uses accumulated training weights for these domains
    /// to modulate premise scores.  Empty for backwards-compatible callers.
    #[serde(default)]
    domain_hints: Vec<String>,
}

/// Serialised proof graph for the Julia server.
///
/// Matches the expected input format for `build_theorem_graph` in
/// `src/julia/models/neural_solver.jl`.
#[derive(Debug, Serialize)]
struct GnnGraphPayload {
    /// Number of nodes
    num_nodes: usize,
    /// Number of edges
    num_edges: usize,
    /// Sparse adjacency: row indices (0-indexed)
    edge_src: Vec<usize>,
    /// Sparse adjacency: column indices (0-indexed)
    edge_dst: Vec<usize>,
    /// Edge weights
    edge_weights: Vec<f32>,
    /// Edge kind labels (for relation-aware message passing)
    edge_kinds: Vec<String>,
    /// Node feature matrix (row-major, shape: num_nodes x feature_dim)
    node_features: Vec<f32>,
    /// Feature dimension per node
    feature_dim: usize,
    /// Node kind labels
    node_kinds: Vec<String>,
    /// Node labels (human-readable)
    node_labels: Vec<String>,
    /// Index of the goal node (if present)
    goal_node_idx: Option<usize>,
    /// Indices of premise nodes (for ranking)
    premise_node_indices: Vec<usize>,
}

/// Server-side configuration hints included in the request.
#[derive(Debug, Serialize)]
struct GnnServerHints {
    num_gnn_layers: usize,
    use_attention: bool,
}

/// Response from the Julia GNN ranking endpoint.
#[derive(Debug, Deserialize)]
struct GnnRankResponse {
    /// Whether the request succeeded
    success: bool,
    /// Ranked premise scores (parallel to `premise_names`)
    scores: Vec<f32>,
    /// Names of ranked premises
    premise_names: Vec<String>,
    /// Optional: node embeddings (if requested)
    #[serde(default)]
    embeddings: Option<Vec<Vec<f32>>>,
    /// Inference time in milliseconds
    #[serde(default)]
    inference_time_ms: f32,
    /// Error message (if success is false)
    #[serde(default)]
    error: Option<String>,
}

/// GNN health check response.
#[derive(Debug, Deserialize)]
struct GnnHealthResponse {
    /// Server status
    status: String,
    /// Whether the GNN model is loaded
    gnn_model_loaded: bool,
    /// Number of GNN layers in the loaded model
    #[serde(default)]
    num_gnn_layers: usize,
}

/// Result of a GNN inference call.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GnnInferenceResult {
    /// Premise names ranked by score (highest first)
    pub ranked_premises: Vec<String>,
    /// Corresponding scores (parallel to `ranked_premises`)
    pub scores: Vec<f32>,
    /// Optional: node embeddings from the GNN (if requested)
    pub node_embeddings: Option<Vec<Vec<f32>>>,
    /// Server-reported inference time in milliseconds
    pub inference_time_ms: f32,
    /// Whether the result came from the GNN server (vs fallback)
    pub from_server: bool,
}

/// Client for GNN-based proof graph inference.
///
/// Communicates with the Julia EchidnaML server to rank premises
/// using Graph Neural Networks. Falls back gracefully when the
/// server is unavailable.
pub struct GnnClient {
    /// Client configuration
    config: GnnConfig,
    /// HTTP client (reusable, connection-pooled)
    client: Client,
    /// Whether the server was reachable on last check
    server_available: bool,
}

impl GnnClient {
    /// Create a new GNN client with default configuration.
    pub fn new() -> Self {
        Self::with_config(GnnConfig::default())
    }

    /// Create a new GNN client with custom configuration.
    pub fn with_config(config: GnnConfig) -> Self {
        let client = Client::builder()
            .timeout(Duration::from_millis(config.timeout_ms))
            .build()
            .expect("Failed to create HTTP client for GNN inference");

        Self {
            config,
            client,
            server_available: false,
        }
    }

    /// Check if the GNN server is available and has a loaded model.
    ///
    /// Updates `server_available` state. Call this before making
    /// inference requests to avoid unnecessary timeouts.
    pub async fn check_health(&mut self) -> Result<bool> {
        let url = format!("{}/gnn/health", self.config.api_url);

        match self.client.get(&url).send().await {
            Ok(response) => {
                if response.status().is_success() {
                    let health: GnnHealthResponse = response
                        .json()
                        .await
                        .context("Failed to parse GNN health response")?;
                    self.server_available = health.gnn_model_loaded;
                    info!(
                        "GNN server status: {}, model_loaded: {}, layers: {}",
                        health.status, health.gnn_model_loaded, health.num_gnn_layers
                    );
                    Ok(health.gnn_model_loaded)
                } else {
                    warn!("GNN server returned error status: {}", response.status());
                    self.server_available = false;
                    Ok(false)
                }
            },
            Err(e) => {
                debug!("GNN server not available: {}", e);
                self.server_available = false;
                Ok(false)
            },
        }
    }

    /// Rank premises in a proof graph using the GNN server.
    ///
    /// Sends the proof graph to the Julia ML server, which runs
    /// GNN message passing + cross-attention + MLP scoring.
    ///
    /// Returns `GnnInferenceResult` with ranked premises and scores.
    /// If the server is unavailable, returns an empty result with
    /// `from_server: false`.
    pub async fn rank_premises(&self, graph: &ProofGraph) -> GnnInferenceResult {
        self.rank_premises_with_aspects(graph, &[]).await
    }

    /// Rank premises with goal-aspect hints for weight-guided scoring.
    ///
    /// Identical to [`rank_premises`] but populates the `domain_hints` field
    /// in the request so Julia can apply accumulated training weights from
    /// `PROVER_DOMAIN_WEIGHTS` (updated by `POST /training/update`).  This
    /// activates the closed-loop feedback path: prior proof outcomes on the
    /// same domain influence current premise scoring.
    ///
    /// Pass an empty slice for behaviour identical to [`rank_premises`].
    pub async fn rank_premises_with_aspects(
        &self,
        graph: &ProofGraph,
        aspects: &[String],
    ) -> GnnInferenceResult {
        if !self.server_available {
            debug!("GNN server not available, returning empty ranking");
            return GnnInferenceResult {
                ranked_premises: Vec::new(),
                scores: Vec::new(),
                node_embeddings: None,
                inference_time_ms: 0.0,
                from_server: false,
            };
        }

        match self.call_rank_api(graph, aspects).await {
            Ok(result) => result,
            Err(e) => {
                warn!("GNN ranking failed: {}", e);
                GnnInferenceResult {
                    ranked_premises: Vec::new(),
                    scores: Vec::new(),
                    node_embeddings: None,
                    inference_time_ms: 0.0,
                    from_server: false,
                }
            },
        }
    }

    /// Internal: call the /gnn/rank endpoint.
    async fn call_rank_api(
        &self,
        graph: &ProofGraph,
        aspects: &[String],
    ) -> Result<GnnInferenceResult> {
        let payload = self.build_request_payload(graph, aspects);
        let url = format!("{}/gnn/rank", self.config.api_url);

        let response = self
            .client
            .post(&url)
            .json(&payload)
            .send()
            .await
            .context("Failed to send GNN rank request")?;

        if !response.status().is_success() {
            bail!("GNN rank request failed with status: {}", response.status());
        }

        let result: GnnRankResponse = response
            .json()
            .await
            .context("Failed to parse GNN rank response")?;

        if !result.success {
            bail!(
                "GNN rank request returned failure: {}",
                result.error.unwrap_or_else(|| "unknown error".to_string())
            );
        }

        Ok(GnnInferenceResult {
            ranked_premises: result.premise_names,
            scores: result.scores,
            node_embeddings: result.embeddings,
            inference_time_ms: result.inference_time_ms,
            from_server: true,
        })
    }

    /// Build the request payload from a proof graph.
    fn build_request_payload(&self, graph: &ProofGraph, aspects: &[String]) -> GnnRankRequest {
        let (edge_src, edge_dst, edge_weights) = graph.sparse_adjacency();

        let edge_kinds: Vec<String> = graph
            .edges
            .iter()
            .map(|e| format!("{:?}", e.kind))
            .collect();

        let node_kinds: Vec<String> = graph
            .nodes
            .iter()
            .map(|n| format!("{:?}", n.kind))
            .collect();

        let node_labels: Vec<String> = graph.nodes.iter().map(|n| n.label.clone()).collect();

        let feature_dim = graph.nodes.first().map(|n| n.features.len()).unwrap_or(0);

        let goal_node_idx = graph
            .goal_node_id
            .and_then(|id| graph.id_to_index.get(&id).copied());

        let premise_node_indices: Vec<usize> = graph
            .premise_node_ids
            .iter()
            .filter_map(|id| graph.id_to_index.get(id).copied())
            .collect();

        let graph_payload = GnnGraphPayload {
            num_nodes: graph.num_nodes(),
            num_edges: graph.num_edges(),
            edge_src,
            edge_dst,
            edge_weights,
            edge_kinds,
            node_features: graph.feature_matrix(),
            feature_dim,
            node_kinds,
            node_labels,
            goal_node_idx,
            premise_node_indices,
        };

        GnnRankRequest {
            graph: graph_payload,
            top_k: self.config.top_k,
            min_score: self.config.min_score,
            include_embeddings: self.config.request_embeddings,
            config: GnnServerHints {
                num_gnn_layers: self.config.num_gnn_layers,
                use_attention: self.config.use_attention,
            },
            domain_hints: aspects.to_vec(),
        }
    }

    /// Whether the server was available on last health check.
    pub fn is_available(&self) -> bool {
        self.server_available
    }

    /// Get current configuration.
    pub fn config(&self) -> &GnnConfig {
        &self.config
    }

    /// Update configuration (rebuilds HTTP client for new timeout).
    pub fn set_config(&mut self, config: GnnConfig) {
        self.client = Client::builder()
            .timeout(Duration::from_millis(config.timeout_ms))
            .build()
            .expect("Failed to create HTTP client for GNN inference");
        self.config = config;
    }
}

impl Default for GnnClient {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{ProofState, Term};
    use crate::gnn::embeddings::TermFeatureExtractor;
    use crate::gnn::graph::ProofGraphBuilder;

    #[test]
    fn test_gnn_config_default() {
        let config = GnnConfig::default();
        assert_eq!(config.api_url, "http://localhost:8081");
        assert_eq!(config.top_k, 20);
        assert_eq!(config.num_gnn_layers, 4);
        assert!(config.use_attention);
    }

    #[test]
    fn test_gnn_client_creation() {
        let client = GnnClient::new();
        assert!(!client.is_available());
    }

    #[test]
    fn test_build_request_payload() {
        let state = ProofState::new(Term::App {
            func: Box::new(Term::Const("f".to_string())),
            args: vec![Term::Var("x".to_string())],
        });

        let mut builder = ProofGraphBuilder::new(3);
        let mut graph = builder.build_from_proof_state(&state);

        let mut extractor = TermFeatureExtractor::new();
        extractor.extract_features(&mut graph);

        let client = GnnClient::new();
        let payload = client.build_request_payload(&graph, &[]);

        assert_eq!(payload.graph.num_nodes, graph.num_nodes());
        assert_eq!(payload.graph.num_edges, graph.num_edges());
        assert_eq!(payload.graph.edge_src.len(), graph.num_edges());
        assert!(payload.domain_hints.is_empty());

        // With aspects: the same payload but with domain_hints populated
        let aspects = vec!["arithmetic.factorisation".to_string(), "crypto.hash.sha256".to_string()];
        let payload_with = client.build_request_payload(&graph, &aspects);
        assert_eq!(payload_with.domain_hints, aspects);
    }

    #[tokio::test]
    async fn test_rank_premises_no_server() {
        let client = GnnClient::new();
        // Server not available, should return empty result
        let state = ProofState::new(Term::Const("test".to_string()));
        let mut builder = ProofGraphBuilder::new(2);
        let graph = builder.build_from_proof_state(&state);

        let result = client.rank_premises(&graph).await;
        assert!(!result.from_server);
        assert!(result.ranked_premises.is_empty());
    }
}
