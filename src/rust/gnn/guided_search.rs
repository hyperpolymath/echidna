// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

#![forbid(unsafe_code)]

//! GNN-guided proof search strategy
//!
//! Integrates the GNN premise ranking into the proof search loop.
//! The guided search:
//!
//! 1. Builds a proof graph from the current proof state
//! 2. Extracts local features for all nodes
//! 3. Sends the graph to the Julia GNN server for premise ranking
//! 4. Converts ranked premises into scored tactics
//! 5. Combines GNN scores with symbolic heuristics
//!
//! The search strategy supports multiple modes:
//! - **GNN-only**: Pure neural guidance (when server is available)
//! - **Hybrid**: GNN scores combined with symbolic scoring
//! - **Fallback**: Pure symbolic scoring (when server is unavailable)
//!
//! # Integration with Agent Module
//!
//! The `GnnGuidedSearch` is designed to be used by the agent's planner
//! (`src/rust/agent/planner.rs`) as a tactic selector. It produces
//! `ScoredPremise` values that the planner converts to tactics.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Instant;
use tracing::{debug, info};

use crate::core::{ProofState, Tactic, Term, Theorem};
use crate::gnn::client::{GnnClient, GnnConfig};
use crate::gnn::embeddings::{TermEmbedding, TermFeatureExtractor};
use crate::gnn::fallback_monitor::{FallbackMonitor, FallbackSlaConfig};
use crate::gnn::graph::ProofGraphBuilder;

/// Configuration for GNN-guided search.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GuidedSearchConfig {
    /// Maximum depth for proof graph construction
    pub max_graph_depth: u32,
    /// Weight for GNN scores in hybrid mode (0.0 = pure symbolic, 1.0 = pure GNN)
    pub gnn_weight: f32,
    /// Weight for symbolic similarity scores
    pub symbolic_weight: f32,
    /// Maximum number of tactics to return
    pub max_tactics: usize,
    /// Minimum combined score to include a tactic
    pub min_combined_score: f32,
    /// Whether to use cosine similarity as symbolic fallback
    pub use_cosine_fallback: bool,
    /// GNN client configuration
    pub gnn_config: GnnConfig,
}

impl Default for GuidedSearchConfig {
    fn default() -> Self {
        Self {
            max_graph_depth: 4,
            gnn_weight: 0.7,
            symbolic_weight: 0.3,
            max_tactics: 20,
            min_combined_score: 0.05,
            use_cosine_fallback: true,
            gnn_config: GnnConfig::default(),
        }
    }
}

/// A premise scored by the GNN-guided search.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScoredPremise {
    /// Name of the premise (theorem/lemma name)
    pub name: String,
    /// GNN-computed score (0.0 to 1.0, higher = more relevant)
    pub gnn_score: f32,
    /// Symbolic similarity score (cosine similarity of term embeddings)
    pub symbolic_score: f32,
    /// Combined score (weighted average of gnn_score and symbolic_score)
    pub combined_score: f32,
    /// Suggested tactic for applying this premise
    pub suggested_tactic: Tactic,
    /// Whether the GNN score came from the server (vs estimated)
    pub gnn_score_from_server: bool,
}

/// GNN-guided proof search strategy.
///
/// Combines graph neural network inference with local symbolic heuristics
/// to rank available premises and suggest tactics for proof search.
pub struct GnnGuidedSearch {
    /// Configuration
    config: GuidedSearchConfig,
    /// GNN inference client
    gnn_client: GnnClient,
    /// Feature extractor for local embeddings
    feature_extractor: TermFeatureExtractor,
    /// Cache of term embeddings for available premises (avoid recomputation)
    premise_embedding_cache: HashMap<String, TermEmbedding>,
    /// Statistics about search performance
    stats: SearchStats,
    /// Monitor for cosine similarity fallback SLA compliance
    fallback_monitor: FallbackMonitor,
}

/// Statistics about GNN-guided search performance.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SearchStats {
    /// Total number of search calls
    pub total_calls: u64,
    /// Number of calls where GNN server was used
    pub gnn_calls: u64,
    /// Number of calls where symbolic fallback was used
    pub fallback_calls: u64,
    /// Average GNN inference time (milliseconds)
    pub avg_gnn_time_ms: f32,
    /// Average number of premises returned per call
    pub avg_premises_returned: f32,
}

impl GnnGuidedSearch {
    /// Create a new GNN-guided search with default configuration.
    pub fn new() -> Self {
        Self::with_config(GuidedSearchConfig::default())
    }

    /// Create a new GNN-guided search with custom configuration.
    pub fn with_config(config: GuidedSearchConfig) -> Self {
        let gnn_client = GnnClient::with_config(config.gnn_config.clone());
        let fallback_monitor = FallbackMonitor::with_config(FallbackSlaConfig::default());
        Self {
            config,
            gnn_client,
            feature_extractor: TermFeatureExtractor::new(),
            premise_embedding_cache: HashMap::new(),
            stats: SearchStats::default(),
            fallback_monitor,
        }
    }

    /// Check GNN server availability. Call once at startup or periodically.
    pub async fn check_server(&mut self) -> bool {
        match self.gnn_client.check_health().await {
            Ok(available) => {
                if available {
                    info!("GNN server available for guided proof search");
                } else {
                    debug!("GNN server not available, will use symbolic fallback");
                }
                available
            },
            Err(e) => {
                debug!("GNN health check failed: {}", e);
                false
            },
        }
    }

    /// Rank available premises for the current proof state.
    ///
    /// Convenience wrapper around [`rank_premises_with_aspects`] that passes
    /// no domain hints — equivalent to `rank_premises_with_aspects(state, premises, &[])`.
    pub async fn rank_premises(
        &mut self,
        state: &ProofState,
        available_premises: &[Theorem],
    ) -> Vec<ScoredPremise> {
        self.rank_premises_with_aspects(state, available_premises, &[]).await
    }

    /// Rank available premises with goal-aspect hints for closed-loop scoring.
    ///
    /// This is the main entry point. It:
    /// 1. Builds a proof graph from the state
    /// 2. Extracts features
    /// 3. Queries the GNN server (if available), passing `aspects` so Julia
    ///    can apply accumulated `PROVER_DOMAIN_WEIGHTS` from prior outcomes
    /// 4. Computes symbolic scores
    /// 5. Combines and ranks results
    ///
    /// # Arguments
    /// * `state` - Current proof state (goals + context)
    /// * `available_premises` - Theorems that could be applied
    /// * `aspects` - Goal aspect tags (e.g. from `AgenticGoal::aspects`).
    ///   Empty slice = behaviour identical to [`rank_premises`].
    ///
    /// # Returns
    /// Premises ranked by combined score (highest first).
    pub async fn rank_premises_with_aspects(
        &mut self,
        state: &ProofState,
        available_premises: &[Theorem],
        aspects: &[String],
    ) -> Vec<ScoredPremise> {
        self.stats.total_calls += 1;

        // Step 1: Build proof graph
        let mut builder = ProofGraphBuilder::new(self.config.max_graph_depth);
        let mut graph = builder.build_from_proof_state(state);

        // Step 2: Extract features
        self.feature_extractor.extract_features(&mut graph);

        // Step 3: Get GNN scores (if server available); aspects flow through
        // as `domain_hints` so Julia's rank_with_gnn can apply per-domain
        // weights accumulated from past proof outcomes.
        let gnn_result = self
            .gnn_client
            .rank_premises_with_aspects(&graph, aspects)
            .await;

        let gnn_scores: HashMap<String, f32> = if gnn_result.from_server {
            self.stats.gnn_calls += 1;
            self.stats.avg_gnn_time_ms = (self.stats.avg_gnn_time_ms
                * (self.stats.gnn_calls - 1) as f32
                + gnn_result.inference_time_ms)
                / self.stats.gnn_calls as f32;

            gnn_result
                .ranked_premises
                .into_iter()
                .zip(gnn_result.scores.into_iter())
                .collect()
        } else {
            self.stats.fallback_calls += 1;
            HashMap::new()
        };

        // Step 4: Compute symbolic scores using cosine similarity
        let symbolic_scores = self.compute_symbolic_scores(state, available_premises);

        // Step 5: Combine scores and build result
        let mut scored: Vec<ScoredPremise> = available_premises
            .iter()
            .map(|theorem| {
                let gnn_score = gnn_scores.get(&theorem.name).copied().unwrap_or(0.0);
                let symbolic_score = symbolic_scores.get(&theorem.name).copied().unwrap_or(0.0);
                let gnn_from_server = gnn_scores.contains_key(&theorem.name);

                let combined = if gnn_from_server {
                    self.config.gnn_weight * gnn_score
                        + self.config.symbolic_weight * symbolic_score
                } else {
                    // Pure symbolic mode
                    symbolic_score
                };

                ScoredPremise {
                    name: theorem.name.clone(),
                    gnn_score,
                    symbolic_score,
                    combined_score: combined,
                    suggested_tactic: infer_tactic(&theorem.name, &theorem.statement),
                    gnn_score_from_server: gnn_from_server,
                }
            })
            .filter(|sp| sp.combined_score >= self.config.min_combined_score)
            .collect();

        // Sort by combined score descending
        scored.sort_by(|a, b| {
            b.combined_score
                .partial_cmp(&a.combined_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Truncate to max_tactics
        scored.truncate(self.config.max_tactics);

        // Update average premises returned
        let total = self.stats.total_calls as f32;
        self.stats.avg_premises_returned =
            (self.stats.avg_premises_returned * (total - 1.0) + scored.len() as f32) / total;

        scored
    }

    /// Compute symbolic similarity scores between the goal and premises.
    ///
    /// Uses cosine similarity of local term embeddings as a fast heuristic
    /// that works without the GNN server. Tracks latency and cache hits
    /// via fallback_monitor for SLA compliance.
    fn compute_symbolic_scores(
        &mut self,
        state: &ProofState,
        premises: &[Theorem],
    ) -> HashMap<String, f32> {
        let mut scores = HashMap::new();

        if !self.config.use_cosine_fallback {
            return scores;
        }

        let fallback_start = Instant::now();

        // Embed the goal term
        let goal_embedding = state
            .goals
            .first()
            .map(|g| TermEmbedding::from_term(&g.target));

        let goal_emb = match goal_embedding {
            Some(e) => e,
            None => return scores,
        };

        let mut cache_hits = 0;
        let mut cache_misses = 0;

        // Score each premise by cosine similarity to the goal
        for theorem in premises {
            let is_cache_hit = self.premise_embedding_cache.contains_key(&theorem.name);

            let premise_emb = self
                .premise_embedding_cache
                .entry(theorem.name.clone())
                .or_insert_with(|| TermEmbedding::from_term(&theorem.statement))
                .clone();

            if is_cache_hit {
                cache_hits += 1;
            } else {
                cache_misses += 1;
            }

            let similarity = goal_emb.cosine_similarity(&premise_emb);
            scores.insert(theorem.name.clone(), similarity);
        }

        // Record fallback operation metrics
        let fallback_latency_ms = fallback_start.elapsed().as_millis() as u64;
        let is_cache_hit = cache_hits > 0 && cache_misses == 0;
        self.fallback_monitor.record_fallback(fallback_latency_ms, is_cache_hit);
        self.fallback_monitor.set_cache_size(self.premise_embedding_cache.len());

        scores
    }

    /// Get search statistics.
    pub fn stats(&self) -> &SearchStats {
        &self.stats
    }

    /// Reset search statistics.
    pub fn reset_stats(&mut self) {
        self.stats = SearchStats::default();
    }

    /// Clear the premise embedding cache.
    pub fn clear_cache(&mut self) {
        self.premise_embedding_cache.clear();
    }

    /// Get current configuration.
    pub fn config(&self) -> &GuidedSearchConfig {
        &self.config
    }

    /// Whether the GNN server is available.
    pub fn gnn_available(&self) -> bool {
        self.gnn_client.is_available()
    }

    /// Get fallback monitor for accessing SLA metrics
    pub fn fallback_monitor(&self) -> &FallbackMonitor {
        &self.fallback_monitor
    }

    /// Whether fallback is currently meeting SLA
    pub fn fallback_meets_sla(&self) -> bool {
        self.fallback_monitor.meets_sla()
    }

    /// Get fallback cache hit rate
    pub fn fallback_cache_hit_rate(&self) -> f64 {
        self.fallback_monitor.cache_hit_rate()
    }

    /// Get fallback average latency (ms)
    pub fn fallback_avg_latency_ms(&self) -> f64 {
        self.fallback_monitor.metrics().avg_latency_ms
    }

    /// Get fallback max latency (ms)
    pub fn fallback_max_latency_ms(&self) -> u64 {
        self.fallback_monitor.metrics().max_latency_ms
    }
}

impl Default for GnnGuidedSearch {
    fn default() -> Self {
        Self::new()
    }
}

/// Infer the most likely tactic for applying a theorem.
///
/// Examines the theorem's name and statement to guess the appropriate
/// tactic (Apply, Rewrite, Induction, etc.). This heuristic is used
/// when the GNN provides only premise rankings without tactic suggestions.
fn infer_tactic(name: &str, statement: &Term) -> Tactic {
    let name_lower = name.to_lowercase();

    // Rewrite hints: names containing "eq", "subst", "rewrite", "sym"
    if name_lower.contains("eq")
        || name_lower.contains("subst")
        || name_lower.contains("rewrite")
        || name_lower.contains("sym")
    {
        return Tactic::Rewrite(name.to_string());
    }

    // Induction hints: names containing "ind", "rec", "induction"
    if name_lower.contains("_ind")
        || name_lower.contains("_rec")
        || name_lower.contains("induction")
    {
        if let Term::Pi { param_type, .. } = statement {
            return Tactic::Induction(*param_type.clone());
        }
    }

    // Cases hints: names containing "cases", "destruct", "elim"
    if name_lower.contains("cases")
        || name_lower.contains("destruct")
        || name_lower.contains("elim")
    {
        if let Term::Pi { param_type, .. } = statement {
            return Tactic::Cases(*param_type.clone());
        }
    }

    // Default: Apply the theorem
    Tactic::Apply(name.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, Goal, Hypothesis, Variable};

    fn make_test_state() -> ProofState {
        ProofState {
            goals: vec![Goal {
                id: "g0".to_string(),
                target: Term::App {
                    func: Box::new(Term::Const("is_even".to_string())),
                    args: vec![Term::App {
                        func: Box::new(Term::Const("add".to_string())),
                        args: vec![Term::Var("n".to_string()), Term::Var("n".to_string())],
                    }],
                },
                hypotheses: vec![Hypothesis {
                    name: "h".to_string(),
                    ty: Term::Const("Nat".to_string()),
                    body: None,
                    type_info: None,
                }],
            }],
            context: Context {
                theorems: Vec::new(),
                axioms: Vec::new(),
                definitions: Vec::new(),
                variables: vec![Variable {
                    name: "n".to_string(),
                    ty: Term::Const("Nat".to_string()),
                    type_info: None,
                }],
            },
            proof_script: Vec::new(),
            metadata: std::collections::HashMap::new(),
        }
    }

    fn make_test_premises() -> Vec<Theorem> {
        vec![
            Theorem {
                name: "even_add_self".to_string(),
                statement: Term::Pi {
                    param: "m".to_string(),
                    param_type: Box::new(Term::Const("Nat".to_string())),
                    body: Box::new(Term::App {
                        func: Box::new(Term::Const("is_even".to_string())),
                        args: vec![Term::App {
                            func: Box::new(Term::Const("add".to_string())),
                            args: vec![Term::Var("m".to_string()), Term::Var("m".to_string())],
                        }],
                    }),
                },
                proof: None,
                aspects: vec!["arithmetic".to_string()],
            },
            Theorem {
                name: "zero_is_even".to_string(),
                statement: Term::App {
                    func: Box::new(Term::Const("is_even".to_string())),
                    args: vec![Term::Const("zero".to_string())],
                },
                proof: None,
                aspects: vec!["base_case".to_string()],
            },
            Theorem {
                name: "add_comm".to_string(),
                statement: Term::Pi {
                    param: "a".to_string(),
                    param_type: Box::new(Term::Const("Nat".to_string())),
                    body: Box::new(Term::Pi {
                        param: "b".to_string(),
                        param_type: Box::new(Term::Const("Nat".to_string())),
                        body: Box::new(Term::App {
                            func: Box::new(Term::Const("eq".to_string())),
                            args: vec![
                                Term::App {
                                    func: Box::new(Term::Const("add".to_string())),
                                    args: vec![
                                        Term::Var("a".to_string()),
                                        Term::Var("b".to_string()),
                                    ],
                                },
                                Term::App {
                                    func: Box::new(Term::Const("add".to_string())),
                                    args: vec![
                                        Term::Var("b".to_string()),
                                        Term::Var("a".to_string()),
                                    ],
                                },
                            ],
                        }),
                    }),
                },
                proof: None,
                aspects: vec!["commutativity".to_string()],
            },
        ]
    }

    #[tokio::test]
    async fn test_rank_premises_without_server() {
        let mut search = GnnGuidedSearch::new();
        let state = make_test_state();
        let premises = make_test_premises();

        let ranked = search.rank_premises(&state, &premises).await;

        // Even without server, symbolic scores should produce results
        assert!(
            !ranked.is_empty(),
            "Symbolic fallback should produce results"
        );

        // All results should have symbolic scores only
        for sp in &ranked {
            assert!(
                !sp.gnn_score_from_server,
                "No GNN server, scores should be local"
            );
            assert!(sp.combined_score >= 0.0, "Scores must be non-negative");
        }
    }

    #[tokio::test]
    async fn test_all_premises_scored() {
        let mut search = GnnGuidedSearch::new();
        let state = make_test_state();
        let premises = make_test_premises();

        let ranked = search.rank_premises(&state, &premises).await;

        // All three premises should appear (with symbolic fallback)
        assert!(
            !ranked.is_empty(),
            "Symbolic fallback should produce ranked premises"
        );

        // Check that known premises are present
        let names: Vec<&str> = ranked.iter().map(|sp| sp.name.as_str()).collect();
        assert!(
            names.contains(&"even_add_self"),
            "even_add_self should appear in rankings"
        );

        // All scores should be valid (non-NaN, non-negative)
        for sp in &ranked {
            assert!(
                sp.symbolic_score.is_finite() && sp.symbolic_score >= 0.0,
                "Symbolic score for {} must be finite and non-negative, got {}",
                sp.name,
                sp.symbolic_score
            );
            assert!(
                sp.combined_score.is_finite() && sp.combined_score >= 0.0,
                "Combined score for {} must be finite and non-negative, got {}",
                sp.name,
                sp.combined_score
            );
        }
    }

    #[test]
    fn test_infer_tactic_apply() {
        let tactic = infer_tactic("some_lemma", &Term::Const("P".to_string()));
        assert_eq!(tactic, Tactic::Apply("some_lemma".to_string()));
    }

    #[test]
    fn test_infer_tactic_rewrite() {
        let tactic = infer_tactic("add_eq_zero", &Term::Const("P".to_string()));
        assert_eq!(tactic, Tactic::Rewrite("add_eq_zero".to_string()));
    }

    #[test]
    fn test_infer_tactic_induction() {
        let tactic = infer_tactic(
            "nat_ind",
            &Term::Pi {
                param: "n".to_string(),
                param_type: Box::new(Term::Const("Nat".to_string())),
                body: Box::new(Term::Var("P".to_string())),
            },
        );
        assert_eq!(tactic, Tactic::Induction(Term::Const("Nat".to_string())));
    }

    #[test]
    fn test_search_stats_tracking() {
        let search = GnnGuidedSearch::new();
        assert_eq!(search.stats().total_calls, 0);
        assert_eq!(search.stats().gnn_calls, 0);
    }

    #[tokio::test]
    async fn test_stats_increment_on_call() {
        let mut search = GnnGuidedSearch::new();
        let state = make_test_state();
        let premises = make_test_premises();

        let _ = search.rank_premises(&state, &premises).await;
        assert_eq!(search.stats().total_calls, 1);
        assert_eq!(search.stats().fallback_calls, 1); // No server

        let _ = search.rank_premises(&state, &premises).await;
        assert_eq!(search.stats().total_calls, 2);
    }

    #[test]
    fn test_config_defaults() {
        let config = GuidedSearchConfig::default();
        assert_eq!(config.max_graph_depth, 4);
        assert!((config.gnn_weight - 0.7).abs() < f32::EPSILON);
        assert!((config.symbolic_weight - 0.3).abs() < f32::EPSILON);
        assert_eq!(config.max_tactics, 20);
    }
}
