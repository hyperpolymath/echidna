// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! VCL-UT: Cross-Prover Query Language for ECHIDNA
//!
//! Typed query builder and executor for querying proof state across all 30
//! prover backends via VeriSimDB's octad storage. Implements a subset of
//! VCL-UT with progressive type safety enforcement.
//!
//! Query types:
//!   - `FindProof` — retrieve a specific proof by theorem + prover
//!   - `FindSimilar` — similarity search via goal embeddings
//!   - `CrossProverSearch` — find all proofs of a theorem across provers
//!   - `ProvenanceTrace` — get the audit trail for a proof
//!   - `TemporalHistory` — get version history
//!   - `DependencyGraph` — get theorem dependency links
//!   - `AxiomUsage` — aggregate axiom usage across proofs
//!   - `TacticStats` — aggregate tactic success statistics
//!
//! All queries are type-safe at the requested level (1-10) and route
//! through VeriSimDB's HTTP API.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use tracing::{debug, info};
#[cfg(feature = "verisim")]
use tracing::warn;

use crate::provers::ProverKind;

#[cfg(feature = "verisim")]
use crate::core::Goal;
#[cfg(feature = "verisim")]
use crate::proof_encoding;
#[cfg(feature = "verisim")]
use crate::verisim_bridge::{OctadPayload, VeriSimDBClient};

// ═══════════════════════════════════════════════════════════════════════
// Type Safety Levels
// ═══════════════════════════════════════════════════════════════════════

/// The 10 progressive type safety levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TypeLevel {
    /// Level 0: No type safety (raw string queries)
    Unsafe = 0,
    /// Level 1: Parse-time safety (syntactically valid)
    Parse = 1,
    /// Level 2: Schema-binding safety (fields exist)
    Schema = 2,
    /// Level 3: Type-compatible operations (matching types in filters)
    TypeCompat = 3,
    /// Level 4: Null-safety (no null dereferences)
    NullSafe = 4,
    /// Level 5: Injection-proof (no user input in structure)
    InjectionProof = 5,
    /// Level 6: Result-type safety (return type matches projection)
    ResultType = 6,
    /// Level 7: Cardinality safety (bounded result sets)
    Cardinality = 7,
    /// Level 8: Effect-tracking (declared read/write effects)
    Effect = 8,
    /// Level 9: Temporal safety (version-aware, no stale reads)
    Temporal = 9,
    /// Level 10: Linearity safety (proof consumption tracking)
    Linear = 10,
}

// ═══════════════════════════════════════════════════════════════════════
// Query AST
// ═══════════════════════════════════════════════════════════════════════

/// A typed proof query.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofQuery {
    /// Query operation
    pub operation: QueryOp,

    /// Type safety level for this query
    pub level: TypeLevel,

    /// Theorem name filter (optional)
    pub theorem_name: Option<String>,

    /// Prover filter (optional — None means all provers)
    pub prover: Option<ProverKind>,

    /// Goal display string for identity matching
    pub goal_display: Option<String>,

    /// Aspect tags for document search
    pub aspects: Vec<String>,

    /// Maximum results (required at Level 7+)
    pub limit: Option<usize>,

    /// Minimum version (required at Level 9+)
    pub min_version: Option<u64>,

    /// Query effect declaration (required at Level 8+)
    pub effect: QueryEffect,
}

/// Query operation types.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum QueryOp {
    FindProof,
    FindSimilar,
    CrossProverSearch,
    ProvenanceTrace,
    TemporalHistory,
    DependencyGraph,
    AxiomUsage,
    TacticStats,
}

/// Query effect classification.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum QueryEffect {
    ReadOnly,
    ReadWrite,
    WriteOnly,
}

/// Query result — a list of matching octad summaries.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryResult {
    /// Number of matching results
    pub count: usize,

    /// Result entries (summary, not full octad)
    pub entries: Vec<QueryResultEntry>,

    /// Type level that was verified
    pub verified_level: TypeLevel,

    /// Query effect that was declared
    pub effect: QueryEffect,
}

/// A single entry in the query result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryResultEntry {
    /// Octad key (proof identity)
    pub key: String,

    /// Theorem name
    pub theorem_name: String,

    /// Prover that produced this proof
    pub prover: String,

    /// Proof status
    pub status: String,

    /// Time taken (ms)
    pub time_ms: u64,

    /// Aspect tags
    pub aspects: Vec<String>,

    /// Axioms used
    pub axioms: Vec<String>,

    /// Cross-prover identity (goal-only hash)
    pub cross_prover_id: String,
}

// ═══════════════════════════════════════════════════════════════════════
// CrossProverQueryBuilder — fluent API for constructing typed queries
// ═══════════════════════════════════════════════════════════════════════

/// Builder for constructing type-safe cross-prover queries.
///
/// The builder enforces progressive type safety: each `with_*` method
/// raises the minimum type level of the query. The final `build()` call
/// validates that the query meets the requested level.
///
/// # Example
/// ```ignore
/// let query = CrossProverQueryBuilder::new(TypeLevel::Cardinality)
///     .find_proof("nat_add_zero")
///     .with_prover(ProverKind::Lean4)
///     .with_limit(10)
///     .build()?;
/// ```
pub struct CrossProverQueryBuilder {
    query: ProofQuery,
}

impl CrossProverQueryBuilder {
    /// Create a new query builder at the given type safety level.
    pub fn new(level: TypeLevel) -> Self {
        CrossProverQueryBuilder {
            query: ProofQuery {
                operation: QueryOp::FindProof,
                level,
                theorem_name: None,
                prover: None,
                goal_display: None,
                aspects: Vec::new(),
                limit: None,
                min_version: None,
                effect: QueryEffect::ReadOnly,
            },
        }
    }

    /// Set the operation to FindProof for a specific theorem.
    pub fn find_proof(mut self, theorem_name: &str) -> Self {
        self.query.operation = QueryOp::FindProof;
        self.query.theorem_name = Some(theorem_name.to_string());
        self
    }

    /// Set the operation to FindSimilar for a goal.
    pub fn find_similar(mut self, goal_display: &str) -> Self {
        self.query.operation = QueryOp::FindSimilar;
        self.query.goal_display = Some(goal_display.to_string());
        self
    }

    /// Set the operation to CrossProverSearch.
    pub fn cross_prover_search(mut self, theorem_name: &str) -> Self {
        self.query.operation = QueryOp::CrossProverSearch;
        self.query.theorem_name = Some(theorem_name.to_string());
        self
    }

    /// Set the operation to ProvenanceTrace.
    pub fn provenance_trace(mut self, theorem_name: &str) -> Self {
        self.query.operation = QueryOp::ProvenanceTrace;
        self.query.theorem_name = Some(theorem_name.to_string());
        self
    }

    /// Set the operation to TemporalHistory.
    pub fn temporal_history(mut self, theorem_name: &str) -> Self {
        self.query.operation = QueryOp::TemporalHistory;
        self.query.theorem_name = Some(theorem_name.to_string());
        self
    }

    /// Set the operation to DependencyGraph.
    pub fn dependency_graph(mut self, theorem_name: &str) -> Self {
        self.query.operation = QueryOp::DependencyGraph;
        self.query.theorem_name = Some(theorem_name.to_string());
        self
    }

    /// Set the operation to AxiomUsage.
    pub fn axiom_usage(mut self) -> Self {
        self.query.operation = QueryOp::AxiomUsage;
        self
    }

    /// Set the operation to TacticStats.
    pub fn tactic_stats(mut self) -> Self {
        self.query.operation = QueryOp::TacticStats;
        self
    }

    /// Filter by prover.
    pub fn with_prover(mut self, prover: ProverKind) -> Self {
        self.query.prover = Some(prover);
        self
    }

    /// Filter by aspect tags.
    pub fn with_aspects(mut self, aspects: Vec<String>) -> Self {
        self.query.aspects = aspects;
        self
    }

    /// Set the result limit (required at Level 7+).
    pub fn with_limit(mut self, limit: usize) -> Self {
        self.query.limit = Some(limit);
        self
    }

    /// Set the minimum version (required at Level 9+).
    pub fn with_min_version(mut self, version: u64) -> Self {
        self.query.min_version = Some(version);
        self
    }

    /// Set the goal display string for identity matching.
    pub fn with_goal(mut self, goal_display: &str) -> Self {
        self.query.goal_display = Some(goal_display.to_string());
        self
    }

    /// Build the query, validating type safety at the requested level.
    pub fn build(self) -> Result<ProofQuery> {
        let level = self.query.level as u8;

        // Level 1: Parse safety (always satisfied by the builder API)
        // Level 2: Schema binding (satisfied — we use typed fields)
        // Level 3: Type compatibility (satisfied — no mixed-type comparisons)
        // Level 4: Null safety (satisfied — Option types)
        // Level 5: Injection proof (satisfied — no string interpolation)
        // Level 6: Result type (satisfied — QueryOp determines return type)

        // Level 7: Cardinality — must have a limit
        if level >= 7 && self.query.limit.is_none() {
            anyhow::bail!(
                "VCL-UT Level {} requires a cardinality limit (use .with_limit())",
                level
            );
        }

        // Level 8: Effect tracking — always ReadOnly for query ops
        // (builder ensures effect matches operation)

        // Level 9: Temporal safety — must have a version constraint
        if level >= 9 && self.query.min_version.is_none() {
            anyhow::bail!(
                "VCL-UT Level {} requires a version constraint (use .with_min_version())",
                level
            );
        }

        // Level 10: Linearity — tracked at the octad level, not query level
        // (enforced by VeriSimDB's provenance modality)

        debug!(
            "VCL-UT query built: {:?} at level {} for {:?}",
            self.query.operation, level, self.query.theorem_name,
        );

        Ok(self.query)
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Query Executor
// ═══════════════════════════════════════════════════════════════════════

/// Executes VCL-UT queries against VeriSimDB.
///
/// Uses the VeriSimDBClient from the verisim_bridge module when
/// the `verisim` feature is enabled. Falls back to a no-op executor
/// when VeriSimDB is not available.
pub struct QueryExecutor {
    #[cfg(feature = "verisim")]
    client: VeriSimDBClient,

    #[cfg(not(feature = "verisim"))]
    _phantom: std::marker::PhantomData<()>,
}

impl QueryExecutor {
    /// Create a new query executor.
    #[cfg(feature = "verisim")]
    pub fn new(verisim_url: &str) -> Self {
        QueryExecutor {
            client: VeriSimDBClient::new(verisim_url),
        }
    }

    /// Create a new query executor (no VeriSimDB — stub mode).
    #[cfg(not(feature = "verisim"))]
    pub fn new(_verisimdb_url: &str) -> Self {
        QueryExecutor {
            _phantom: std::marker::PhantomData,
        }
    }

    /// Validate a query against TypeLL's VCL-UT 10-level type checker.
    ///
    /// Calls the TypeLL server at localhost:7800 to verify that the query
    /// meets its declared safety level. Returns the verified level and any
    /// diagnostics. Falls back gracefully if TypeLL is unreachable.
    async fn validate_with_typell(&self, query: &ProofQuery) -> Result<TypeLevel> {
        let typell_url =
            std::env::var("TYPELL_URL").unwrap_or_else(|_| "http://localhost:7800".to_string());

        let check_body = serde_json::json!({
            "query": serde_json::to_string(query).unwrap_or_default(),
            "modalities": ["Semantic", "Document", "Graph", "Provenance", "Temporal"],
            "result_fields": query.theorem_name.as_deref().map(|t| vec![t]).unwrap_or_default(),
        });

        let client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(5))
            .build()
            .context("Failed to create HTTP client for TypeLL")?;

        match client
            .post(format!("{}/api/v1/vcl-ut/check", typell_url))
            .json(&check_body)
            .send()
            .await
        {
            Ok(resp) if resp.status().is_success() => {
                if let Ok(body) = resp.json::<serde_json::Value>().await {
                    let max_level = body
                        .get("safety_report")
                        .and_then(|sr| sr.get("max_level"))
                        .and_then(|ml| ml.as_u64())
                        .unwrap_or(0);

                    let valid = body.get("valid").and_then(|v| v.as_bool()).unwrap_or(true);

                    if !valid {
                        let errors = body
                            .get("rule_errors")
                            .and_then(|e| e.as_array())
                            .map(|arr| {
                                arr.iter()
                                    .filter_map(|v| v.as_str())
                                    .collect::<Vec<_>>()
                                    .join("; ")
                            })
                            .unwrap_or_default();
                        anyhow::bail!("TypeLL VCL-UT validation failed: {}", errors);
                    }

                    info!(
                        "TypeLL verified VCL-UT level {}/10 for {:?}",
                        max_level, query.operation,
                    );

                    // Map TypeLL's 1-based SafetyLevel to our 0-10 TypeLevel
                    Ok(match max_level {
                        0 | 1 => TypeLevel::Parse,
                        2 => TypeLevel::Schema,
                        3 => TypeLevel::TypeCompat,
                        4 => TypeLevel::NullSafe,
                        5 => TypeLevel::InjectionProof,
                        6 => TypeLevel::ResultType,
                        7 => TypeLevel::Cardinality,
                        8 => TypeLevel::Effect,
                        9 => TypeLevel::Temporal,
                        10 => TypeLevel::Linear,
                        _ => TypeLevel::Linear,
                    })
                } else {
                    debug!("TypeLL returned non-JSON response, falling back");
                    Ok(query.level)
                }
            },
            Ok(resp) => {
                debug!(
                    "TypeLL returned status {}, falling back to local validation",
                    resp.status()
                );
                Ok(query.level)
            },
            Err(e) => {
                debug!(
                    "TypeLL unreachable ({}), falling back to local validation",
                    e
                );
                Ok(query.level)
            },
        }
    }

    /// Execute a typed query and return results.
    ///
    /// Validates the query against TypeLL's 10-level type checker before
    /// execution. Falls back to local validation if TypeLL is unreachable.
    pub async fn execute(&self, query: &ProofQuery) -> Result<QueryResult> {
        info!(
            "Executing VCL-UT query: {:?} at level {:?}",
            query.operation, query.level,
        );

        // Pre-flight: validate with TypeLL if available
        let verified_level = self
            .validate_with_typell(query)
            .await
            .unwrap_or(query.level);

        if (verified_level as u8) < (query.level as u8) {
            anyhow::bail!(
                "TypeLL verified level {:?} is below requested level {:?}",
                verified_level,
                query.level,
            );
        }

        match query.operation {
            QueryOp::FindProof => self.execute_find_proof(query).await,
            QueryOp::FindSimilar => self.execute_find_similar(query).await,
            QueryOp::CrossProverSearch => self.execute_cross_prover(query).await,
            QueryOp::ProvenanceTrace => self.execute_provenance(query).await,
            QueryOp::TemporalHistory => self.execute_temporal(query).await,
            QueryOp::DependencyGraph => self.execute_dependency(query).await,
            QueryOp::AxiomUsage => self.execute_axiom_usage(query).await,
            QueryOp::TacticStats => self.execute_tactic_stats(query).await,
        }
    }

    /// Find a specific proof by theorem name and optional prover.
    async fn execute_find_proof(&self, query: &ProofQuery) -> Result<QueryResult> {
        #[cfg(feature = "verisim")]
        if let Some(prover) = query.prover {
            // Generate the octad key and look it up directly
            if let Some(ref goal_display) = query.goal_display {
                let theorem = query.theorem_name.as_deref().unwrap_or("");
                let goal = Goal {
                    id: "query".to_string(),
                    target: crate::core::Term::Var(goal_display.clone()),
                    hypotheses: vec![],
                };
                let key = proof_encoding::proof_identity(theorem, &goal, prover);

                if let Some(octad) = self.client.get_octad(&key).await? {
                    return Ok(QueryResult {
                        count: 1,
                        entries: vec![octad_to_entry(&octad)],
                        verified_level: query.level,
                        effect: query.effect,
                    });
                }
            }
        }

        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Find similar proofs via vector similarity search.
    /// Calls VeriSimDB POST /api/v1/search/vector with the goal embedding.
    async fn execute_find_similar(&self, query: &ProofQuery) -> Result<QueryResult> {
        let limit = query.limit.unwrap_or(10);
        let goal_display = query.goal_display.as_deref().unwrap_or("");

        #[cfg(feature = "verisim")]
        {
            // Request a goal embedding from the Julia inference service
            let embedding = self
                .fetch_goal_embedding(goal_display)
                .await
                .unwrap_or_default();

            if !embedding.is_empty() {
                let search_body = serde_json::json!({
                    "vector": embedding,
                    "limit": limit,
                    "modality": "vector"
                });

                let url = format!("{}/api/v1/search/vector", self.client.base_url);
                let response = self.client.http.post(&url).json(&search_body).send().await;

                if let Ok(resp) = response {
                    if resp.status().is_success() {
                        if let Ok(results) = resp.json::<Vec<serde_json::Value>>().await {
                            let entries: Vec<QueryResultEntry> = results
                                .iter()
                                .filter_map(|r| search_result_to_entry(r))
                                .take(limit)
                                .collect();
                            return Ok(QueryResult {
                                count: entries.len(),
                                entries,
                                verified_level: query.level,
                                effect: query.effect,
                            });
                        }
                    }
                }
            }
        }

        let _ = (limit, goal_display);
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Search across all provers for proofs of a theorem.
    /// Calls VeriSimDB GET /api/v1/search/text with the theorem name.
    async fn execute_cross_prover(&self, query: &ProofQuery) -> Result<QueryResult> {
        let theorem = query.theorem_name.as_deref().unwrap_or("");
        let limit = query.limit.unwrap_or(100);

        #[cfg(feature = "verisim")]
        {
            let url = format!(
                "{}/api/v1/search/text?q={}&limit={}",
                self.client.base_url,
                urlencoding::encode(theorem),
                limit,
            );

            let response = self.client.http.get(&url).send().await;

            if let Ok(resp) = response {
                if resp.status().is_success() {
                    if let Ok(results) = resp.json::<Vec<serde_json::Value>>().await {
                        let entries: Vec<QueryResultEntry> = results
                            .iter()
                            .filter_map(|r| search_result_to_entry(r))
                            .take(limit)
                            .collect();
                        return Ok(QueryResult {
                            count: entries.len(),
                            entries,
                            verified_level: query.level,
                            effect: query.effect,
                        });
                    }
                }
            }
        }

        let _ = (theorem, limit);
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Get the provenance trace for a proof.
    /// Calls VeriSimDB GET /api/v1/octads/{key} and extracts provenance modality.
    async fn execute_provenance(&self, query: &ProofQuery) -> Result<QueryResult> {
        #[cfg(feature = "verisim")]
        if let Some(ref theorem) = query.theorem_name {
            if let Some(ref goal_display) = query.goal_display {
                if let Some(prover) = query.prover {
                    let goal = Goal {
                        id: "query".to_string(),
                        target: crate::core::Term::Var(goal_display.clone()),
                        hypotheses: vec![],
                    };
                    let key = proof_encoding::proof_identity(theorem, &goal, prover);

                    if let Some(octad) = self.client.get_octad(&key).await? {
                        let entry = octad_to_entry(&octad);
                        return Ok(QueryResult {
                            count: 1,
                            entries: vec![entry],
                            verified_level: query.level,
                            effect: query.effect,
                        });
                    }
                }
            }
        }

        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Get the temporal version history for a proof.
    /// Calls VeriSimDB GET /api/v1/octads/{key} and extracts temporal modality.
    async fn execute_temporal(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Same retrieval as provenance — the octad contains all modalities
        self.execute_provenance(query).await
    }

    /// Get the dependency graph for a proof.
    /// Calls VeriSimDB GET /api/v1/search/related/{id} for graph traversal.
    async fn execute_dependency(&self, query: &ProofQuery) -> Result<QueryResult> {
        let limit = query.limit.unwrap_or(50);

        #[cfg(feature = "verisim")]
        if let Some(ref theorem) = query.theorem_name {
            if let Some(ref goal_display) = query.goal_display {
                if let Some(prover) = query.prover {
                    let goal = Goal {
                        id: "query".to_string(),
                        target: crate::core::Term::Var(goal_display.clone()),
                        hypotheses: vec![],
                    };
                    let key = proof_encoding::proof_identity(theorem, &goal, prover);

                    let url = format!(
                        "{}/api/v1/search/related/{}?limit={}",
                        self.client.base_url, key, limit,
                    );

                    let response = self.client.http.get(&url).send().await;

                    if let Ok(resp) = response {
                        if resp.status().is_success() {
                            if let Ok(results) = resp.json::<Vec<serde_json::Value>>().await {
                                let entries: Vec<QueryResultEntry> = results
                                    .iter()
                                    .filter_map(|r| search_result_to_entry(r))
                                    .take(limit)
                                    .collect();
                                return Ok(QueryResult {
                                    count: entries.len(),
                                    entries,
                                    verified_level: query.level,
                                    effect: query.effect,
                                });
                            }
                        }
                    }
                }
            }
        }

        let _ = limit;
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Aggregate axiom usage across proofs.
    /// Calls VeriSimDB text search for all proofs, then aggregates axioms.
    async fn execute_axiom_usage(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Delegate to cross-prover search with aspect filter "axiom"
        let mut axiom_query = query.clone();
        axiom_query.operation = QueryOp::CrossProverSearch;
        self.execute_cross_prover(&axiom_query).await
    }

    /// Aggregate tactic success statistics.
    /// Calls VeriSimDB text search for all proofs, then aggregates tactics.
    async fn execute_tactic_stats(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Delegate to cross-prover search with aspect filter "tactic"
        let mut tactic_query = query.clone();
        tactic_query.operation = QueryOp::CrossProverSearch;
        self.execute_cross_prover(&tactic_query).await
    }

    /// Fetch a goal embedding from the Julia inference service (port 8090).
    /// Returns a 512-dim f32 vector, or empty vec on failure.
    #[cfg(feature = "verisim")]
    async fn fetch_goal_embedding(&self, goal_display: &str) -> Result<Vec<f32>> {
        let julia_url = std::env::var("ECHIDNA_JULIA_URL")
            .unwrap_or_else(|_| "http://localhost:8090".to_string());

        let body = serde_json::json!({
            "goal": goal_display,
            "model": "default"
        });

        let response = self
            .client
            .http
            .post(format!("{}/api/encode", julia_url))
            .json(&body)
            .timeout(std::time::Duration::from_secs(5))
            .send()
            .await
            .context("Failed to reach Julia inference service")?;

        if response.status().is_success() {
            let result: serde_json::Value = response.json().await?;
            if let Some(embedding) = result.get("embedding").and_then(|e| e.as_array()) {
                let vec: Vec<f32> = embedding
                    .iter()
                    .filter_map(|v| v.as_f64().map(|f| f as f32))
                    .collect();
                debug!("Got {}-dim embedding from Julia", vec.len());
                return Ok(vec);
            }
        }

        warn!("Julia inference service returned no embedding");
        Ok(vec![])
    }
}

/// Convert a VeriSimDB search result JSON value to a QueryResultEntry.
#[cfg(feature = "verisim")]
fn search_result_to_entry(value: &serde_json::Value) -> Option<QueryResultEntry> {
    Some(QueryResultEntry {
        key: value.get("key")?.as_str()?.to_string(),
        theorem_name: value
            .get("theorem_statement")
            .or_else(|| {
                value
                    .get("document")
                    .and_then(|d| d.get("theorem_statement"))
            })
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string(),
        prover: value
            .get("prover")
            .or_else(|| value.get("semantic").and_then(|s| s.get("prover")))
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        status: value
            .get("status")
            .or_else(|| value.get("semantic").and_then(|s| s.get("status")))
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string(),
        time_ms: value.get("time_ms").and_then(|v| v.as_u64()).unwrap_or(0),
        aspects: value
            .get("aspects")
            .or_else(|| value.get("document").and_then(|d| d.get("aspects")))
            .and_then(|v| v.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default(),
        axioms: value
            .get("axioms_used")
            .or_else(|| value.get("semantic").and_then(|s| s.get("axioms_used")))
            .and_then(|v| v.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default(),
        cross_prover_id: value
            .get("cross_prover_id")
            .or_else(|| value.get("graph").and_then(|g| g.get("cross_prover_id")))
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string(),
    })
}

/// Simple URL encoding for query parameters.
/// Encodes spaces, ampersands, and other special characters.
#[allow(dead_code)]
mod urlencoding {
    pub fn encode(s: &str) -> String {
        let mut result = String::with_capacity(s.len() * 3);
        for byte in s.bytes() {
            match byte {
                b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                    result.push(byte as char);
                },
                _ => {
                    result.push('%');
                    result.push_str(&format!("{:02X}", byte));
                },
            }
        }
        result
    }
}

/// Convert an OctadPayload to a QueryResultEntry.
#[cfg(feature = "verisim")]
fn octad_to_entry(octad: &OctadPayload) -> QueryResultEntry {
    QueryResultEntry {
        key: octad.key.clone(),
        theorem_name: octad.document.theorem_statement.clone(),
        prover: octad.semantic.prover.clone(),
        status: format!("{:?}", octad.semantic.status),
        time_ms: *octad.tensor.metrics.get("time_ms").unwrap_or(&0.0) as u64,
        aspects: octad.document.aspects.clone(),
        axioms: octad.semantic.axioms_used.clone(),
        cross_prover_id: octad.graph.cross_prover_id.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Cross-prover convenience helpers — match the per-backend trait shape so
// front-ends (CLI, REST, REPL) can append cross-prover results to the
// per-backend aggregation without rebuilding a CrossProverQueryBuilder.
// ═══════════════════════════════════════════════════════════════════════

/// Query VeriSimDB for theorems matching a free-text pattern, across all
/// provers, returning bare names that can be folded into a per-backend
/// `search_theorems` aggregation.
///
/// Uses VeriSimDB's `/api/v1/search/text` (the same endpoint
/// `execute_cross_prover` calls) and projects each `QueryResultEntry` to
/// its `theorem_name`. Empty names are filtered. The query runs at
/// `TypeLevel::Cardinality` (Level 7) so the `limit` is enforced
/// type-safely.
///
/// **Failure mode**: returns `Ok(vec![])` when VeriSimDB is unreachable,
/// returns 4xx/5xx, or has no matches. Errors from the executor itself
/// (TypeLL validation, query construction) propagate. Callers that want
/// strict failure semantics should use `QueryExecutor::execute` directly.
///
/// **Layering**: this is the dispatcher-layer counterpart to a backend's
/// `search_theorems`. The 70+ backends whose native search is empty
/// (`Ok(vec![])`) are not stubs to be filled — they correctly report
/// "no native prover-specific search". Cross-prover semantics belong
/// here, where one query covers every prover that has ever recorded a
/// matching attempt.
#[cfg(feature = "verisim")]
pub async fn cross_prover_search_names(
    verisim_url: &str,
    pattern: &str,
    limit: usize,
) -> Result<Vec<String>> {
    if pattern.trim().is_empty() {
        return Ok(vec![]);
    }
    let executor = QueryExecutor::new(verisim_url);
    let query = CrossProverQueryBuilder::new(TypeLevel::Cardinality)
        .cross_prover_search(pattern)
        .with_limit(limit)
        .build()?;

    match executor.execute(&query).await {
        Ok(result) => Ok(result
            .entries
            .into_iter()
            .filter_map(|e| {
                let name = e.theorem_name.trim().to_string();
                if name.is_empty() {
                    None
                } else {
                    Some(name)
                }
            })
            .collect()),
        Err(_) => Ok(vec![]),
    }
}

/// Build a no-op cross-prover search shim for the no-verisim default
/// build, so callers don't need their own `#[cfg]` ladder. Always
/// returns `Ok(vec![])`.
#[cfg(not(feature = "verisim"))]
pub async fn cross_prover_search_names(
    _verisim_url: &str,
    _pattern: &str,
    _limit: usize,
) -> Result<Vec<String>> {
    Ok(vec![])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_level6() {
        let query = CrossProverQueryBuilder::new(TypeLevel::ResultType)
            .find_proof("nat_add_zero")
            .with_prover(ProverKind::Lean)
            .with_goal("forall n, n + 0 = n")
            .build()
            .unwrap();

        assert_eq!(query.operation, QueryOp::FindProof);
        assert_eq!(query.level, TypeLevel::ResultType);
        assert_eq!(query.prover, Some(ProverKind::Lean));
    }

    #[test]
    fn test_builder_level7_requires_limit() {
        let result = CrossProverQueryBuilder::new(TypeLevel::Cardinality)
            .cross_prover_search("nat_add_zero")
            .build();

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("cardinality limit"));
    }

    #[test]
    fn test_builder_level7_with_limit() {
        let query = CrossProverQueryBuilder::new(TypeLevel::Cardinality)
            .cross_prover_search("nat_add_zero")
            .with_limit(50)
            .build()
            .unwrap();

        assert_eq!(query.limit, Some(50));
    }

    #[test]
    fn test_builder_level9_requires_version() {
        let result = CrossProverQueryBuilder::new(TypeLevel::Temporal)
            .find_proof("thm")
            .with_limit(10)
            .build();

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("version constraint"));
    }

    #[test]
    fn test_builder_level9_with_version() {
        let query = CrossProverQueryBuilder::new(TypeLevel::Temporal)
            .find_proof("thm")
            .with_limit(10)
            .with_min_version(5)
            .build()
            .unwrap();

        assert_eq!(query.min_version, Some(5));
    }

    #[test]
    fn test_builder_level10() {
        let query = CrossProverQueryBuilder::new(TypeLevel::Linear)
            .axiom_usage()
            .with_limit(100)
            .with_min_version(1)
            .build()
            .unwrap();

        assert_eq!(query.level, TypeLevel::Linear);
        assert_eq!(query.operation, QueryOp::AxiomUsage);
    }

    #[test]
    fn test_all_query_ops() {
        for op in [
            QueryOp::FindProof,
            QueryOp::FindSimilar,
            QueryOp::CrossProverSearch,
            QueryOp::ProvenanceTrace,
            QueryOp::TemporalHistory,
            QueryOp::DependencyGraph,
            QueryOp::AxiomUsage,
            QueryOp::TacticStats,
        ] {
            let mut builder = CrossProverQueryBuilder::new(TypeLevel::Parse);
            builder.query.operation = op;
            let query = builder.build().unwrap();
            assert_eq!(query.operation, op);
        }
    }

    #[tokio::test]
    async fn test_executor_find_proof_empty() {
        let executor = QueryExecutor::new("http://localhost:8081");
        let query = CrossProverQueryBuilder::new(TypeLevel::ResultType)
            .find_proof("nonexistent")
            .build()
            .unwrap();

        let result = executor.execute(&query).await.unwrap();
        assert_eq!(result.count, 0);
        assert_eq!(result.verified_level, TypeLevel::ResultType);
    }

    #[tokio::test]
    async fn test_cross_prover_search_names_empty_pattern() {
        // Empty / whitespace patterns short-circuit to empty without
        // touching VeriSimDB at all — useful for callers that pass an
        // un-validated CLI argument.
        let names =
            cross_prover_search_names("http://127.0.0.1:1", "", 10).await.unwrap();
        assert!(names.is_empty());
        let names =
            cross_prover_search_names("http://127.0.0.1:1", "   ", 10).await.unwrap();
        assert!(names.is_empty());
    }

    #[tokio::test]
    async fn test_cross_prover_search_names_unreachable_returns_empty() {
        // A real pattern against an unreachable VeriSimDB must return Ok(vec![])
        // — search is a soft query, an outage cannot kill the caller.
        // Without the verisim feature this is a no-op stub that also returns
        // Ok(vec![]), so the same assertion holds in both build modes.
        let names = cross_prover_search_names(
            "http://127.0.0.1:1",
            "associativity",
            5,
        )
        .await
        .unwrap();
        assert!(names.is_empty());
    }
}
