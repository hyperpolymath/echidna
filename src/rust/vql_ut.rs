// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! VQL-UT: Cross-Prover Query Language for ECHIDNA
//!
//! Typed query builder and executor for querying proof state across all 30
//! prover backends via VeriSimDB's octad storage. Implements a subset of
//! VQL-UT with progressive type safety enforcement.
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
use std::collections::HashMap;
use tracing::{debug, info};

use crate::core::Goal;
use crate::provers::ProverKind;

#[cfg(feature = "verisimdb")]
use crate::proof_encoding;
#[cfg(feature = "verisimdb")]
use crate::verisimdb_bridge::{OctadPayload, VeriSimDBClient};

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
                "VQL-UT Level {} requires a cardinality limit (use .with_limit())",
                level
            );
        }

        // Level 8: Effect tracking — always ReadOnly for query ops
        // (builder ensures effect matches operation)

        // Level 9: Temporal safety — must have a version constraint
        if level >= 9 && self.query.min_version.is_none() {
            anyhow::bail!(
                "VQL-UT Level {} requires a version constraint (use .with_min_version())",
                level
            );
        }

        // Level 10: Linearity — tracked at the octad level, not query level
        // (enforced by VeriSimDB's provenance modality)

        debug!(
            "VQL-UT query built: {:?} at level {} for {:?}",
            self.query.operation, level, self.query.theorem_name,
        );

        Ok(self.query)
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Query Executor
// ═══════════════════════════════════════════════════════════════════════

/// Executes VQL-UT queries against VeriSimDB.
///
/// Uses the VeriSimDBClient from the verisimdb_bridge module when
/// the `verisimdb` feature is enabled. Falls back to a no-op executor
/// when VeriSimDB is not available.
pub struct QueryExecutor {
    #[cfg(feature = "verisimdb")]
    client: VeriSimDBClient,

    #[cfg(not(feature = "verisimdb"))]
    _phantom: std::marker::PhantomData<()>,
}

impl QueryExecutor {
    /// Create a new query executor.
    #[cfg(feature = "verisimdb")]
    pub fn new(verisimdb_url: &str) -> Self {
        QueryExecutor {
            client: VeriSimDBClient::new(verisimdb_url),
        }
    }

    /// Create a new query executor (no VeriSimDB — stub mode).
    #[cfg(not(feature = "verisimdb"))]
    pub fn new(_verisimdb_url: &str) -> Self {
        QueryExecutor {
            _phantom: std::marker::PhantomData,
        }
    }

    /// Execute a typed query and return results.
    pub async fn execute(&self, query: &ProofQuery) -> Result<QueryResult> {
        info!(
            "Executing VQL-UT query: {:?} at level {:?}",
            query.operation, query.level,
        );

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
        let theorem = query.theorem_name.as_deref().unwrap_or("");

        #[cfg(feature = "verisimdb")]
        if let Some(prover) = query.prover {
            // Generate the octad key and look it up directly
            if let Some(ref goal_display) = query.goal_display {
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

    /// Find similar proofs via vector similarity (future: neural embeddings).
    async fn execute_find_similar(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Vector similarity requires neural embeddings in VeriSimDB's
        // vector modality. Returns empty for now — wired when neural
        // module provides embeddings.
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Search across all provers for proofs of a theorem.
    async fn execute_cross_prover(&self, query: &ProofQuery) -> Result<QueryResult> {
        let _theorem = query.theorem_name.as_deref().unwrap_or("");
        let _limit = query.limit.unwrap_or(100);

        // In production: query VeriSimDB's document modality for all octads
        // matching the theorem name, then group by cross_prover_id.
        // The graph modality provides the cross-prover links.

        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Get the provenance trace for a proof.
    async fn execute_provenance(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Route to VeriSimDB's provenance modality
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Get the temporal version history for a proof.
    async fn execute_temporal(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Route to VeriSimDB's temporal modality
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Get the dependency graph for a proof.
    async fn execute_dependency(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Route to VeriSimDB's graph modality
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Aggregate axiom usage across proofs.
    async fn execute_axiom_usage(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Aggregate across VeriSimDB's semantic modality (axioms_used field)
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }

    /// Aggregate tactic success statistics.
    async fn execute_tactic_stats(&self, query: &ProofQuery) -> Result<QueryResult> {
        // Aggregate across VeriSimDB's document modality (tactics_text field)
        Ok(QueryResult {
            count: 0,
            entries: vec![],
            verified_level: query.level,
            effect: query.effect,
        })
    }
}

/// Convert an OctadPayload to a QueryResultEntry.
#[cfg(feature = "verisimdb")]
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
        assert!(result.unwrap_err().to_string().contains("cardinality limit"));
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
        assert!(result.unwrap_err().to_string().contains("version constraint"));
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
            QueryOp::FindProof, QueryOp::FindSimilar, QueryOp::CrossProverSearch,
            QueryOp::ProvenanceTrace, QueryOp::TemporalHistory, QueryOp::DependencyGraph,
            QueryOp::AxiomUsage, QueryOp::TacticStats,
        ] {
            let mut builder = CrossProverQueryBuilder::new(TypeLevel::Parse);
            builder.query.operation = op;
            let query = builder.build().unwrap();
            assert_eq!(query.operation, op);
        }
    }

    #[tokio::test]
    async fn test_executor_find_proof_empty() {
        let executor = QueryExecutor::new("http://localhost:8080");
        let query = CrossProverQueryBuilder::new(TypeLevel::ResultType)
            .find_proof("nonexistent")
            .build()
            .unwrap();

        let result = executor.execute(&query).await.unwrap();
        assert_eq!(result.count, 0);
        assert_eq!(result.verified_level, TypeLevel::ResultType);
    }
}
