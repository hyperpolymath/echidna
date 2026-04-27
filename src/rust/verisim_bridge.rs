// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! VeriSimDB Bridge — Maps ECHIDNA proof state to VeriSimDB's 8-modality octad.
//!
//! This module bridges ECHIDNA's proof pipeline to VeriSimDB for persistent,
//! queryable, federated proof storage. Each proof attempt is stored as an octad
//! with data distributed across 8 modalities:
//!
//!   - **Semantic**: CBOR-encoded ProofState + type metadata + axiom list
//!   - **Temporal**: Version chain tracking proof evolution (initial → tactics → QED)
//!   - **Provenance**: Hash-chain audit trail (who ran what prover, what tactic, when)
//!   - **Document**: Full-text searchable proof text (goals, tactics, theorems)
//!   - **Graph**: Dependency links (theorem → lemmas used, goal → subgoals)
//!   - **Vector**: Goal embeddings for similarity search (find related proofs)
//!   - **Tensor**: Reserved for multi-dimensional proof metrics (future)
//!   - **Spatial**: Reserved for proof origin metadata (future)
//!
//! The bridge uses VeriSimDB's HTTP API via reqwest. For BoJ-integrated deployments,
//! the V-lang adapter (`echidna_llm_verisimdb.v`) routes through verisim.zig FFI.

use anyhow::{Context, Result};
use chrono::Utc;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{debug, info, warn};

use crate::core::{Goal, ProofState, Tactic};
use crate::proof_encoding;
use crate::provers::ProverKind;

// ═══════════════════════════════════════════════════════════════════════
// Octad Payload — the 8-modality structure for VeriSimDB
// ═══════════════════════════════════════════════════════════════════════

/// A complete octad payload ready to send to VeriSimDB.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OctadPayload {
    /// Octad key (SHA-256 proof identity)
    pub key: String,

    /// Semantic modality: CBOR proof blob + type metadata
    pub semantic: SemanticPayload,

    /// Temporal modality: version chain of proof evolution
    pub temporal: TemporalPayload,

    /// Provenance modality: audit trail of proof steps
    pub provenance: ProvenancePayload,

    /// Document modality: full-text searchable proof text
    pub document: DocumentPayload,

    /// Graph modality: dependency links
    pub graph: GraphPayload,

    /// Vector modality: goal embeddings for similarity search
    pub vector: VectorPayload,

    /// Tensor modality: multi-dimensional proof metrics (reserved)
    pub tensor: TensorPayload,

    /// Spatial modality: origin metadata (reserved)
    pub spatial: SpatialPayload,
}

/// Semantic modality — the core proof data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticPayload {
    /// CBOR-encoded ProofState (base64 for JSON transport)
    pub proof_blob_b64: String,

    /// Proof status
    pub status: ProofStatus,

    /// Goal type classification
    pub goal_type: String,

    /// Prover that produced this proof
    pub prover: String,

    /// Axioms used in the proof
    pub axioms_used: Vec<String>,

    /// Model tier used for LLM advisory (if any)
    pub llm_model: Option<String>,

    /// Whether this proof is advisory-only (LLM-suggested, not verified)
    pub advisory_only: bool,
}

/// Proof status in the octad.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum ProofStatus {
    /// Proof complete (all goals discharged)
    Complete,
    /// Proof in progress (some goals remain)
    Partial,
    /// Proof attempt failed
    Failed,
    /// Proof cached from memory (replay)
    Cached,
}

/// Temporal modality — version chain of proof evolution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TemporalPayload {
    /// Ordered list of proof snapshots (initial, after each tactic, final)
    pub versions: Vec<ProofVersion>,
}

/// A single version in the proof's temporal chain.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofVersion {
    /// Version number (monotonically increasing)
    pub version: u64,

    /// ISO 8601 timestamp
    pub timestamp: String,

    /// Actor that produced this version (prover name or "echidna-dispatch")
    pub actor: String,

    /// Description of what changed
    pub description: String,

    /// Number of remaining goals at this version
    pub goals_remaining: usize,

    /// Tactic applied (if any)
    pub tactic: Option<String>,
}

/// Provenance modality — hash-chain audit trail.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenancePayload {
    /// Ordered list of provenance records forming a hash chain
    pub records: Vec<ProvenanceRecord>,
}

/// A single provenance record in the hash chain.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceRecord {
    /// SHA-256 hash of this record's content
    pub hash: String,

    /// Hash of the previous record (empty for first record)
    pub parent_hash: String,

    /// Event type
    pub event: ProvenanceEvent,

    /// Actor (prover, agent, dispatcher)
    pub actor: String,

    /// ISO 8601 timestamp
    pub timestamp: String,

    /// Additional event-specific data
    pub data: HashMap<String, serde_json::Value>,
}

/// Provenance event types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProvenanceEvent {
    /// Proof attempt created
    Created,
    /// Tactic applied
    TacticApplied,
    /// Sub-goal spawned
    SubGoalSpawned,
    /// Prover dispatched
    ProverDispatched,
    /// Proof verified
    Verified,
    /// Proof failed
    Failed,
    /// LLM consulted
    LlmConsulted,
    /// Cross-checked with another prover
    CrossChecked,
}

/// Document modality — full-text searchable proof text.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentPayload {
    /// Theorem statement (human-readable)
    pub theorem_statement: String,

    /// Current goals (human-readable)
    pub goals_text: Vec<String>,

    /// Tactics applied so far
    pub tactics_text: Vec<String>,

    /// Aspect tags for search
    pub aspects: Vec<String>,

    /// Free-text searchable content (concatenation of above)
    pub searchable_text: String,
}

/// Graph modality — dependency links.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraphPayload {
    /// Theorems/lemmas this proof depends on (octad keys)
    pub depends_on: Vec<String>,

    /// Sub-goal proof IDs
    pub sub_goals: Vec<String>,

    /// Cross-prover identity (goal-only hash, prover-agnostic)
    pub cross_prover_id: String,

    /// Prover that produced this proof
    pub prover_id: String,
}

/// Vector modality — goal embeddings for similarity search.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VectorPayload {
    /// Goal embedding (f32 vector from neural premise selection)
    /// Empty if neural module is not available.
    pub goal_embedding: Vec<f32>,

    /// Embedding model identifier
    pub model: String,

    /// Embedding dimensions
    pub dimensions: usize,
}

/// Tensor modality — reserved for multi-dimensional proof metrics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TensorPayload {
    /// Placeholder: proof complexity metrics per tactic
    pub metrics: HashMap<String, f64>,
}

/// Spatial modality — reserved for proof origin metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpatialPayload {
    /// Placeholder: proof system origin (e.g., "lean4-mathlib")
    pub origin: String,
}

// ═══════════════════════════════════════════════════════════════════════
// ProofOctadBuilder — constructs an octad from ECHIDNA proof state
// ═══════════════════════════════════════════════════════════════════════

/// Builds a VeriSimDB octad payload from ECHIDNA proof state.
///
/// Usage:
/// ```ignore
/// let octad = ProofOctadBuilder::new("my_theorem", &goal, ProverKind::Lean)
///     .with_proof_state(&proof_state)
///     .with_axioms(vec!["Classical.em".to_string()])
///     .with_aspects(vec!["logic".to_string()])
///     .with_time_ms(42)
///     .build()?;
/// ```
pub struct ProofOctadBuilder {
    theorem_name: String,
    goal: Goal,
    prover: ProverKind,
    proof_state: Option<ProofState>,
    status: ProofStatus,
    axioms: Vec<String>,
    aspects: Vec<String>,
    time_ms: u64,
    llm_model: Option<String>,
    parent_proofs: Vec<String>,
    sub_goals: Vec<String>,
    goal_embedding: Vec<f32>,
}

impl ProofOctadBuilder {
    /// Create a new builder for a proof octad.
    pub fn new(theorem_name: &str, goal: &Goal, prover: ProverKind) -> Self {
        ProofOctadBuilder {
            theorem_name: theorem_name.to_string(),
            goal: goal.clone(),
            prover,
            proof_state: None,
            status: ProofStatus::Partial,
            axioms: Vec::new(),
            aspects: Vec::new(),
            time_ms: 0,
            llm_model: None,
            parent_proofs: Vec::new(),
            sub_goals: Vec::new(),
            goal_embedding: Vec::new(),
        }
    }

    /// Set the proof state (required for semantic + temporal modalities).
    pub fn with_proof_state(mut self, proof: &ProofState) -> Self {
        self.proof_state = Some(proof.clone());
        if proof.is_complete() {
            self.status = ProofStatus::Complete;
        }
        self
    }

    /// Set the proof status explicitly.
    pub fn with_status(mut self, status: ProofStatus) -> Self {
        self.status = status;
        self
    }

    /// Set axioms used in the proof.
    pub fn with_axioms(mut self, axioms: Vec<String>) -> Self {
        self.axioms = axioms;
        self
    }

    /// Set aspect tags for search.
    pub fn with_aspects(mut self, aspects: Vec<String>) -> Self {
        self.aspects = aspects;
        self
    }

    /// Set the proof time in milliseconds.
    pub fn with_time_ms(mut self, ms: u64) -> Self {
        self.time_ms = ms;
        self
    }

    /// Set the LLM model tier used for advisory.
    pub fn with_llm_model(mut self, model: &str) -> Self {
        self.llm_model = Some(model.to_string());
        self
    }

    /// Set parent proof dependencies (octad keys).
    pub fn with_dependencies(mut self, deps: Vec<String>) -> Self {
        self.parent_proofs = deps;
        self
    }

    /// Set sub-goal proof IDs.
    pub fn with_sub_goals(mut self, subs: Vec<String>) -> Self {
        self.sub_goals = subs;
        self
    }

    /// Set the neural goal embedding for similarity search.
    pub fn with_embedding(mut self, embedding: Vec<f32>) -> Self {
        self.goal_embedding = embedding;
        self
    }

    /// Build the octad payload.
    pub fn build(self) -> Result<OctadPayload> {
        let now = Utc::now();
        let timestamp = now.to_rfc3339();

        // Generate identities
        let octad_key = proof_encoding::proof_identity(&self.theorem_name, &self.goal, self.prover);
        let cross_prover_id = proof_encoding::goal_identity(&self.theorem_name, &self.goal);

        // Semantic modality: CBOR-encode the proof state
        let proof_blob_b64 = if let Some(ref proof) = self.proof_state {
            let cbor = proof_encoding::encode_proof_state_cbor(proof)
                .context("Failed to encode proof for semantic modality")?;
            base64_encode(&cbor)
        } else {
            String::new()
        };

        let goal_type = classify_goal_type(&self.goal);

        let semantic = SemanticPayload {
            proof_blob_b64,
            status: self.status,
            goal_type,
            prover: format!("{:?}", self.prover),
            axioms_used: self.axioms.clone(),
            llm_model: self.llm_model.clone(),
            advisory_only: self.llm_model.is_some() && self.status != ProofStatus::Complete,
        };

        // Temporal modality: initial version
        let goals_remaining = self
            .proof_state
            .as_ref()
            .map(|p| p.goals.len())
            .unwrap_or(1);

        let tactic_versions = build_tactic_versions(&self.proof_state, &self.prover, &timestamp);

        let temporal = TemporalPayload {
            versions: tactic_versions,
        };

        // Provenance modality: creation record + one per tactic
        let provenance =
            build_provenance_chain(&self.proof_state, &self.prover, &self.axioms, &timestamp);

        // Document modality: searchable text
        let theorem_statement = format!("{}", self.goal.target);
        let goals_text: Vec<String> = self
            .proof_state
            .as_ref()
            .map(|p| p.goals.iter().map(|g| format!("{}", g.target)).collect())
            .unwrap_or_else(|| vec![theorem_statement.clone()]);

        let tactics_text: Vec<String> = self
            .proof_state
            .as_ref()
            .map(|p| p.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        let searchable_text = format!(
            "{} {} {} {}",
            self.theorem_name,
            theorem_statement,
            goals_text.join(" "),
            tactics_text.join(" "),
        );

        let document = DocumentPayload {
            theorem_statement,
            goals_text,
            tactics_text,
            aspects: self.aspects.clone(),
            searchable_text,
        };

        // Graph modality: dependencies
        let graph = GraphPayload {
            depends_on: self.parent_proofs,
            sub_goals: self.sub_goals,
            cross_prover_id,
            prover_id: format!("echidna:prover:{:?}", self.prover),
        };

        // Vector modality: embeddings
        let dimensions = self.goal_embedding.len();
        let vector = VectorPayload {
            goal_embedding: self.goal_embedding,
            model: if dimensions > 0 {
                "echidna-neural-v1".to_string()
            } else {
                "none".to_string()
            },
            dimensions,
        };

        // Tensor + Spatial: reserved
        let mut metrics = HashMap::new();
        metrics.insert("time_ms".to_string(), self.time_ms as f64);
        metrics.insert("goals_remaining".to_string(), goals_remaining as f64);

        let tensor = TensorPayload { metrics };
        let spatial = SpatialPayload {
            origin: format!("echidna-v{}", env!("CARGO_PKG_VERSION")),
        };

        Ok(OctadPayload {
            key: octad_key,
            semantic,
            temporal,
            provenance,
            document,
            graph,
            vector,
            tensor,
            spatial,
        })
    }
}

// ═══════════════════════════════════════════════════════════════════════
// VeriSimDB HTTP Client
// ═══════════════════════════════════════════════════════════════════════

/// Client for VeriSimDB's HTTP API.
///
/// Sends octad payloads to VeriSimDB for persistent storage.
/// Uses reqwest for async HTTP. Falls back gracefully if VeriSimDB
/// is unavailable (proof memory continues in-memory).
///
/// `Clone` is cheap: `reqwest::Client` is internally `Arc`'d, and the
/// base URL is just a `String`. Cloning is required for fire-and-forget
/// `tokio::spawn` writes (e.g. `dispatch::ProverDispatcher::spawn_record_attempt`).
#[derive(Clone)]
pub struct VeriSimDBClient {
    // pub(crate) — the sibling vcl_ut module composes queries directly
    // against the base URL + shared HTTP client rather than going through
    // a narrowed accessor surface. Keeping the crate-local visibility
    // documents that intent without leaking the fields to downstream
    // crates.
    pub(crate) base_url: String,
    pub(crate) http: reqwest::Client,
}

impl VeriSimDBClient {
    /// Create a new VeriSimDB client.
    pub fn new(base_url: &str) -> Self {
        VeriSimDBClient {
            base_url: base_url.trim_end_matches('/').to_string(),
            http: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(10))
                .build()
                .expect("Failed to create HTTP client"),
        }
    }

    /// Store an octad payload in VeriSimDB.
    pub async fn create_octad(&self, payload: &OctadPayload) -> Result<()> {
        let url = format!("{}/api/v1/octads", self.base_url);

        let response = self
            .http
            .post(&url)
            .json(payload)
            .send()
            .await
            .context("Failed to send octad to VeriSimDB")?;

        if response.status().is_success() {
            debug!("Stored octad {} in VeriSimDB", payload.key);
            Ok(())
        } else {
            let status = response.status();
            let body = response.text().await.unwrap_or_default();
            warn!("VeriSimDB returned {}: {}", status, body);
            anyhow::bail!("VeriSimDB returned {}: {}", status, body)
        }
    }

    /// Retrieve an octad by key.
    pub async fn get_octad(&self, key: &str) -> Result<Option<OctadPayload>> {
        let url = format!("{}/api/v1/octads/{}", self.base_url, key);

        let response = self
            .http
            .get(&url)
            .send()
            .await
            .context("Failed to query VeriSimDB")?;

        if response.status().is_success() {
            let octad: OctadPayload = response
                .json()
                .await
                .context("Failed to parse octad from VeriSimDB")?;
            Ok(Some(octad))
        } else if response.status() == reqwest::StatusCode::NOT_FOUND {
            Ok(None)
        } else {
            let status = response.status();
            anyhow::bail!("VeriSimDB returned {} for key {}", status, key)
        }
    }

    /// Update an existing octad.
    pub async fn update_octad(&self, payload: &OctadPayload) -> Result<()> {
        // VeriSimDB uses POST for create-or-update
        self.create_octad(payload).await
    }

    /// Delete an octad by key.
    pub async fn delete_octad(&self, key: &str) -> Result<()> {
        let url = format!("{}/api/v1/octads/{}", self.base_url, key);

        let response = self
            .http
            .delete(&url)
            .send()
            .await
            .context("Failed to delete octad from VeriSimDB")?;

        if response.status().is_success() || response.status() == reqwest::StatusCode::NOT_FOUND {
            Ok(())
        } else {
            anyhow::bail!("VeriSimDB delete failed: {}", response.status())
        }
    }

    /// Check if VeriSimDB is reachable.
    pub async fn health_check(&self) -> bool {
        let url = format!("{}/health", self.base_url);
        self.http
            .get(&url)
            .timeout(std::time::Duration::from_secs(2))
            .send()
            .await
            .map(|r| r.status().is_success())
            .unwrap_or(false)
    }

    /// Record a proof attempt in VeriSimDB's proof_attempts table.
    ///
    /// Posts to `/api/v1/proof_attempts` which writes a row to ClickHouse.
    /// The row is visible to hypatia's proof_strategy_selection rule (H3) via
    /// the mv_prover_success_by_class materialised view, closing the learning
    /// loop: attempt → table → MV → hypatia recommendation → next attempt.
    ///
    /// Returns the `attempt_id` on success. Propagates HTTP errors so callers
    /// can decide whether to retry or continue without persistence.
    pub async fn record_proof_attempt(&self, attempt: &ProofAttempt) -> Result<String> {
        let url = format!("{}/api/v1/proof_attempts", self.base_url);

        let response = self
            .http
            .post(&url)
            .json(attempt)
            .send()
            .await
            .context("Failed to post proof_attempt to VeriSimDB")?;

        if response.status().is_success() {
            debug!(
                "Recorded proof_attempt {} (prover={}, outcome={}) in VeriSimDB",
                attempt.attempt_id, attempt.prover_used, attempt.outcome
            );
            Ok(attempt.attempt_id.clone())
        } else {
            let status = response.status();
            let body = response.text().await.unwrap_or_default();
            warn!("VeriSimDB proof_attempts returned {}: {}", status, body);
            anyhow::bail!("VeriSimDB proof_attempts returned {}: {}", status, body)
        }
    }

    /// Query proof attempts by goal hash (obligation_id).
    ///
    /// Returns all known attempts for this obligation, most recent first, up
    /// to 50 rows.  Maps to:
    ///   `GET /api/v1/proof_attempts?obligation_id={hash}&limit=50`
    ///
    /// Returns `Ok(vec![])` when VeriSimDB has no record for this obligation
    /// (404 or empty body).  Propagates network/parse errors so callers can
    /// decide whether to retry or fall back.
    pub async fn query_by_goal_hash(&self, obligation_id: &str) -> Result<Vec<ProofAttempt>> {
        let url = format!(
            "{}/api/v1/proof_attempts?obligation_id={}&limit=50",
            self.base_url, obligation_id
        );

        let response = self
            .http
            .get(&url)
            .send()
            .await
            .context("Failed to query proof_attempts by obligation_id from VeriSimDB")?;

        if response.status() == reqwest::StatusCode::NOT_FOUND {
            debug!(
                "No proof_attempts found for obligation_id={} (404)",
                obligation_id
            );
            return Ok(vec![]);
        }

        if !response.status().is_success() {
            let status = response.status();
            anyhow::bail!(
                "VeriSimDB proof_attempts query returned {} for obligation_id={}",
                status,
                obligation_id
            );
        }

        // A 200 with an empty JSON array is valid and maps to Ok(vec![]).
        let attempts: Vec<ProofAttempt> = response
            .json()
            .await
            .context("Failed to parse proof_attempts list from VeriSimDB")?;

        debug!(
            "Fetched {} proof_attempt(s) for obligation_id={}",
            attempts.len(),
            obligation_id
        );
        Ok(attempts)
    }

    /// Query the `mv_prover_success_by_class` materialised view.
    ///
    /// Returns a map from prover name → success rate (in `[0.0, 1.0]`) for
    /// the given `obligation_class`.  Maps to:
    ///   `GET /api/v1/mv_prover_success_by_class?class={class}`
    ///
    /// The MV response is a JSON array of objects:
    /// ```json
    /// [{"prover": "coq", "success_rate": 0.85, "total_attempts": 42}, ...]
    /// ```
    ///
    /// Returns `Ok(HashMap::new())` when VeriSimDB has no statistics for the
    /// class (404 or empty array).  Propagates network/parse errors.
    pub async fn query_prover_success_by_class(
        &self,
        obligation_class: &str,
    ) -> Result<HashMap<String, f32>> {
        // Local deserialisation type — mirrors one row in the MV response.
        #[derive(Deserialize)]
        struct ProverSuccessRow {
            prover: String,
            success_rate: f32,
            #[allow(dead_code)]
            total_attempts: u32,
        }

        let url = format!(
            "{}/api/v1/mv_prover_success_by_class?class={}",
            self.base_url, obligation_class
        );

        let response = self
            .http
            .get(&url)
            .send()
            .await
            .context("Failed to query mv_prover_success_by_class from VeriSimDB")?;

        if response.status() == reqwest::StatusCode::NOT_FOUND {
            debug!(
                "No prover success data for class={} (404)",
                obligation_class
            );
            return Ok(HashMap::new());
        }

        if !response.status().is_success() {
            let status = response.status();
            anyhow::bail!(
                "VeriSimDB mv_prover_success_by_class returned {} for class={}",
                status,
                obligation_class
            );
        }

        let rows: Vec<ProverSuccessRow> = response
            .json()
            .await
            .context("Failed to parse mv_prover_success_by_class response from VeriSimDB")?;

        let map: HashMap<String, f32> = rows
            .into_iter()
            .map(|row| (row.prover, row.success_rate))
            .collect();

        debug!(
            "Fetched {} prover success rate(s) for class={}",
            map.len(),
            obligation_class
        );
        Ok(map)
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ProofAttempt — row written to VeriSimDB's proof_attempts table
// ═══════════════════════════════════════════════════════════════════════

/// A single proof attempt record. Matches the JSON body expected by
/// `POST /api/v1/proof_attempts` on verisim-api.
///
/// Field names use snake_case; prover/outcome use lowercase strings matching
/// the ClickHouse Enum8 values ("coq", "lean", ..., "success", "timeout", ...).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofAttempt {
    /// UUID v4 unique to this attempt.
    pub attempt_id: String,
    /// Stable hash of (repo, file, claim) — groups retries of the same obligation.
    pub obligation_id: String,
    /// Repository identifier, e.g. "hyperpolymath/echidna".
    pub repo: String,
    /// File path within the repo, e.g. "proofs/coq/basic.v".
    pub file: String,
    /// Human-readable obligation text.
    pub claim: String,
    /// Obligation class for strategy lookup, e.g. "linearity", "termination".
    pub obligation_class: String,
    /// Prover used ("coq", "lean", "agda", "isabelle", "idris2", "z3", etc.).
    pub prover_used: String,
    /// Outcome ("success", "timeout", "failure", "unknown").
    pub outcome: String,
    pub duration_ms: u64,
    /// Confidence score in [0.0, 1.0].
    pub confidence: f32,
    /// Prior attempt on the same obligation (for retries), or None.
    pub parent_attempt_id: Option<String>,
    /// Strategy used, e.g. "portfolio", "gnn-guided", "manual", "retry".
    pub strategy_tag: String,
    /// ISO-8601 UTC timestamp when the attempt started.
    pub started_at: String,
    /// ISO-8601 UTC timestamp when the attempt completed.
    pub completed_at: String,
    /// Truncated prover stdout/stderr (<=8 KiB recommended).
    pub prover_output: String,
    /// Error message if outcome != success, else None.
    pub error_message: Option<String>,
}

/// Map an echidna `ProverKind` to the lowercase string the endpoint expects.
/// Unknown variants map to "other" — the endpoint's fallback enum value.
pub fn prover_kind_to_str(kind: ProverKind) -> &'static str {
    match kind {
        ProverKind::Coq => "coq",
        ProverKind::Lean => "lean",
        ProverKind::Agda => "agda",
        ProverKind::Isabelle => "isabelle",
        ProverKind::Idris2 => "idris2",
        ProverKind::Z3 => "z3",
        ProverKind::CVC5 => "cvc5",
        ProverKind::AltErgo => "altergo",
        ProverKind::Metamath => "metamath",
        ProverKind::HOLLight => "hol_light",
        ProverKind::Mizar => "mizar",
        ProverKind::HOL4 => "hol4",
        ProverKind::PVS => "pvs",
        ProverKind::ACL2 => "acl2",
        ProverKind::Vampire => "vampire",
        ProverKind::EProver => "eprover",
        _ => "other",
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Helper functions
// ═══════════════════════════════════════════════════════════════════════

/// Classify the goal type for the semantic modality.
fn classify_goal_type(goal: &Goal) -> String {
    use crate::core::Term;
    match &goal.target {
        Term::Pi { .. } => "universal_quantification".to_string(),
        Term::App { func, .. } => match func.as_ref() {
            Term::Const(name) if name == "eq" || name == "Eq" => "equality".to_string(),
            Term::Const(name) if name == "and" || name == "And" => "conjunction".to_string(),
            Term::Const(name) if name == "or" || name == "Or" => "disjunction".to_string(),
            Term::Const(name) if name == "not" || name == "Not" => "negation".to_string(),
            Term::Const(name) if name == "exists" || name == "Exists" => "existential".to_string(),
            _ => "application".to_string(),
        },
        Term::Lambda { .. } => "lambda".to_string(),
        Term::Var(_) => "variable".to_string(),
        Term::Const(_) => "constant".to_string(),
        _ => "other".to_string(),
    }
}

/// Build the temporal version chain from a proof state's tactic history.
fn build_tactic_versions(
    proof_state: &Option<ProofState>,
    prover: &ProverKind,
    timestamp: &str,
) -> Vec<ProofVersion> {
    let mut versions = vec![ProofVersion {
        version: 0,
        timestamp: timestamp.to_string(),
        actor: "echidna-dispatch".to_string(),
        description: "Proof attempt initialised".to_string(),
        goals_remaining: proof_state.as_ref().map(|p| p.goals.len()).unwrap_or(1),
        tactic: None,
    }];

    if let Some(ref proof) = proof_state {
        for (i, tactic) in proof.proof_script.iter().enumerate() {
            versions.push(ProofVersion {
                version: (i + 1) as u64,
                timestamp: timestamp.to_string(),
                actor: format!("{:?}", prover),
                description: format!("Applied tactic: {:?}", tactic),
                goals_remaining: proof.goals.len(), // approximate
                tactic: Some(format!("{:?}", tactic)),
            });
        }

        // Final version if proof is complete
        if proof.is_complete() {
            versions.push(ProofVersion {
                version: (proof.proof_script.len() + 1) as u64,
                timestamp: timestamp.to_string(),
                actor: "echidna-verify".to_string(),
                description: "Proof complete (QED)".to_string(),
                goals_remaining: 0,
                tactic: None,
            });
        }
    }

    versions
}

/// Build the provenance hash chain from a proof state.
fn build_provenance_chain(
    proof_state: &Option<ProofState>,
    prover: &ProverKind,
    axioms: &[String],
    timestamp: &str,
) -> ProvenancePayload {
    let mut records = Vec::new();
    let mut parent_hash = String::new();

    // Record 0: Creation
    let creation_data: HashMap<String, serde_json::Value> = [
        (
            "prover".to_string(),
            serde_json::json!(format!("{:?}", prover)),
        ),
        ("axioms".to_string(), serde_json::json!(axioms)),
    ]
    .into_iter()
    .collect();

    let creation_hash = hash_provenance_record(&parent_hash, "Created", timestamp, &creation_data);
    records.push(ProvenanceRecord {
        hash: creation_hash.clone(),
        parent_hash: parent_hash.clone(),
        event: ProvenanceEvent::Created,
        actor: "echidna-dispatch".to_string(),
        timestamp: timestamp.to_string(),
        data: creation_data,
    });
    parent_hash = creation_hash;

    // Record per tactic
    if let Some(ref proof) = proof_state {
        for tactic in &proof.proof_script {
            let tactic_data: HashMap<String, serde_json::Value> = [(
                "tactic".to_string(),
                serde_json::json!(format!("{:?}", tactic)),
            )]
            .into_iter()
            .collect();

            let tactic_hash =
                hash_provenance_record(&parent_hash, "TacticApplied", timestamp, &tactic_data);
            records.push(ProvenanceRecord {
                hash: tactic_hash.clone(),
                parent_hash: parent_hash.clone(),
                event: ProvenanceEvent::TacticApplied,
                actor: format!("{:?}", prover),
                timestamp: timestamp.to_string(),
                data: tactic_data,
            });
            parent_hash = tactic_hash;
        }

        // Final verification record if complete
        if proof.is_complete() {
            let verify_data = HashMap::new();
            let verify_hash =
                hash_provenance_record(&parent_hash, "Verified", timestamp, &verify_data);
            records.push(ProvenanceRecord {
                hash: verify_hash.clone(),
                parent_hash,
                event: ProvenanceEvent::Verified,
                actor: "echidna-verify".to_string(),
                timestamp: timestamp.to_string(),
                data: verify_data,
            });
        }
    }

    ProvenancePayload { records }
}

/// Hash a provenance record for the hash chain.
fn hash_provenance_record(
    parent_hash: &str,
    event: &str,
    timestamp: &str,
    data: &HashMap<String, serde_json::Value>,
) -> String {
    use sha2::{Digest, Sha256};
    let input = format!(
        "{}:{}:{}:{}",
        parent_hash,
        event,
        timestamp,
        serde_json::to_string(data).unwrap_or_default(),
    );
    format!("{:x}", Sha256::digest(input.as_bytes()))
}

/// Base64-encode bytes (no padding, URL-safe).
fn base64_encode(bytes: &[u8]) -> String {
    // Simple base64 encoding using standard alphabet
    // In production, use the `base64` crate; here we use a compact implementation
    // that avoids adding another dependency.
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut result = String::with_capacity((bytes.len() + 2) / 3 * 4);

    for chunk in bytes.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = chunk.get(1).copied().unwrap_or(0) as u32;
        let b2 = chunk.get(2).copied().unwrap_or(0) as u32;
        let triple = (b0 << 16) | (b1 << 8) | b2;

        result.push(ALPHABET[((triple >> 18) & 0x3F) as usize] as char);
        result.push(ALPHABET[((triple >> 12) & 0x3F) as usize] as char);

        if chunk.len() > 1 {
            result.push(ALPHABET[((triple >> 6) & 0x3F) as usize] as char);
        }
        if chunk.len() > 2 {
            result.push(ALPHABET[(triple & 0x3F) as usize] as char);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, Term};
    use std::collections::HashMap;

    fn sample_goal() -> Goal {
        Goal {
            id: "goal_0".to_string(),
            target: Term::Pi {
                param: "n".to_string(),
                param_type: Box::new(Term::Const("Nat".to_string())),
                body: Box::new(Term::App {
                    func: Box::new(Term::Const("eq".to_string())),
                    args: vec![
                        Term::App {
                            func: Box::new(Term::Const("add".to_string())),
                            args: vec![Term::Var("n".to_string()), Term::Const("0".to_string())],
                        },
                        Term::Var("n".to_string()),
                    ],
                }),
            },
            hypotheses: vec![],
        }
    }

    fn sample_proof_state() -> ProofState {
        ProofState {
            goals: vec![],
            context: Context::default(),
            proof_script: vec![
                Tactic::Induction(Term::Var("n".to_string())),
                Tactic::Simplify,
                Tactic::Reflexivity,
            ],
            metadata: HashMap::new(),
        }
    }

    #[test]
    fn test_build_complete_octad() {
        let goal = sample_goal();
        let proof = sample_proof_state();

        let octad = ProofOctadBuilder::new("nat_add_zero", &goal, ProverKind::Lean)
            .with_proof_state(&proof)
            .with_axioms(vec!["Nat.rec".to_string()])
            .with_aspects(vec!["arithmetic".to_string(), "induction".to_string()])
            .with_time_ms(42)
            .build()
            .expect("Failed to build octad");

        // Key should be a 64-char hex digest
        assert_eq!(octad.key.len(), 64);

        // Semantic modality (ProverKind::Lean is the Lean 4 variant; Lean 3
        // is a sibling ProverKind::Lean3.)
        assert_eq!(octad.semantic.status, ProofStatus::Complete);
        assert_eq!(octad.semantic.prover, "Lean");
        assert!(!octad.semantic.proof_blob_b64.is_empty());
        assert_eq!(octad.semantic.axioms_used, vec!["Nat.rec"]);

        // Temporal modality: initial + 3 tactics + QED = 5 versions
        assert_eq!(octad.temporal.versions.len(), 5);
        assert_eq!(octad.temporal.versions[0].actor, "echidna-dispatch");
        assert_eq!(
            octad.temporal.versions[4].description,
            "Proof complete (QED)"
        );

        // Provenance modality: creation + 3 tactics + verified = 5 records
        assert_eq!(octad.provenance.records.len(), 5);
        // Hash chain integrity: each record's parent_hash matches previous record's hash
        for i in 1..octad.provenance.records.len() {
            assert_eq!(
                octad.provenance.records[i].parent_hash,
                octad.provenance.records[i - 1].hash,
                "Hash chain broken at record {}",
                i,
            );
        }

        // Document modality
        assert!(octad.document.searchable_text.contains("nat_add_zero"));
        assert_eq!(octad.document.aspects, vec!["arithmetic", "induction"]);

        // Graph modality
        assert_eq!(octad.graph.cross_prover_id.len(), 64);
        assert!(octad.graph.prover_id.contains("Lean"));

        // Tensor modality
        assert_eq!(*octad.tensor.metrics.get("time_ms").unwrap(), 42.0);
    }

    #[test]
    fn test_build_partial_octad() {
        let goal = sample_goal();

        let octad = ProofOctadBuilder::new("partial_thm", &goal, ProverKind::Coq)
            .with_status(ProofStatus::Failed)
            .build()
            .expect("Failed to build partial octad");

        assert_eq!(octad.semantic.status, ProofStatus::Failed);
        assert!(octad.semantic.proof_blob_b64.is_empty());
        assert_eq!(octad.temporal.versions.len(), 1); // Only initial version
    }

    #[test]
    fn test_classify_goal_type() {
        let eq_goal = Goal {
            id: "g".to_string(),
            target: Term::App {
                func: Box::new(Term::Const("eq".to_string())),
                args: vec![Term::Var("a".to_string()), Term::Var("b".to_string())],
            },
            hypotheses: vec![],
        };
        assert_eq!(classify_goal_type(&eq_goal), "equality");

        let pi_goal = Goal {
            id: "g".to_string(),
            target: Term::Pi {
                param: "x".to_string(),
                param_type: Box::new(Term::Const("A".to_string())),
                body: Box::new(Term::Var("x".to_string())),
            },
            hypotheses: vec![],
        };
        assert_eq!(classify_goal_type(&pi_goal), "universal_quantification");
    }

    #[test]
    fn test_provenance_hash_chain_integrity() {
        let proof = sample_proof_state();
        let prov = build_provenance_chain(
            &Some(proof),
            &ProverKind::Agda,
            &["ax1".to_string()],
            "2026-03-20T00:00:00Z",
        );

        // First record has empty parent
        assert_eq!(prov.records[0].parent_hash, "");

        // Each subsequent record links to previous
        for i in 1..prov.records.len() {
            assert_eq!(prov.records[i].parent_hash, prov.records[i - 1].hash);
        }

        // All hashes are 64-char hex
        for record in &prov.records {
            assert_eq!(record.hash.len(), 64);
        }
    }

    #[test]
    fn test_base64_encode() {
        assert_eq!(base64_encode(b"hello"), "aGVsbG8");
        assert_eq!(base64_encode(b""), "");
        assert_eq!(base64_encode(b"a"), "YQ");
    }
}
