// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Persistent proof entities for the Verisim E-R schema.
//!
//! The existing `proof_encoding::proof_identity` function produces a stable
//! SHA-256 hex digest for every `(theorem, goal, prover)` triple, but that
//! digest lives only as `OctadPayload.key`.  Downstream entities
//! (ProofAttempt, PortfolioResult, MutationResult, ParetoEntry, certificates,
//! integrity records, training corpora) cannot FK into a `Proof` row because
//! no `Proof` row exists — they each carry their own loose references to
//! theorem names and prover strings.  This module materialises the missing
//! entities so the proof territory has an actual map:
//!
//!   * [`Proof`]             — stable primary key with explicit
//!                             `theorem_hash` and `goal_hash` for cross-prover
//!                             and cross-goal joins.
//!   * [`TacticApplication`] — one row per tactic step; makes the proof DAG
//!                             reconstructable.
//!   * [`ProofVersion`]      — append-only snapshot log so the temporal
//!                             evolution of a proof is durable, not just
//!                             renderable in `OctadPayload.temporal`.
//!   * [`ProofStateRecord`]  — typed training-corpus schema replacing the
//!                             untyped JSONL dict.
//!
//! All four types serialise to JSON/CBOR and are intended to be posted to
//! Verisim alongside — not instead of — the existing `OctadPayload`.  An
//! incremental migration strategy keeps the current octad-posting path
//! working while downstream consumers start reading the new FK-structured
//! tables.

use chrono::Utc;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::core::{Goal, ProofState, Tactic};
use crate::proof_encoding::{goal_identity, proof_identity, session_identity};
use crate::provers::ProverKind;

// ═══════════════════════════════════════════════════════════════════════
// Theorem identity — rename-stable hash of the theorem name.
// ═══════════════════════════════════════════════════════════════════════

/// SHA-256 hex digest of the theorem name, used as `Proof.theorem_hash`.
///
/// The explicit hash lets queries like "all proofs of theorem X" index on
/// a fixed-width column instead of a variable-length name string.  Rename
/// drift still affects the hash — if the *name* changes, the hash changes —
/// but that is the correct semantics: a renamed theorem is a different
/// entity from the E-R perspective.
pub fn theorem_identity(theorem_name: &str) -> String {
    let input = format!("echidna:v1:theorem:{}", theorem_name);
    format!("{:x}", Sha256::digest(input.as_bytes()))
}

// ═══════════════════════════════════════════════════════════════════════
// Proof — first-class entity materialising the identity triple.
// ═══════════════════════════════════════════════════════════════════════

/// A proof of a specific goal by a specific prover of a specific theorem.
///
/// `id` is the primary key: the SHA-256 digest produced by
/// `proof_encoding::proof_identity`, identical to `OctadPayload.key`.  Same
/// `(theorem, goal, prover)` triple always produces the same id, which is
/// what makes the entity content-addressed.
///
/// `theorem_hash` and `goal_hash` are independent digests kept alongside the
/// primary key so queries can join on them directly without re-deriving
/// the triple from `id`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Proof {
    /// Primary key — `proof_encoding::proof_identity` hex digest.
    pub id: String,
    /// `goal_identity` digest (prover-agnostic, cross-prover joins).
    pub goal_hash: String,
    /// `theorem_identity` digest.
    pub theorem_hash: String,
    /// Human-readable theorem name (display only; joins use `theorem_hash`).
    pub theorem_name: String,
    /// Prover that produced this proof.
    pub prover: ProverKind,
    /// ISO-8601 timestamp when the row was first materialised.
    pub first_seen: String,
}

impl Proof {
    /// Derive a `Proof` from its source triple.  All three hashes are
    /// computed here so no caller can supply a mismatched set.
    pub fn new(theorem_name: &str, goal: &Goal, prover: ProverKind) -> Self {
        Proof {
            id: proof_identity(theorem_name, goal, prover),
            goal_hash: goal_identity(theorem_name, goal),
            theorem_hash: theorem_identity(theorem_name),
            theorem_name: theorem_name.to_string(),
            prover,
            first_seen: Utc::now().to_rfc3339(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// TacticApplication — per-step record of the proof DAG.
// ═══════════════════════════════════════════════════════════════════════

/// Outcome of a tactic application.
///
/// MCTS and agentic search gain training signal from failed applications as
/// well as successful ones, so the schema persists both.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum TacticStatus {
    /// Tactic produced a new state; further goals may remain.
    Success,
    /// Tactic closed every remaining goal (QED).
    Closed,
    /// Tactic failed; the error message is preserved verbatim.
    Error(String),
}

/// A single tactic applied to a state, with the status and the post-step
/// goal count.  Rows are indexed by `proof_id` and ordered by `step` so the
/// full tactic DAG of a proof can be reconstructed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticApplication {
    /// FK → [`Proof::id`].
    pub proof_id: String,
    /// Monotonic step index (0-based) within the proof.
    pub step: u32,
    /// The tactic that was applied.
    pub tactic: Tactic,
    /// `goal_identity` digest of the goal the tactic targeted.
    pub goal_hash: String,
    /// Outcome of the application.
    pub status: TacticStatus,
    /// Number of goals remaining after the tactic (0 = QED for this branch).
    pub goals_after: u32,
    /// Wall-clock duration for the application, in milliseconds.
    pub duration_ms: u64,
    /// ISO-8601 timestamp when the tactic was applied.
    pub applied_at: String,
}

impl TacticApplication {
    /// Build a `TacticApplication` row for a step that closed some subset of
    /// the goal tree.  `goal` identifies which specific goal was targeted;
    /// `goals_after` is taken from the post-tactic state.
    pub fn record(
        proof: &Proof,
        step: u32,
        goal: &Goal,
        tactic: &Tactic,
        status: TacticStatus,
        goals_after: u32,
        duration_ms: u64,
    ) -> Self {
        TacticApplication {
            proof_id: proof.id.clone(),
            step,
            tactic: tactic.clone(),
            goal_hash: goal_identity(&proof.theorem_name, goal),
            status,
            goals_after,
            duration_ms,
            applied_at: Utc::now().to_rfc3339(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ProofVersion — append-only snapshot log.
// ═══════════════════════════════════════════════════════════════════════

/// Append-only snapshot of a proof's state at a point in time.
///
/// `OctadPayload.temporal.versions` is render-only: it reflects the current
/// in-memory state of the proof.  Persisting `ProofVersion` rows gives a
/// durable audit log that survives solver restarts and lets Verisim replay
/// how a proof evolved.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofVersion {
    /// FK → [`Proof::id`].
    pub proof_id: String,
    /// Monotonic version number (0 = initial state).
    pub version: u32,
    /// `session_identity` digest unique per `(proof_id, version)`.
    pub snapshot_id: String,
    /// Number of goals remaining in this snapshot.
    pub goals_remaining: u32,
    /// Whether this snapshot closes the proof.
    pub is_qed: bool,
    /// Actor: e.g. `"echidna-auto"`, `"mcts"`, `"user:jdaj"`.
    pub actor: String,
    /// ISO-8601 timestamp.
    pub recorded_at: String,
}

impl ProofVersion {
    /// Initial snapshot (`version = 0`) of a newly-created proof.
    pub fn initial(proof: &Proof, state: &ProofState, actor: &str) -> Self {
        let ts = Utc::now().timestamp();
        let seed = format!("{}:v0", proof.id);
        ProofVersion {
            proof_id: proof.id.clone(),
            version: 0,
            snapshot_id: session_identity(&seed, ts),
            goals_remaining: state.goals.len() as u32,
            is_qed: state.is_complete(),
            actor: actor.to_string(),
            recorded_at: Utc::now().to_rfc3339(),
        }
    }

    /// Successor snapshot; `prev` supplies the `proof_id` and version
    /// counter.  Passing a stale `prev` will produce a correctly-chained
    /// `version + 1` regardless of real-world timing drift.
    pub fn next(prev: &ProofVersion, state: &ProofState, actor: &str) -> Self {
        let ts = Utc::now().timestamp();
        let next_version = prev.version + 1;
        let seed = format!("{}:v{}", prev.proof_id, next_version);
        ProofVersion {
            proof_id: prev.proof_id.clone(),
            version: next_version,
            snapshot_id: session_identity(&seed, ts),
            goals_remaining: state.goals.len() as u32,
            is_qed: state.is_complete(),
            actor: actor.to_string(),
            recorded_at: Utc::now().to_rfc3339(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ProofStateRecord — typed corpus schema.
// ═══════════════════════════════════════════════════════════════════════

/// Typed training-corpus record.
///
/// Replaces the ad-hoc JSONL dict the Julia extractors emit today.  A
/// `ProofStateRecord` is one example per `(proof_id, step)` pair and
/// carries everything the trainer needs without per-prover divergence:
///
///   * `proof_id` + `step` connect the record back to the `Proof` and
///     `TacticApplication` rows for provenance.
///   * `prover_version` captures the solver build so MRR deltas across
///     versions can be attributed.
///   * `state_cbor_b64` is a round-trippable `ProofState` blob so the
///     trainer can reconstruct the pre-tactic state exactly — the JSONL
///     format loses tree structure.
///   * `label_confidence` separates human-verified ground truth from
///     weakly-labelled heuristics.
///
/// Existing extractors can keep emitting legacy JSONL; new extractors
/// should emit this schema so downstream consumers gain FK discipline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStateRecord {
    /// FK → [`Proof::id`].
    pub proof_id: String,
    /// Matches [`TacticApplication::step`].
    pub step: u32,
    /// `goal_identity` digest for this step.
    pub goal_hash: String,
    /// Lowercase prover tag, matching `prover_kind_to_str`.
    pub prover: String,
    /// Solver version string, e.g. `"4.12.0"`.  Empty when unknown.
    pub prover_version: String,
    /// CBOR-encoded `ProofState`, base64-armored for JSONL transport.
    pub state_cbor_b64: String,
    /// Optional pre-computed feature vector.  `None` if the extractor did
    /// not embed features and the trainer is expected to derive them.
    pub features: Option<Vec<f32>>,
    /// Relevant premise names — the label for premise-selection training.
    pub relevant_premises: Vec<String>,
    /// Confidence in the label (0.0 = heuristic, 1.0 = human-verified).
    pub label_confidence: f32,
    /// Upstream source path, e.g. `"external_corpora/mathlib4/Mathlib/..."`.
    pub source: String,
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Term;

    fn sample_goal() -> Goal {
        Goal {
            id: "g0".to_string(),
            target: Term::Const("True".to_string()),
            hypotheses: vec![],
        }
    }

    #[test]
    fn proof_id_matches_proof_identity() {
        let goal = sample_goal();
        let p = Proof::new("mythm", &goal, ProverKind::Lean);
        assert_eq!(p.id, proof_identity("mythm", &goal, ProverKind::Lean));
    }

    #[test]
    fn proof_hashes_are_distinct() {
        let goal = sample_goal();
        let p = Proof::new("mythm", &goal, ProverKind::Lean);
        assert_ne!(p.id, p.goal_hash);
        assert_ne!(p.id, p.theorem_hash);
        assert_ne!(p.goal_hash, p.theorem_hash);
    }

    #[test]
    fn theorem_identity_is_deterministic() {
        assert_eq!(theorem_identity("foo"), theorem_identity("foo"));
        assert_ne!(theorem_identity("foo"), theorem_identity("bar"));
        assert_eq!(theorem_identity("foo").len(), 64);
    }

    #[test]
    fn proof_cross_prover_share_goal_and_theorem_hash() {
        let goal = sample_goal();
        let lean = Proof::new("thm", &goal, ProverKind::Lean);
        let coq = Proof::new("thm", &goal, ProverKind::Coq);
        assert_ne!(lean.id, coq.id);
        assert_eq!(lean.goal_hash, coq.goal_hash);
        assert_eq!(lean.theorem_hash, coq.theorem_hash);
    }

    #[test]
    fn tactic_application_records_fk() {
        let goal = sample_goal();
        let p = Proof::new("thm", &goal, ProverKind::Z3);
        let tac = Tactic::Reflexivity;
        let app = TacticApplication::record(&p, 0, &goal, &tac, TacticStatus::Closed, 0, 12);
        assert_eq!(app.proof_id, p.id);
        assert_eq!(app.step, 0);
        assert_eq!(app.goals_after, 0);
        assert_eq!(app.status, TacticStatus::Closed);
        assert_eq!(app.goal_hash, goal_identity("thm", &goal));
    }

    #[test]
    fn proof_version_chains_monotonically() {
        let goal = sample_goal();
        let p = Proof::new("thm", &goal, ProverKind::Z3);
        let state = ProofState::new(goal.target.clone());
        let v0 = ProofVersion::initial(&p, &state, "echidna-auto");
        let v1 = ProofVersion::next(&v0, &state, "echidna-auto");
        let v2 = ProofVersion::next(&v1, &state, "echidna-auto");
        assert_eq!(v0.version, 0);
        assert_eq!(v1.version, 1);
        assert_eq!(v2.version, 2);
        assert_eq!(v0.proof_id, p.id);
        assert_eq!(v1.proof_id, p.id);
        assert_ne!(v0.snapshot_id, v1.snapshot_id);
    }

    #[test]
    fn proof_version_marks_qed_when_state_is_complete() {
        let goal = sample_goal();
        let p = Proof::new("thm", &goal, ProverKind::Z3);
        let open = ProofState::new(goal.target.clone());
        let closed = ProofState::default();
        let v_open = ProofVersion::initial(&p, &open, "mcts");
        let v_closed = ProofVersion::next(&v_open, &closed, "mcts");
        assert!(!v_open.is_qed);
        assert!(v_closed.is_qed);
        assert_eq!(v_closed.goals_remaining, 0);
    }

    #[test]
    fn proof_state_record_round_trips_via_serde() {
        let rec = ProofStateRecord {
            proof_id: "abc".to_string(),
            step: 3,
            goal_hash: "def".to_string(),
            prover: "lean".to_string(),
            prover_version: "4.12.0".to_string(),
            state_cbor_b64: "Zm9v".to_string(),
            features: Some(vec![0.1, 0.2, 0.3]),
            relevant_premises: vec!["Nat.add_comm".to_string()],
            label_confidence: 0.9,
            source: "external_corpora/mathlib4/foo.lean".to_string(),
        };
        let json = serde_json::to_string(&rec).unwrap();
        let back: ProofStateRecord = serde_json::from_str(&json).unwrap();
        assert_eq!(back.proof_id, rec.proof_id);
        assert_eq!(back.features, rec.features);
        assert!((back.label_confidence - rec.label_confidence).abs() < 1e-6);
    }
}
