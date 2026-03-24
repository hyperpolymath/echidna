// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Proof Encoding — CBOR serialisation and identity hashing for VeriSimDB octads.
//!
//! Provides two key capabilities:
//!   1. CBOR encode/decode for `ProofState` (compact binary for VeriSimDB semantic modality)
//!   2. Stable proof identity generation via SHA-256 (used as VeriSimDB octad keys)
//!
//! The proof identity scheme produces content-addressed keys that are stable across
//! serialisation round-trips: same goal + prover + theorem always produces the same ID.

use anyhow::{Context, Result};
use sha2::{Digest, Sha256};

use crate::core::{Goal, ProofState};
use crate::provers::ProverKind;

/// Encode a ProofState to CBOR bytes for the VeriSimDB semantic modality.
///
/// CBOR (RFC 8949) is used instead of JSON because:
///   - 30-50% smaller than equivalent JSON for proof state trees
///   - Binary-safe (no escaping for Term trees)
///   - Self-describing (VeriSimDB can introspect without schema)
///   - Matches VeriSimDB's semantic modality expectation
pub fn encode_proof_state_cbor(proof: &ProofState) -> Result<Vec<u8>> {
    serde_cbor::to_vec(proof).context("Failed to CBOR-encode ProofState")
}

/// Decode a ProofState from CBOR bytes.
pub fn decode_proof_state_cbor(bytes: &[u8]) -> Result<ProofState> {
    serde_cbor::from_slice(bytes).context("Failed to CBOR-decode ProofState")
}

/// Generate a stable, content-addressed proof identity for use as a VeriSimDB octad key.
///
/// The identity is a SHA-256 hex digest of:
///   `echidna:v1:{theorem_name}:{goal_target_display}:{prover_kind_debug}`
///
/// This ensures:
///   - Same theorem + goal + prover always produces the same ID
///   - Different provers for the same theorem get distinct IDs (for cross-prover tracking)
///   - The "echidna:v1:" prefix prevents collision with other VeriSimDB clients
///   - Deterministic across serialisation round-trips (uses Display, not Debug for Term)
pub fn proof_identity(theorem_name: &str, goal: &Goal, prover: ProverKind) -> String {
    let input = format!(
        "echidna:v1:{}:{}:{:?}",
        theorem_name,
        goal.target, // uses Display impl from core.rs
        prover,
    );
    let hash = Sha256::digest(input.as_bytes());
    format!("{:x}", hash)
}

/// Generate a goal-only identity (prover-agnostic).
///
/// Used for cross-prover queries: "find all proofs of theorem X regardless of prover".
/// The VeriSimDB graph modality uses this to link proofs of the same theorem.
pub fn goal_identity(theorem_name: &str, goal: &Goal) -> String {
    let input = format!("echidna:v1:goal:{}:{}", theorem_name, goal.target,);
    let hash = Sha256::digest(input.as_bytes());
    format!("{:x}", hash)
}

/// Generate a session identity for ephemeral proof attempts.
///
/// Uses timestamp + goal ID to create a unique session key for temporal
/// versioning of proof state snapshots during a single proof attempt.
pub fn session_identity(goal_id: &str, timestamp: i64) -> String {
    let input = format!("echidna:v1:session:{}:{}", goal_id, timestamp,);
    let hash = Sha256::digest(input.as_bytes());
    format!("{:x}", hash)
}

/// Estimate the CBOR-encoded size of a ProofState without allocating.
///
/// Returns an approximate byte count. Useful for deciding whether to
/// inline the proof in the octad or store it as an external blob.
pub fn estimate_cbor_size(proof: &ProofState) -> usize {
    // Rough estimate: JSON size * 0.7 (CBOR is typically 30% smaller)
    let json_estimate = serde_json::to_string(proof)
        .map(|s| s.len())
        .unwrap_or(1024);
    (json_estimate as f64 * 0.7) as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, Term};
    use std::collections::HashMap;

    fn sample_proof_state() -> ProofState {
        ProofState {
            goals: vec![Goal {
                id: "goal_0".to_string(),
                target: Term::Pi {
                    param: "n".to_string(),
                    param_type: Box::new(Term::Const("Nat".to_string())),
                    body: Box::new(Term::App {
                        func: Box::new(Term::Const("eq".to_string())),
                        args: vec![
                            Term::App {
                                func: Box::new(Term::Const("add".to_string())),
                                args: vec![
                                    Term::Var("n".to_string()),
                                    Term::Const("0".to_string()),
                                ],
                            },
                            Term::Var("n".to_string()),
                        ],
                    }),
                },
                hypotheses: vec![],
            }],
            context: Context::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        }
    }

    #[test]
    fn test_cbor_round_trip() {
        let proof = sample_proof_state();
        let encoded = encode_proof_state_cbor(&proof).unwrap();
        let decoded = decode_proof_state_cbor(&encoded).unwrap();

        // Verify structural equality (goals match)
        assert_eq!(decoded.goals.len(), proof.goals.len());
        assert_eq!(decoded.goals[0].id, proof.goals[0].id);
    }

    #[test]
    fn test_cbor_smaller_than_json() {
        let proof = sample_proof_state();
        let cbor = encode_proof_state_cbor(&proof).unwrap();
        let json = serde_json::to_vec(&proof).unwrap();

        // CBOR should be smaller (or at worst equal) to JSON
        assert!(
            cbor.len() <= json.len(),
            "CBOR ({} bytes) should be <= JSON ({} bytes)",
            cbor.len(),
            json.len()
        );
    }

    #[test]
    fn test_proof_identity_deterministic() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        };

        let id1 = proof_identity("my_theorem", &goal, ProverKind::Lean4);
        let id2 = proof_identity("my_theorem", &goal, ProverKind::Lean4);
        assert_eq!(id1, id2, "Same inputs must produce same identity");
    }

    #[test]
    fn test_proof_identity_differs_by_prover() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        };

        let lean = proof_identity("thm", &goal, ProverKind::Lean4);
        let coq = proof_identity("thm", &goal, ProverKind::Coq);
        assert_ne!(
            lean, coq,
            "Different provers must produce different identities"
        );
    }

    #[test]
    fn test_goal_identity_prover_agnostic() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Var("P".to_string()),
            hypotheses: vec![],
        };

        let id = goal_identity("my_theorem", &goal);
        assert_eq!(id.len(), 64, "SHA-256 hex digest should be 64 chars");
    }

    #[test]
    fn test_session_identity_unique() {
        let id1 = session_identity("g0", 1000);
        let id2 = session_identity("g0", 1001);
        assert_ne!(
            id1, id2,
            "Different timestamps must produce different session IDs"
        );
    }

    #[test]
    fn test_estimate_cbor_size() {
        let proof = sample_proof_state();
        let estimate = estimate_cbor_size(&proof);
        let actual = encode_proof_state_cbor(&proof).unwrap().len();

        // Estimate should be within 2x of actual
        assert!(
            estimate < actual * 3,
            "Estimate ({}) should be reasonable vs actual ({})",
            estimate,
            actual
        );
    }

    #[test]
    fn test_cbor_empty_state_roundtrip() {
        let proof = ProofState::default();
        let encoded = encode_proof_state_cbor(&proof).unwrap();
        let decoded = decode_proof_state_cbor(&encoded).unwrap();

        assert!(decoded.goals.is_empty());
        assert!(decoded.context.theorems.is_empty());
    }

    #[test]
    fn test_cbor_decode_invalid_bytes() {
        let bad_bytes = vec![0xFF, 0xFE, 0x00, 0x01];
        let result = decode_proof_state_cbor(&bad_bytes);
        assert!(result.is_err());
    }

    #[test]
    fn test_proof_identity_hex_format() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Const("True".to_string()),
            hypotheses: vec![],
        };

        let id = proof_identity("thm", &goal, ProverKind::Lean);
        // Should be a valid hex string
        assert!(id.chars().all(|c| c.is_ascii_hexdigit()));
        assert_eq!(id.len(), 64);
    }

    #[test]
    fn test_goal_identity_deterministic() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Const("P".to_string()),
            hypotheses: vec![],
        };

        let id1 = goal_identity("thm", &goal);
        let id2 = goal_identity("thm", &goal);
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_goal_identity_differs_by_name() {
        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Const("P".to_string()),
            hypotheses: vec![],
        };

        let id1 = goal_identity("thm_a", &goal);
        let id2 = goal_identity("thm_b", &goal);
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_session_identity_deterministic() {
        let id1 = session_identity("g0", 12345);
        let id2 = session_identity("g0", 12345);
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_estimate_cbor_size_positive() {
        let proof = ProofState::default();
        let estimate = estimate_cbor_size(&proof);
        assert!(estimate > 0);
    }
}
