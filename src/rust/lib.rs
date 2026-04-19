// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA: Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
//!
//! A neurosymbolic theorem proving platform supporting 12 theorem provers
//! with aspect tagging, OpenCyc integration, and neural premise selection.

pub mod agent;
pub mod anomaly_detection;
pub mod aspect;
pub mod core;
pub mod disciplines; // Canonical TypeDiscipline taxonomy (katagoria transition)
pub mod dispatch;
pub mod exchange;
pub mod executor;
pub mod ffi;
pub mod gnn; // Graph Neural Network integration for proof search guidance
pub mod groove; // Gossamer Groove discovery endpoint (port 9000)
pub mod integrity;
pub mod learning; // Continuous self-learning loop (MCTS + self-play + curriculum + daemon)
pub mod llm; // Frontier LLM advisor (via BoJ Server)
pub mod neural;
pub mod parsers;
#[cfg(feature = "verisim")]
pub mod proof_encoding; // CBOR encoding + proof identity hashing
pub mod proof_search; // Chapel parallel proof search (optional feature)
pub mod provers;
pub mod types; // Native type-system decorations (multiplicity, effects, modality, temporal, semiring, …)
pub mod verification;
#[cfg(feature = "verisim")]
pub mod verisim_bridge; // VeriSimDB 8-modality octad integration
pub mod vcl_ut; // VCL-UT: 10-level type-safe cross-prover query language

pub use agent::{AgentConfig, AgentCore};
pub use core::{ProofState, Tactic, TacticResult, Term};
pub use disciplines::{DisciplineFamily, TypeDiscipline};
pub use gnn::{GnnClient, GnnGuidedSearch, ProofGraph, ProofGraphBuilder};
pub use llm::{LlmAdvisor, LlmConfig};
pub use provers::{ProverBackend, ProverConfig, ProverKind};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
