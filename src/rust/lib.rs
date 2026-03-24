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
pub mod dispatch;
pub mod exchange;
pub mod executor;
pub mod ffi;
pub mod groove; // Gossamer Groove discovery endpoint (port 9000)
pub mod integrity;
pub mod llm; // Frontier LLM advisor (via BoJ Server)
pub mod neural;
pub mod parsers;
#[cfg(feature = "verisimdb")]
pub mod proof_encoding; // CBOR encoding + proof identity hashing
pub mod proof_search; // Chapel parallel proof search (optional feature)
pub mod provers;
pub mod verification;
#[cfg(feature = "verisimdb")]
pub mod verisimdb_bridge; // VeriSimDB 8-modality octad integration
pub mod vql_ut; // VQL-UT: 10-level type-safe cross-prover query language

pub use agent::{AgentConfig, AgentCore};
pub use core::{ProofState, Tactic, TacticResult, Term};
pub use llm::{LlmAdvisor, LlmConfig};
pub use provers::{ProverBackend, ProverConfig, ProverKind};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
