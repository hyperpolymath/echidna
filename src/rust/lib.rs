// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA: Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
//!
//! A neurosymbolic theorem proving platform supporting 12 theorem provers
//! with aspect tagging, OpenCyc integration, and neural premise selection.

pub mod core;
pub mod provers;
pub mod parsers;
pub mod neural;
pub mod aspect;
pub mod agent;
pub mod ffi;
pub mod anomaly_detection;
pub mod proof_search; // Chapel parallel proof search (optional feature)

pub use core::{ProofState, Term, Tactic, TacticResult};
pub use provers::{ProverBackend, ProverKind, ProverConfig};
pub use agent::{AgentCore, AgentConfig};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
