//! Prover dispatcher - communicates with ECHIDNA Core

pub mod echidna_client;

pub use echidna_client::EchidnaClient;

use serde::{Deserialize, Serialize};

/// Proof verification result from ECHIDNA
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofResult {
    pub status: ProofStatus,
    pub message: String,
    pub prover_output: String,
    pub duration_ms: u64,
    pub artifacts: Vec<String>,
}

/// Proof verification status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ProofStatus {
    Verified,
    Failed,
    Timeout,
    Error,
    Unknown,
}

/// Prover kind matching ECHIDNA's supported backends
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ProverKind {
    // Tier 1 (complete in ECHIDNA)
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    Cvc5,
    // Tier 2 (complete in ECHIDNA)
    Metamath,
    HolLight,
    Mizar,
    // Tier 3 (stubs in ECHIDNA)
    Pvs,
    Acl2,
    Hol4,
}

impl ProverKind {
    /// Get file extensions associated with this prover
    pub fn file_extensions(&self) -> &[&str] {
        match self {
            Self::Agda => &[".agda", ".lagda", ".lagda.md"],
            Self::Coq => &[".v"],
            Self::Lean => &[".lean"],
            Self::Isabelle => &[".thy"],
            Self::Z3 => &[".smt2", ".z3"],
            Self::Cvc5 => &[".smt2", ".cvc5"],
            Self::Metamath => &[".mm"],
            Self::HolLight => &[".ml"],
            Self::Mizar => &[".miz"],
            Self::Pvs => &[".pvs"],
            Self::Acl2 => &[".lisp", ".acl2"],
            Self::Hol4 => &[".sml"],
        }
    }

    /// Get the tier (1 = complete, 2 = complete, 3 = stub)
    pub fn tier(&self) -> u8 {
        match self {
            Self::Agda | Self::Coq | Self::Lean | Self::Isabelle | Self::Z3 | Self::Cvc5 => 1,
            Self::Metamath | Self::HolLight | Self::Mizar => 2,
            Self::Pvs | Self::Acl2 | Self::Hol4 => 3,
        }
    }

    /// Human-readable name
    pub fn display_name(&self) -> &str {
        match self {
            Self::Agda => "Agda",
            Self::Coq => "Coq",
            Self::Lean => "Lean 4",
            Self::Isabelle => "Isabelle/HOL",
            Self::Z3 => "Z3",
            Self::Cvc5 => "CVC5",
            Self::Metamath => "Metamath",
            Self::HolLight => "HOL Light",
            Self::Mizar => "Mizar",
            Self::Pvs => "PVS",
            Self::Acl2 => "ACL2",
            Self::Hol4 => "HOL4",
        }
    }

    /// Detect prover from file extension
    pub fn from_extension(ext: &str) -> Option<Self> {
        let ext = ext.to_lowercase();
        let ext = if ext.starts_with('.') { ext } else { format!(".{}", ext) };

        for prover in Self::all() {
            if prover.file_extensions().iter().any(|e| e.to_lowercase() == ext) {
                return Some(prover);
            }
        }
        None
    }

    /// All prover variants
    pub fn all() -> impl Iterator<Item = Self> {
        [
            Self::Agda,
            Self::Coq,
            Self::Lean,
            Self::Isabelle,
            Self::Z3,
            Self::Cvc5,
            Self::Metamath,
            Self::HolLight,
            Self::Mizar,
            Self::Pvs,
            Self::Acl2,
            Self::Hol4,
        ]
        .into_iter()
    }
}

/// Tactic suggestion from ECHIDNA's Julia ML component
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticSuggestion {
    pub tactic: String,
    pub confidence: f64,
    pub explanation: Option<String>,
}
