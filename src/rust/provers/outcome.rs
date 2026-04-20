// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Structured prover outcome types.
//!
//! [`ProverOutcome`] provides a richer alternative to a plain `bool` for
//! verification results, distinguishing proved goals, counterexamples,
//! timeouts, input errors, inconsistent premises, and system failures.

use serde::{Deserialize, Serialize};

/// Classification of a prover verification result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProverOutcome {
    /// The goal was proved (e.g. negation is UNSAT).
    Proved { elapsed_ms: u64 },

    /// The premises / axioms are themselves inconsistent — any goal follows
    /// trivially, so the proof result cannot be trusted.
    InconsistentPremises { detail: Option<String> },

    /// The prover terminated without proving the goal.
    NoProofFound {
        elapsed_ms: u64,
        reason: Option<String>,
    },

    /// The goal uses a feature / logic fragment the prover does not support.
    UnsupportedFeature { feature: String },

    /// The input was malformed or violated the prover's expectations.
    InvalidInput {
        reason: String,
        location: Option<String>,
    },

    /// The prover timed out before reaching a verdict.
    Timeout { limit_secs: u64 },

    /// An error internal to the prover (crash, assertion failure, etc.).
    ProverError {
        detail: String,
        exit_code: Option<i32>,
    },

    /// A system-level error (binary not found, I/O failure, etc.).
    SystemError { detail: String },
}

impl ProverOutcome {
    /// Returns `true` when the outcome represents a successful proof.
    pub fn is_proved(&self) -> bool {
        matches!(self, Self::Proved { .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proved_is_proved() {
        let o = ProverOutcome::Proved { elapsed_ms: 42 };
        assert!(o.is_proved());
    }

    #[test]
    fn timeout_is_not_proved() {
        let o = ProverOutcome::Timeout { limit_secs: 60 };
        assert!(!o.is_proved());
    }

    #[test]
    fn roundtrips_through_json() {
        let o = ProverOutcome::NoProofFound {
            elapsed_ms: 100,
            reason: Some("counterexample".to_string()),
        };
        let json = serde_json::to_string(&o).unwrap();
        let back: ProverOutcome = serde_json::from_str(&json).unwrap();
        assert_eq!(o, back);
    }
}
