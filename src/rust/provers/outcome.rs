// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Prover outcome taxonomy.
//!
//! Every call to a prover backend's `check()` method returns a `ProverOutcome`.
//! The variants are deliberately disjoint and name *what kind* of result
//! occurred, so that downstream code (dispatch, trust scoring, the Julia ML
//! arbiter, the sanity suite) can reason epistemically about outcomes rather
//! than conflating "unproved" with "errored" or "timed out".
//!
//! ## Invariants
//!
//! - `status_str()` is unique per variant and stable across serialisation.
//! - `is_proved()` is true iff the variant is `Proved`.
//! - `is_conclusive()` covers the three variants where the prover produced
//!   a well-defined mathematical answer: `Proved`, `NoProofFound`,
//!   `InconsistentPremises`.
//! - `is_retryable()` is true only for `Timeout` (the user may retry with a
//!   larger budget).
//! - `is_input_problem()` covers user-input failures — `InvalidInput`,
//!   `UnsupportedFeature`.
//! - `has_suspect_premises()` is true only for `InconsistentPremises` —
//!   signals that a vacuous "everything follows" situation was detected.
//!
//! ## Error classification
//!
//! `classify_anyhow_error()` inspects the string form of an `anyhow::Error`
//! and maps it to the most specific variant.  The order of checks matters:
//! timeout → parse/syntax → system (OS/spawn) → unsupported → other.

use serde::{Deserialize, Serialize};
use std::fmt;

/// The 8-variant outcome taxonomy for a single prover invocation.
///
/// See module documentation for invariants and classification rules.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ProverOutcome {
    /// The prover established the goal (UNSAT of the negation for SMT,
    /// Qed for interactive provers, verified-true for model checkers).
    Proved {
        /// Wall-clock time the prover spent deciding, in milliseconds.
        elapsed_ms: u64,
    },
    /// The prover ran to completion but could not prove the goal.
    /// For SMT solvers this is typically a `sat` reply to the negation.
    NoProofFound {
        elapsed_ms: u64,
        /// Optional one-line explanation (e.g. "SMT returned sat with model").
        reason: Option<String>,
    },
    /// The input was malformed — parse error, unknown symbol, etc.
    /// This is a *user* problem, not a prover problem.
    InvalidInput {
        reason: String,
        /// Optional line / character offset when the parser reports one.
        location: Option<usize>,
    },
    /// The prover reports that the input uses a logic / feature it does
    /// not support. Distinct from `InvalidInput` — the syntax is legal but
    /// the semantics are out of scope for this backend.
    UnsupportedFeature { feature: String },
    /// The prover was interrupted by the configured timeout.
    /// Retryable with a larger budget.
    Timeout { limit_secs: u64 },
    /// The premises (axioms / hypotheses / goal set) are mutually
    /// unsatisfiable.  Anything follows trivially, so an unqualified
    /// PROVED would be epistemically worthless.  The system flags this
    /// explicitly so that callers can decide what to do.
    InconsistentPremises { detail: Option<String> },
    /// The prover itself failed (crash, internal assertion, non-zero exit
    /// without a recognised error token).
    ProverError {
        detail: String,
        exit_code: Option<i32>,
    },
    /// The surrounding system failed (binary not found, IO error,
    /// permission denied, etc.) — nothing to do with the prover's logic.
    SystemError { detail: String },
}

impl Default for ProverOutcome {
    /// Default is the most conservative variant: `SystemError`.  A default
    /// constructor must never silently pass as success *or* a well-defined
    /// failure; `SystemError` forces callers to notice.
    fn default() -> Self {
        ProverOutcome::SystemError {
            detail: "uninitialised ProverOutcome".to_string(),
        }
    }
}

impl ProverOutcome {
    /// Stable, unique string tag for this variant.  Used in logs, wire
    /// formats, and the Julia ML arbiter's feature table.
    pub fn status_str(&self) -> &'static str {
        match self {
            ProverOutcome::Proved { .. } => "PROVED",
            ProverOutcome::NoProofFound { .. } => "NO_PROOF_FOUND",
            ProverOutcome::InvalidInput { .. } => "INVALID_INPUT",
            ProverOutcome::UnsupportedFeature { .. } => "UNSUPPORTED_FEATURE",
            ProverOutcome::Timeout { .. } => "TIMEOUT",
            ProverOutcome::InconsistentPremises { .. } => "INCONSISTENT_PREMISES",
            ProverOutcome::ProverError { .. } => "PROVER_ERROR",
            ProverOutcome::SystemError { .. } => "SYSTEM_ERROR",
        }
    }

    /// `true` iff the outcome is `Proved`.
    pub fn is_proved(&self) -> bool {
        matches!(self, ProverOutcome::Proved { .. })
    }

    /// `true` iff the prover produced a well-defined mathematical answer.
    /// Proved, NoProofFound, and InconsistentPremises are all conclusive;
    /// timeouts, input errors, and system errors are not.
    pub fn is_conclusive(&self) -> bool {
        matches!(
            self,
            ProverOutcome::Proved { .. }
                | ProverOutcome::NoProofFound { .. }
                | ProverOutcome::InconsistentPremises { .. }
        )
    }

    /// `true` iff re-running with a larger budget might help.
    pub fn is_retryable(&self) -> bool {
        matches!(self, ProverOutcome::Timeout { .. })
    }

    /// `true` iff the outcome is caused by bad user input.
    pub fn is_input_problem(&self) -> bool {
        matches!(
            self,
            ProverOutcome::InvalidInput { .. } | ProverOutcome::UnsupportedFeature { .. }
        )
    }

    /// `true` iff the premise set is inconsistent — caller should treat
    /// any "proved" conclusion with extreme suspicion.
    pub fn has_suspect_premises(&self) -> bool {
        matches!(self, ProverOutcome::InconsistentPremises { .. })
    }
}

impl fmt::Display for ProverOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProverOutcome::Proved { elapsed_ms } => {
                write!(f, "PROVED in {}ms", elapsed_ms)
            },
            ProverOutcome::NoProofFound { elapsed_ms, reason } => match reason {
                Some(r) => write!(f, "NO_PROOF_FOUND in {}ms ({})", elapsed_ms, r),
                None => write!(f, "NO_PROOF_FOUND in {}ms", elapsed_ms),
            },
            ProverOutcome::InvalidInput { reason, location } => match location {
                Some(l) => write!(f, "INVALID_INPUT at {}: {}", l, reason),
                None => write!(f, "INVALID_INPUT: {}", reason),
            },
            ProverOutcome::UnsupportedFeature { feature } => {
                write!(f, "UNSUPPORTED_FEATURE: {}", feature)
            },
            ProverOutcome::Timeout { limit_secs } => {
                write!(f, "TIMEOUT after {}s", limit_secs)
            },
            ProverOutcome::InconsistentPremises { detail } => match detail {
                Some(d) => write!(f, "INCONSISTENT_PREMISES: {}", d),
                None => write!(f, "INCONSISTENT_PREMISES"),
            },
            ProverOutcome::ProverError { detail, exit_code } => match exit_code {
                Some(c) => write!(f, "PROVER_ERROR (exit {}): {}", c, detail),
                None => write!(f, "PROVER_ERROR: {}", detail),
            },
            ProverOutcome::SystemError { detail } => write!(f, "SYSTEM_ERROR: {}", detail),
        }
    }
}

/// Classify an `anyhow::Error` into the most specific `ProverOutcome` variant.
///
/// The classifier inspects the error message as a lower-case string and
/// runs a prioritised series of substring checks.  Order matters —
/// "timeout" wins over "error", parse/syntax wins over generic failures.
///
/// `limit_secs` is used only when the error is classified as `Timeout`, so
/// the outcome preserves the budget that was in effect.
pub fn classify_anyhow_error(err: &anyhow::Error, limit_secs: u64) -> ProverOutcome {
    let msg = format!("{}", err);
    let lower = msg.to_lowercase();

    // 1. Timeout — highest priority, always retryable.
    if lower.contains("timeout") || lower.contains("timed out") {
        return ProverOutcome::Timeout { limit_secs };
    }

    // 2. Unsupported / out-of-logic features.
    if lower.contains("unsupported") || lower.contains("not supported") {
        return ProverOutcome::UnsupportedFeature {
            feature: extract_feature(&msg),
        };
    }

    // 3. Input problems — parse / syntax / undeclared symbol.
    if lower.contains("parse error")
        || lower.contains("syntax error")
        || lower.contains("unexpected token")
        || lower.contains("not declared")
        || lower.contains("undeclared")
    {
        return ProverOutcome::InvalidInput {
            reason: msg.clone(),
            location: extract_location(&msg),
        };
    }

    // 4. System errors — OS / spawn / file / permission.
    if lower.contains("failed to spawn")
        || lower.contains("no such file")
        || lower.contains("permission denied")
        || lower.contains("os error")
        || lower.contains("io error")
    {
        return ProverOutcome::SystemError { detail: msg };
    }

    // 5. Default: prover-side error.
    ProverOutcome::ProverError {
        detail: msg,
        exit_code: None,
    }
}

/// Extract a concise feature name from an "unsupported X" message.
/// Heuristic — falls back to the full message when we can't find the tail.
fn extract_feature(msg: &str) -> String {
    let lower = msg.to_lowercase();
    if let Some(idx) = lower.find("unsupported") {
        let tail = &msg[idx + "unsupported".len()..];
        let tail = tail.trim_start_matches([':', ' ', '\t', '"']);
        let tail = tail.trim_end_matches(['"', ')']);
        if !tail.is_empty() {
            return tail.trim().to_string();
        }
    }
    msg.to_string()
}

/// Extract a line / character offset from a parser error message.
/// Looks for patterns like "at line 5" or "line 12:".
fn extract_location(msg: &str) -> Option<usize> {
    let lower = msg.to_lowercase();
    let needles = ["at line ", "line ", "at offset "];
    for needle in &needles {
        if let Some(idx) = lower.find(needle) {
            let rest = &msg[idx + needle.len()..];
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse::<usize>() {
                return Some(n);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn status_str_is_unique_per_variant() {
        let all = [
            ProverOutcome::Proved { elapsed_ms: 0 }.status_str(),
            ProverOutcome::NoProofFound {
                elapsed_ms: 0,
                reason: None,
            }
            .status_str(),
            ProverOutcome::InvalidInput {
                reason: String::new(),
                location: None,
            }
            .status_str(),
            ProverOutcome::UnsupportedFeature {
                feature: String::new(),
            }
            .status_str(),
            ProverOutcome::Timeout { limit_secs: 0 }.status_str(),
            ProverOutcome::InconsistentPremises { detail: None }.status_str(),
            ProverOutcome::ProverError {
                detail: String::new(),
                exit_code: None,
            }
            .status_str(),
            ProverOutcome::SystemError {
                detail: String::new(),
            }
            .status_str(),
        ];
        let unique: std::collections::HashSet<&&str> = all.iter().collect();
        assert_eq!(all.len(), unique.len());
    }

    #[test]
    fn default_is_system_error() {
        let o = ProverOutcome::default();
        assert_eq!(o.status_str(), "SYSTEM_ERROR");
        assert!(!o.is_proved());
        assert!(!o.is_conclusive());
    }

    #[test]
    fn classification_timeout_beats_error() {
        let e = anyhow::anyhow!("Z3 execution timeout after 30 seconds");
        let o = classify_anyhow_error(&e, 30);
        assert_eq!(o.status_str(), "TIMEOUT");
        assert!(o.is_retryable());
    }

    #[test]
    fn classification_parse_error() {
        let e = anyhow::anyhow!("parse error: unexpected token ')' at line 5");
        let o = classify_anyhow_error(&e, 30);
        assert_eq!(o.status_str(), "INVALID_INPUT");
        if let ProverOutcome::InvalidInput { location, .. } = o {
            assert_eq!(location, Some(5));
        } else {
            panic!("expected InvalidInput");
        }
    }

    #[test]
    fn classification_system_error() {
        let e = anyhow::anyhow!("Failed to spawn Z3 process: no such file or directory");
        let o = classify_anyhow_error(&e, 30);
        assert_eq!(o.status_str(), "SYSTEM_ERROR");
    }

    #[test]
    fn classification_unsupported() {
        let e = anyhow::anyhow!("(error \"unsupported logic: non-linear arithmetic\")");
        let o = classify_anyhow_error(&e, 30);
        assert_eq!(o.status_str(), "UNSUPPORTED_FEATURE");
    }

    #[test]
    fn serde_round_trip_all_variants() {
        let outcomes = vec![
            ProverOutcome::Proved { elapsed_ms: 42 },
            ProverOutcome::NoProofFound {
                elapsed_ms: 100,
                reason: Some("sat".to_string()),
            },
            ProverOutcome::Timeout { limit_secs: 60 },
            ProverOutcome::InvalidInput {
                reason: "bad".to_string(),
                location: Some(7),
            },
            ProverOutcome::InconsistentPremises {
                detail: Some("P ∧ ¬P".to_string()),
            },
            ProverOutcome::UnsupportedFeature {
                feature: "HOL".to_string(),
            },
            ProverOutcome::ProverError {
                detail: "segfault".to_string(),
                exit_code: Some(139),
            },
            ProverOutcome::SystemError {
                detail: "not found".to_string(),
            },
        ];
        for o in &outcomes {
            let s = serde_json::to_string(o).unwrap();
            let d: ProverOutcome = serde_json::from_str(&s).unwrap();
            assert_eq!(o, &d, "round-trip failed for {}", o);
        }
    }
}
