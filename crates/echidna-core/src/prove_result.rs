// SPDX-License-Identifier: MPL-2.0

//! The `echidna.prove.result/1` contract.
//!
//! `echidna prove <file> --output json` prints exactly one line on stdout:
//! a JCS-canonical (RFC 8785) I-JSON (RFC 7493) object of this shape
//! (shown wrapped; keys appear in JCS order on the wire):
//!
//! ```json
//! {"duration_ms":12,"echidna_version":"2.3.0","goal":"probe.thy",
//!  "message":"PROVED in 12ms","prover":"Isabelle",
//!  "schema":"echidna.prove.result/1","status":"verified",
//!  "trust":{"axioms":[],"confidence":null}}
//! ```
//!
//! This module holds the type both sides use: ECHIDNA serialises it with
//! [`ProveResult::to_jcs`], and consumers (proof-burrower, echidnabot) can
//! parse it strictly with [`ProveResult::parse`].
//!
//! ## Receipt, not warrant
//!
//! `trust.confidence` is a number only when a receipt-backed computation
//! produced it, such as an independently checked proof certificate. A
//! single-prover run that checked no certificate reports `null`, never a
//! guessed score. The distinction follows the factive / non-factive split
//! of `hyperpolymath/epistemic-types` (`FactiveModality`): a receipt is
//! transported proof, a warrant is only evidence. This crate copies that
//! distinction as a pattern; it does not depend on the Agda library.
//!
//! ## Versioning
//!
//! Adding a field is backwards compatible (consumers must ignore unknown
//! fields). Removing, renaming or retyping a field needs a new schema
//! identifier (`echidna.prove.result/2`).

use serde::{Deserialize, Serialize};
use std::fmt;

/// The schema identifier this module emits and accepts.
pub const SCHEMA: &str = "echidna.prove.result/1";

/// Largest integer I-JSON (RFC 7493 §2.2) guarantees to round-trip: 2^53 − 1.
pub const MAX_SAFE_INTEGER: u64 = (1u64 << 53) - 1;

/// The verdict of one prove run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ProveStatus {
    /// The backend established the goal.
    Verified,
    /// The backend ran to completion and did not establish the goal.
    Failed,
    /// ECHIDNA or the backend could not run, or the input was rejected.
    Error,
    /// The backend exceeded its time budget.
    Timeout,
    /// The run finished without a usable answer (for example, the premises
    /// were inconsistent, so a "proof" would be vacuous).
    Unknown,
}

impl ProveStatus {
    /// Every status, in contract order.
    pub const ALL: [ProveStatus; 5] = [
        ProveStatus::Verified,
        ProveStatus::Failed,
        ProveStatus::Error,
        ProveStatus::Timeout,
        ProveStatus::Unknown,
    ];

    /// The wire string of this status.
    pub fn as_str(self) -> &'static str {
        match self {
            ProveStatus::Verified => "verified",
            ProveStatus::Failed => "failed",
            ProveStatus::Error => "error",
            ProveStatus::Timeout => "timeout",
            ProveStatus::Unknown => "unknown",
        }
    }
}

/// What a verdict rests on.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct ProveTrust {
    /// Receipt-backed confidence in `[0, 1]`, or `None` (`null`) when no
    /// receipt-backed figure exists. See the module docs.
    pub confidence: Option<f64>,
    /// Axioms and escape hatches (`sorry`, `Admitted`, ...) found in the
    /// input, sorted and de-duplicated.
    pub axioms: Vec<String>,
}

/// One `echidna.prove.result/1` object.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProveResult {
    /// Always [`SCHEMA`].
    pub schema: String,
    /// The verdict.
    pub status: ProveStatus,
    /// The backend, as ECHIDNA names it (`ProverKind` variant name), or the
    /// empty string when no backend could be selected.
    pub prover: String,
    /// The goal ECHIDNA was asked to prove: the proof file path as given.
    pub goal: String,
    /// Wall-clock time of the backend check, in milliseconds.
    pub duration_ms: u64,
    /// Human-readable diagnostic; may be empty.
    pub message: String,
    /// What the verdict rests on.
    pub trust: ProveTrust,
    /// The ECHIDNA version that emitted this object.
    pub echidna_version: String,
}

/// Why a value cannot be emitted, or a payload is not a valid result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveResultError {
    /// `duration_ms` exceeds [`MAX_SAFE_INTEGER`].
    UnsafeInteger(u64),
    /// `trust.confidence` is NaN, infinite, or outside `[0, 1]`.
    BadConfidence,
    /// The payload is empty.
    Empty,
    /// The payload holds more than one line.
    ExtraOutput,
    /// The payload is not valid JSON.
    NotJson(String),
    /// The payload is JSON but not byte-identical to its RFC 8785 form.
    NotCanonical,
    /// The object names a different schema.
    WrongSchema(String),
    /// The object does not have the contract's shape.
    Shape(String),
}

impl fmt::Display for ProveResultError {
    /// Render the error as a one-line diagnostic.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProveResultError::UnsafeInteger(n) => {
                write!(f, "duration_ms {n} exceeds the I-JSON safe range")
            },
            ProveResultError::BadConfidence => {
                write!(
                    f,
                    "trust.confidence must be a finite number in [0, 1] or null"
                )
            },
            ProveResultError::Empty => write!(f, "empty payload"),
            ProveResultError::ExtraOutput => write!(f, "more than one line"),
            ProveResultError::NotJson(e) => write!(f, "not JSON: {e}"),
            ProveResultError::NotCanonical => write!(f, "not JCS-canonical (RFC 8785)"),
            ProveResultError::WrongSchema(s) => write!(f, "unsupported schema {s:?}"),
            ProveResultError::Shape(e) => write!(f, "wrong shape: {e}"),
        }
    }
}

impl std::error::Error for ProveResultError {}

impl ProveResult {
    /// Build a result with the current [`SCHEMA`].
    ///
    /// `duration_ms` saturates at [`MAX_SAFE_INTEGER`] and `axioms` are
    /// sorted and de-duplicated, so the output is deterministic for the
    /// same inputs.
    pub fn new(
        status: ProveStatus,
        prover: impl Into<String>,
        goal: impl Into<String>,
        duration_ms: u64,
        message: impl Into<String>,
        mut trust: ProveTrust,
        echidna_version: impl Into<String>,
    ) -> Self {
        trust.axioms.sort();
        trust.axioms.dedup();
        ProveResult {
            schema: SCHEMA.to_string(),
            status,
            prover: prover.into(),
            goal: goal.into(),
            duration_ms: duration_ms.min(MAX_SAFE_INTEGER),
            message: message.into(),
            trust,
            echidna_version: echidna_version.into(),
        }
    }

    /// Serialise to the one-line JCS-canonical I-JSON form (no newline).
    ///
    /// Fails rather than emit a value outside I-JSON: an integer beyond
    /// 2^53 − 1, or a non-finite or out-of-range confidence.
    pub fn to_jcs(&self) -> Result<String, ProveResultError> {
        if self.duration_ms > MAX_SAFE_INTEGER {
            return Err(ProveResultError::UnsafeInteger(self.duration_ms));
        }
        if let Some(c) = self.trust.confidence {
            if !c.is_finite() || !(0.0..=1.0).contains(&c) {
                return Err(ProveResultError::BadConfidence);
            }
        }
        // JCS output has no raw newlines (control characters in strings
        // are escaped), so this is always exactly one line.
        serde_json_canonicalizer::to_string(self)
            .map_err(|e| ProveResultError::Shape(e.to_string()))
    }

    /// Parse and validate a payload as exactly one result object.
    ///
    /// One trailing newline is allowed. The line must be JSON, must equal
    /// its own RFC 8785 canonical form byte for byte (which rules out
    /// duplicate keys and unsafe integers), must name [`SCHEMA`], and must
    /// carry every field with the right type. Unknown extra fields are
    /// tolerated.
    pub fn parse(payload: &str) -> Result<Self, ProveResultError> {
        let line = payload.strip_suffix('\n').unwrap_or(payload);
        if line.is_empty() {
            return Err(ProveResultError::Empty);
        }
        if line.contains('\n') {
            return Err(ProveResultError::ExtraOutput);
        }
        let value: serde_json::Value =
            serde_json::from_str(line).map_err(|e| ProveResultError::NotJson(e.to_string()))?;
        let canonical = serde_json_canonicalizer::to_string(&value)
            .map_err(|e| ProveResultError::NotJson(e.to_string()))?;
        if canonical != line {
            return Err(ProveResultError::NotCanonical);
        }
        match value.get("schema").and_then(|s| s.as_str()) {
            Some(SCHEMA) => {},
            Some(other) => return Err(ProveResultError::WrongSchema(other.to_string())),
            None => {
                return Err(ProveResultError::Shape(
                    "missing string field `schema`".into(),
                ))
            },
        }
        serde_json::from_value(value).map_err(|e| ProveResultError::Shape(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fixed sample used by the golden tests.
    fn sample(status: ProveStatus) -> ProveResult {
        ProveResult::new(
            status,
            "Isabelle",
            "probe.thy",
            12,
            "",
            ProveTrust {
                confidence: None,
                axioms: vec!["sorry".into()],
            },
            "2.3.0",
        )
    }

    /// Every status serialises to the exact golden JCS bytes and parses back.
    #[test]
    fn golden_jcs_bytes_for_every_status() {
        for status in ProveStatus::ALL {
            let expected = format!(
                r#"{{"duration_ms":12,"echidna_version":"2.3.0","goal":"probe.thy","message":"","prover":"Isabelle","schema":"echidna.prove.result/1","status":"{}","trust":{{"axioms":["sorry"],"confidence":null}}}}"#,
                status.as_str()
            );
            let got = sample(status).to_jcs().unwrap();
            assert_eq!(got, expected);
            assert_eq!(ProveResult::parse(&got).unwrap(), sample(status));
        }
    }

    /// Escapes and non-ASCII text still yield one canonical line.
    #[test]
    fn output_is_its_own_canonical_form() {
        let mut r = sample(ProveStatus::Failed);
        r.message = "line one\nline \"two\" \u{e9}".into();
        r.trust.confidence = Some(0.5);
        let out = r.to_jcs().unwrap();
        assert!(!out.contains('\n'));
        let reparsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(serde_json_canonicalizer::to_string(&reparsed).unwrap(), out);
        assert_eq!(ProveResult::parse(&out).unwrap(), r);
    }

    /// Planted mutants (reordered keys, whitespace, duplicates, extra lines, wrong schema) are refused.
    #[test]
    fn planted_non_canonical_payloads_are_rejected() {
        let good = sample(ProveStatus::Verified).to_jcs().unwrap();
        // Reordered keys.
        let reordered = good.replacen(
            r#"{"duration_ms":12,"echidna_version":"2.3.0""#,
            r#"{"echidna_version":"2.3.0","duration_ms":12"#,
            1,
        );
        assert_ne!(reordered, good);
        assert_eq!(
            ProveResult::parse(&reordered),
            Err(ProveResultError::NotCanonical)
        );
        // Whitespace.
        let spaced = good.replacen(':', ": ", 1);
        assert_eq!(
            ProveResult::parse(&spaced),
            Err(ProveResultError::NotCanonical)
        );
        // Duplicate key.
        assert_eq!(
            ProveResult::parse(r#"{"a":1,"a":2}"#),
            Err(ProveResultError::NotCanonical)
        );
        // Extra line, empty, wrong schema.
        assert_eq!(
            ProveResult::parse(&format!("notice\n{good}")),
            Err(ProveResultError::ExtraOutput)
        );
        assert_eq!(ProveResult::parse("\n"), Err(ProveResultError::Empty));
        let wrong = good.replace("echidna.prove.result/1", "echidna.prove.result/9");
        assert!(matches!(
            ProveResult::parse(&wrong),
            Err(ProveResultError::WrongSchema(_))
        ));
    }

    /// Values outside I-JSON or the confidence range are not emitted.
    #[test]
    fn out_of_range_values_are_refused() {
        let mut r = sample(ProveStatus::Verified);
        r.duration_ms = MAX_SAFE_INTEGER + 1;
        assert_eq!(
            r.to_jcs(),
            Err(ProveResultError::UnsafeInteger(MAX_SAFE_INTEGER + 1))
        );
        let mut r = sample(ProveStatus::Verified);
        r.trust.confidence = Some(f64::NAN);
        assert_eq!(r.to_jcs(), Err(ProveResultError::BadConfidence));
        r.trust.confidence = Some(1.5);
        assert_eq!(r.to_jcs(), Err(ProveResultError::BadConfidence));
    }

    /// `new` saturates the duration and sorts and de-duplicates axioms.
    #[test]
    fn constructor_saturates_and_normalises() {
        let r = ProveResult::new(
            ProveStatus::Verified,
            "Lean",
            "a.lean",
            u64::MAX,
            "",
            ProveTrust {
                confidence: None,
                axioms: vec!["sorry".into(), "Classical.choice".into(), "sorry".into()],
            },
            "x",
        );
        assert_eq!(r.duration_ms, MAX_SAFE_INTEGER);
        assert_eq!(r.trust.axioms, vec!["Classical.choice", "sorry"]);
        assert!(r.to_jcs().is_ok());
    }
}
