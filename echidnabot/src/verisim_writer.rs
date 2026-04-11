// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! VeriSimDB proof-attempt writer for echidnabot.
//!
//! Records every proof attempt (success or failure) to VeriSimDB's
//! `proof_attempts` table via `POST /api/v1/proof_attempts`.
//!
//! This closes the learning loop:
//!
//! ```text
//! echidnabot verify_proof
//!     → VeriSimWriter::record
//!     → POST /api/v1/proof_attempts
//!     → ClickHouse proof_attempts table
//!     → mv_prover_success_by_class (auto-maintained)
//!     → Hypatia ProofStrategySelection.recommend/2
//!     → echidnabot prover_hint in next dispatch
//! ```
//!
//! The writer is fully non-fatal: if VeriSimDB is unreachable, it logs a
//! warning at `WARN` level and returns so the calling job continues. The
//! learning loop degrades gracefully to the last known recommendations.
//!
//! # Configuration
//!
//! Set `HYPATIA_VERISIM_URL` to the verisim-api base URL
//! (e.g. `http://localhost:8080`). If the variable is absent or empty,
//! the writer is disabled and every call to `record` is a no-op.
//!
//! # Prover-agnosticism
//!
//! `prover_to_str` maps every `ProverKind` variant to the lowercase
//! string the ClickHouse `Enum8` expects. Adding a new prover to
//! `ProverKind` requires adding one arm here — no other change needed.

use chrono::{DateTime, Utc};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{debug, warn};
use uuid::Uuid;

use crate::dispatcher::{ProofResult, ProofStatus, ProverKind};

// ─── Row type ─────────────────────────────────────────────────────────────────

/// A single row written to VeriSimDB's `proof_attempts` table.
///
/// Field names are snake_case to match the JSON body expected by
/// `POST /api/v1/proof_attempts` on verisim-api. The `prover_used` and
/// `outcome` strings are lowercase Enum8 values in ClickHouse.
///
/// Schema note: `obligation_id` is a stable hash of `(repo, file)` that
/// groups retries of the same obligation. `attempt_id` is unique per call.
#[derive(Debug, Serialize, Deserialize)]
struct ProofAttemptRow {
    /// UUID v4 — unique to this invocation.
    attempt_id: String,
    /// Stable 16-hex-char hash of `(repo, file)` — groups retries.
    obligation_id: String,
    /// Repository slug, e.g. `"hyperpolymath/echidna"`.
    repo: String,
    /// Relative file path within the repo.
    file: String,
    /// Human-readable description of what is being proved.
    claim: String,
    /// Mathematical obligation class for strategy lookup.
    /// Examples: `"linearity"`, `"termination"`, `"equiv"`, `"safety"`.
    obligation_class: String,
    /// Lowercase prover name matching ClickHouse Enum8:
    /// `"coq"` | `"lean"` | `"agda"` | `"isabelle"` | `"z3"` | `"cvc5"`
    /// | `"metamath"` | `"hol_light"` | `"mizar"` | `"pvs"` | `"acl2"`
    /// | `"hol4"` | `"other"`.
    prover_used: String,
    /// Outcome: `"success"` | `"failure"` | `"timeout"` | `"unknown"`.
    outcome: String,
    /// Wall-clock duration in milliseconds.
    duration_ms: u64,
    /// Confidence in \[0.0, 1.0\]. Derived from outcome for echidnabot jobs.
    confidence: f32,
    /// Set for retries; `None` for first attempts.
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_attempt_id: Option<String>,
    /// Strategy that dispatched this attempt. Fixed to `"echidnabot"` here.
    strategy_tag: String,
    /// ISO-8601 UTC — when the prover was invoked.
    started_at: String,
    /// ISO-8601 UTC — when the result was received.
    completed_at: String,
    /// Truncated prover stdout/stderr (≤ 8 KiB recommended).
    prover_output: String,
    /// Non-`None` when `outcome != "success"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    error_message: Option<String>,
}

// ─── Writer ───────────────────────────────────────────────────────────────────

/// Asynchronously records proof attempts to VeriSimDB.
///
/// Construct once per process with [`VeriSimWriter::from_env`], then call
/// [`VeriSimWriter::record`] after every [`EchidnaClient::verify_proof`].
pub struct VeriSimWriter {
    base_url: String,
    http: Client,
    enabled: bool,
}

impl VeriSimWriter {
    /// Build from the `HYPATIA_VERISIM_URL` environment variable.
    ///
    /// If the variable is absent or empty the writer is disabled:
    /// every [`record`] call returns immediately without network I/O.
    pub fn from_env() -> Self {
        match std::env::var("HYPATIA_VERISIM_URL") {
            Ok(url) if !url.trim().is_empty() => {
                let http = Client::builder()
                    .timeout(std::time::Duration::from_secs(10))
                    .build()
                    .unwrap_or_else(|_| Client::new());
                Self {
                    base_url: url.trim_end_matches('/').to_string(),
                    http,
                    enabled: true,
                }
            }
            _ => {
                tracing::info!(
                    "HYPATIA_VERISIM_URL not set — VeriSimDB proof-attempt recording disabled"
                );
                Self {
                    base_url: String::new(),
                    http: Client::new(),
                    enabled: false,
                }
            }
        }
    }

    /// Record one proof attempt to VeriSimDB.
    ///
    /// Non-fatal: any network or HTTP error is logged at `WARN` and
    /// the function returns so the caller's job loop continues.
    ///
    /// # Arguments
    ///
    /// * `result`     — the outcome from [`EchidnaClient::verify_proof`]
    /// * `prover`     — which prover backend was used
    /// * `repo`       — repository slug, e.g. `"hyperpolymath/echidna"`
    /// * `file_path`  — proof file path (relative or absolute)
    /// * `started_at` — timestamp recorded just before `verify_proof` was called
    pub async fn record(
        &self,
        result: &ProofResult,
        prover: ProverKind,
        repo: &str,
        file_path: &str,
        started_at: DateTime<Utc>,
    ) {
        if !self.enabled {
            return;
        }

        let completed_at = Utc::now();
        let obligation_class = classify_obligation_from_path(file_path, prover);
        let outcome = outcome_str(&result.status);
        let confidence = confidence_from_status(&result.status);
        let prover_str = prover_to_str(prover);

        let row = ProofAttemptRow {
            attempt_id: Uuid::new_v4().to_string(),
            obligation_id: stable_obligation_id(repo, file_path),
            repo: repo.to_string(),
            file: file_path.to_string(),
            claim: format!("Verify proof in {file_path}"),
            obligation_class,
            prover_used: prover_str.to_string(),
            outcome,
            duration_ms: result.duration_ms,
            confidence,
            parent_attempt_id: None,
            strategy_tag: "echidnabot".to_string(),
            started_at: started_at.to_rfc3339(),
            completed_at: completed_at.to_rfc3339(),
            prover_output: truncate_utf8(&result.prover_output, 8 * 1024),
            error_message: if result.status == ProofStatus::Verified {
                None
            } else {
                Some(result.message.clone())
            },
        };

        let url = format!("{}/api/v1/proof_attempts", self.base_url);

        match self.http.post(&url).json(&row).send().await {
            Ok(resp) if resp.status().is_success() => {
                debug!(
                    attempt_id = %row.attempt_id,
                    prover = prover_str,
                    outcome = %row.outcome,
                    file = file_path,
                    "proof_attempt recorded in VeriSimDB"
                );
            }
            Ok(resp) => {
                let status = resp.status();
                let body = resp.text().await.unwrap_or_default();
                warn!(
                    %status,
                    body = %body,
                    prover = prover_str,
                    file = file_path,
                    "VeriSimDB proof_attempts endpoint returned error — attempt not recorded"
                );
            }
            Err(e) => {
                warn!(
                    error = %e,
                    prover = prover_str,
                    file = file_path,
                    "VeriSimDB unreachable — proof_attempt not recorded (learning loop degraded)"
                );
            }
        }
    }
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

/// Map `ProofStatus` to the lowercase ClickHouse Enum8 outcome string.
fn outcome_str(status: &ProofStatus) -> String {
    match status {
        ProofStatus::Verified => "success",
        ProofStatus::Timeout => "timeout",
        ProofStatus::Failed | ProofStatus::Error => "failure",
        ProofStatus::Unknown => "unknown",
    }
    .to_string()
}

/// Derive an obligation class from the file path and prover.
///
/// Keyword-matching against the path provides coarse-grained class labels
/// that feed `mv_prover_success_by_class`. Unknown paths fall back to a
/// prover-namespaced class (e.g. `"metamath_proof"`) so the MV always has
/// a non-null class to aggregate on.
fn classify_obligation_from_path(file_path: &str, prover: ProverKind) -> String {
    let lower = file_path.to_lowercase();
    for (keyword, class) in &[
        ("terminat", "termination"),
        ("linear", "linearity"),
        ("equiv", "equiv"),
        ("correct", "equiv"),
        ("safety", "safety"),
        ("secure", "safety"),
        ("memory", "safety"),
        ("sort", "termination"),
        ("bound", "termination"),
    ] {
        if lower.contains(keyword) {
            return class.to_string();
        }
    }
    // Fallback: prover-namespaced so the MV still groups by (class, prover)
    format!("{}_proof", prover_to_str(prover))
}

/// Derive a rough confidence score from the proof outcome.
///
/// These are priors; the `mv_prover_success_by_class` MV computes true
/// empirical rates from the growing table — the stored `confidence` here
/// is per-attempt metadata, not a prediction.
fn confidence_from_status(status: &ProofStatus) -> f32 {
    match status {
        ProofStatus::Verified => 0.95,
        ProofStatus::Failed => 0.10,
        ProofStatus::Timeout => 0.05,
        ProofStatus::Error => 0.10,
        ProofStatus::Unknown => 0.50,
    }
}

/// Stable 16-char hex obligation ID derived from `(repo, file)`.
///
/// Uses a non-cryptographic hash — good enough for grouping retries.
/// The same `(repo, file)` always produces the same ID across runs.
fn stable_obligation_id(repo: &str, file: &str) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    repo.hash(&mut h);
    b'\0'.hash(&mut h);
    file.hash(&mut h);
    format!("{:016x}", h.finish())
}

/// Truncate `s` to at most `max_bytes` bytes, preserving UTF-8 boundaries.
fn truncate_utf8(s: &str, max_bytes: usize) -> String {
    if s.len() <= max_bytes {
        return s.to_string();
    }
    let boundary = s
        .char_indices()
        .map(|(i, _)| i)
        .take_while(|&i| i <= max_bytes)
        .last()
        .unwrap_or(0);
    format!("{}…", &s[..boundary])
}

/// Map every `ProverKind` variant to the lowercase ClickHouse Enum8 string.
///
/// Adding a new prover requires adding one arm here. The `_ => "other"` arm
/// is intentionally absent so the compiler flags missing variants.
pub fn prover_to_str(kind: ProverKind) -> &'static str {
    match kind {
        ProverKind::Agda => "agda",
        ProverKind::Coq => "coq",
        ProverKind::Lean => "lean",
        ProverKind::Isabelle => "isabelle",
        ProverKind::Z3 => "z3",
        ProverKind::Cvc5 => "cvc5",
        ProverKind::Metamath => "metamath",
        ProverKind::HolLight => "hol_light",
        ProverKind::Mizar => "mizar",
        ProverKind::Pvs => "pvs",
        ProverKind::Acl2 => "acl2",
        ProverKind::Hol4 => "hol4",
    }
}
