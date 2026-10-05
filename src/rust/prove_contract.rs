// SPDX-License-Identifier: MPL-2.0

//! Producer side of the `echidna.prove.result/1` contract.
//!
//! `echidna prove <file> --output json` runs one backend check and prints
//! one [`ProveResult`] as JCS-canonical I-JSON on stdout. The type and its
//! serialiser live in `echidna-core` ([`echidna_core::prove_result`]) so
//! consumers share them; this module turns a backend run into that value.
//!
//! See `docs/PROVE-RESULT-CONTRACT.adoc` for the contract and the status
//! mapping.

use std::path::Path;
use std::time::Instant;

pub use echidna_core::prove_result::{ProveResult, ProveStatus, ProveTrust, SCHEMA};

use crate::provers::{ProverBackend, ProverKind, ProverOutcome};
use crate::verification::axiom_tracker::AxiomTracker;

/// The version string this build writes into `echidna_version`.
pub const ECHIDNA_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Names of the axioms and escape hatches the tracker finds in `content`.
///
/// Uses ECHIDNA's source-level [`AxiomTracker`] for `kind`; returns the
/// constructs only (sorted and de-duplicated by [`ProveResult::new`]).
pub fn axioms_in(kind: ProverKind, content: &str) -> Vec<String> {
    AxiomTracker::new()
        .scan(kind, content)
        .into_iter()
        .map(|u| u.construct)
        .collect()
}

/// Build the result for a backend run that produced `outcome`.
///
/// `confidence` stays `null`: a single-prover check verifies no proof
/// certificate, so there is no receipt-backed figure to report.
pub fn result_from_outcome(
    kind: ProverKind,
    goal: &str,
    outcome: &ProverOutcome,
    duration_ms: u64,
    axioms: Vec<String>,
) -> ProveResult {
    ProveResult::new(
        outcome.prove_status(),
        kind.to_string(),
        goal,
        duration_ms,
        outcome.to_string(),
        ProveTrust {
            confidence: None,
            axioms,
        },
        ECHIDNA_VERSION,
    )
}

/// Build the `error` result for a run that failed before the backend check
/// (no backend for the file, unreadable or unparsable input, ...).
///
/// `kind` is the backend if one was selected; otherwise `prover` is empty.
pub fn result_from_error(
    kind: Option<ProverKind>,
    goal: &str,
    err: &anyhow::Error,
    duration_ms: u64,
) -> ProveResult {
    ProveResult::new(
        ProveStatus::Error,
        kind.map(|k| k.to_string()).unwrap_or_default(),
        goal,
        duration_ms,
        format!("{err:#}"),
        ProveTrust::default(),
        ECHIDNA_VERSION,
    )
}

/// Parse `file` with `backend`, run its rich check, and build the result.
///
/// Never fails: every failure becomes an `error` result. `duration_ms`
/// covers parsing plus the backend check.
pub async fn run(kind: ProverKind, backend: &dyn ProverBackend, file: &Path) -> ProveResult {
    run_detailed(kind, backend, file).await.0
}

/// Like [`run`], and also return the backend's [`ProverOutcome`] when the
/// check itself ran (for `--diagnose`).
pub async fn run_detailed(
    kind: ProverKind,
    backend: &dyn ProverBackend,
    file: &Path,
) -> (ProveResult, Option<ProverOutcome>) {
    let goal = file.display().to_string();
    let start = Instant::now();
    let elapsed = || u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX);

    let content = match crate::provers::bounded_read_proof_file(file).await {
        Ok(c) => c,
        Err(e) => return (result_from_error(Some(kind), &goal, &e, elapsed()), None),
    };
    let state = match backend.parse_file(file.to_path_buf()).await {
        Ok(s) => s,
        Err(e) => {
            let e = e.context("Failed to parse proof file");
            return (result_from_error(Some(kind), &goal, &e, elapsed()), None);
        },
    };
    let outcome = match backend.check(&state).await {
        Ok(o) => o,
        Err(e) => {
            let e = e.context("Failed to verify proof");
            return (result_from_error(Some(kind), &goal, &e, elapsed()), None);
        },
    };
    let result = result_from_outcome(kind, &goal, &outcome, elapsed(), axioms_in(kind, &content));
    (result, Some(outcome))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Expected JCS line for a given status and message, with fixed fields.
    fn golden(status: &str, prover: &str, message: &str, axioms: &str) -> String {
        format!(
            r#"{{"duration_ms":7,"echidna_version":"{ECHIDNA_VERSION}","goal":"g.lean","message":"{message}","prover":"{prover}","schema":"echidna.prove.result/1","status":"{status}","trust":{{"axioms":[{axioms}],"confidence":null}}}}"#
        )
    }

    /// Golden JCS bytes for every contract status, via the outcome path.
    #[test]
    fn golden_output_for_each_outcome_status() {
        let cases = [
            (
                ProverOutcome::Proved { elapsed_ms: 7 },
                "verified",
                "PROVED in 7ms",
            ),
            (
                ProverOutcome::NoProofFound {
                    elapsed_ms: 7,
                    reason: None,
                },
                "failed",
                "NO_PROOF_FOUND in 7ms",
            ),
            (
                ProverOutcome::Timeout { limit_secs: 3 },
                "timeout",
                "TIMEOUT after 3s",
            ),
            (
                ProverOutcome::InconsistentPremises { detail: None },
                "unknown",
                "INCONSISTENT_PREMISES",
            ),
            (
                ProverOutcome::SystemError {
                    detail: "lean not found".into(),
                },
                "error",
                "SYSTEM_ERROR: lean not found",
            ),
        ];
        for (outcome, status, message) in cases {
            let r = result_from_outcome(
                ProverKind::Lean,
                "g.lean",
                &outcome,
                7,
                vec!["sorry".into(), "sorry".into()],
            );
            assert_eq!(
                r.to_jcs().unwrap(),
                golden(status, "Lean", message, r#""sorry""#)
            );
        }
    }

    /// A pre-check failure is an `error` with the full error chain.
    #[test]
    fn golden_output_for_pre_check_error() {
        let e = anyhow::anyhow!("no such file").context("Failed to parse proof file");
        let r = result_from_error(None, "g.lean", &e, 7);
        assert_eq!(
            r.to_jcs().unwrap(),
            golden("error", "", "Failed to parse proof file: no such file", "")
        );
    }

    /// The tracker's findings reach `trust.axioms`.
    #[test]
    fn axioms_are_reported_from_the_input() {
        let found = axioms_in(ProverKind::Lean, "theorem t : 1 = 1 := by\n  sorry\n");
        assert!(found.iter().any(|a| a == "sorry"), "{found:?}");
        assert!(axioms_in(ProverKind::Lean, "theorem t : 1 = 1 := rfl\n").is_empty());
    }
}
