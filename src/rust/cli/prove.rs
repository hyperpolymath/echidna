// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: prove. Moved verbatim from main.rs (hotspot split).

use super::*;
use crate::output::OutputFormatter;
use anyhow::{Context, Result};
use echidna::{
    diagnostics::proof_failure::diagnose_from_outcome, provers::ProverBackend, ProverKind,
};
use std::path::PathBuf;
use tracing::info;

/// Prove command implementation
#[allow(clippy::too_many_arguments)]
pub(crate) async fn prove_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    diagnose: bool,
    project_root: Option<PathBuf>,
    sandbox: String,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Starting proof for: {}", file.display());

    let kind = detect_prover(prover_kind, &file)?;
    let config = create_config(
        kind,
        timeout,
        neural,
        executable,
        library,
        project_root,
        &sandbox,
    )?;
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    let pb = create_progress_bar("Parsing proof file...");
    let state = prover
        .parse_file(file.clone())
        .await
        .context("Failed to parse proof file")?;

    pb.set_message("Verifying proof...");
    let result = prover
        .verify_proof(&state)
        .await
        .context("Failed to verify proof")?;
    pb.finish_and_clear();

    if result {
        formatter.success(&format!(
            "✓ Proof verified successfully for {}",
            file.display()
        ))?;
        formatter.output_proof_state(&state)?;
    } else {
        formatter.error(&format!(
            "✗ Proof verification failed for {}",
            file.display()
        ))?;
        formatter.output_proof_state(&state)?;
        if diagnose {
            emit_diagnostic(kind, &*prover, &state, formatter).await;
        }
        std::process::exit(1);
    }

    Ok(())
}

/// `echidna prove --output json`: print one `echidna.prove.result/1` object.
///
/// Every failure, including a missing backend or unreadable file, becomes an
/// `error` result rather than a non-JSON message. Exits 0 when the status is
/// `verified` and 1 otherwise. With `--diagnose`, the diagnostic report for a
/// non-verified run goes to stderr.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn prove_json_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    diagnose: bool,
    project_root: Option<PathBuf>,
    sandbox: String,
) {
    use echidna::prove_contract::{self, ProveStatus};

    let goal = file.display().to_string();
    let start = std::time::Instant::now();
    let since =
        |start: std::time::Instant| u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX);

    let kind = match detect_prover(prover_kind, &file) {
        Ok(k) => k,
        Err(e) => {
            let r = prove_contract::result_from_error(prover_kind, &goal, &e, since(start));
            emit_prove_result(&r);
        },
    };
    let backend = match create_config(
        kind,
        timeout,
        neural,
        executable,
        library,
        project_root,
        &sandbox,
    )
    .and_then(|config| {
        echidna::provers::ProverFactory::create(kind, config)
            .context("Failed to create prover backend")
    }) {
        Ok(b) => b,
        Err(e) => {
            let r = prove_contract::result_from_error(Some(kind), &goal, &e, since(start));
            emit_prove_result(&r);
        },
    };

    let (result, outcome) = prove_contract::run_detailed(kind, &*backend, &file).await;
    if let (true, Some(outcome)) = (diagnose && result.status != ProveStatus::Verified, outcome) {
        eprintln!("--- Proof Failure Diagnostic ---");
        eprintln!("{}", diagnose_from_outcome(kind, &outcome).display());
    }
    emit_prove_result(&result);
}

/// Print `result` as its one JCS line on stdout and exit (0 iff verified).
///
/// If the value cannot be serialised (it never should), a minimal `error`
/// object is printed instead, so stdout always carries one contract object.
pub(crate) fn emit_prove_result(result: &echidna::prove_contract::ProveResult) -> ! {
    use echidna::prove_contract::{self, ProveStatus};
    let line = result.to_jcs().unwrap_or_else(|e| {
        let e = anyhow::anyhow!("could not serialise prove result: {e}");
        prove_contract::result_from_error(None, &result.goal, &e, 0)
            .to_jcs()
            .expect("an error result with no numbers out of range serialises")
    });
    println!("{line}");
    std::process::exit(if result.status == ProveStatus::Verified {
        0
    } else {
        1
    });
}

/// Run `check()` on the prover and display a structured diagnostic report.
///
/// Called after a failed `verify_proof()` when `--diagnose` is active.
/// Uses the richer `ProverOutcome` returned by `check()` to produce an
/// actionable report via `diagnose_from_outcome`.
pub(crate) async fn emit_diagnostic(
    kind: ProverKind,
    prover: &dyn ProverBackend,
    state: &echidna::core::ProofState,
    formatter: &OutputFormatter,
) {
    let outcome = match prover.check(state).await {
        Ok(o) => o,
        Err(e) => {
            let _ = formatter.error(&format!("[diagnose] could not run check(): {}", e));
            return;
        },
    };
    let report = diagnose_from_outcome(kind, &outcome);
    let _ = formatter.info("\n--- Proof Failure Diagnostic ---");
    let _ = formatter.info(&report.display());
}
