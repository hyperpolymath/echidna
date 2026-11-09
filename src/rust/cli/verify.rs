// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: verify. Moved verbatim from main.rs (hotspot split).

use super::*;
use crate::output::OutputFormatter;
use anyhow::{Context, Result};
use echidna::ProverKind;
use std::path::PathBuf;
use tracing::info;

/// Verify command implementation
pub(crate) async fn verify_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    diagnose: bool,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Verifying proof: {}", file.display());

    let kind = detect_prover(prover_kind, &file)?;
    let config = create_config(kind, timeout, true, executable, library, None, "none")?;
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
        formatter.success(&format!("✓ Proof is valid: {}", file.display()))?;
        formatter.info(&format!("Goals: {}", state.goals.len()))?;
        formatter.info(&format!("Tactics: {}", state.proof_script.len()))?;
        formatter.info(&format!(
            "Theorems in context: {}",
            state.context.theorems.len()
        ))?;
    } else {
        formatter.error(&format!("✗ Proof is invalid: {}", file.display()))?;
        if diagnose {
            emit_diagnostic(kind, &*prover, &state, formatter).await;
        }
        std::process::exit(1);
    }

    Ok(())
}
