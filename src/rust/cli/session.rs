// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: session. Moved verbatim from main.rs (hotspot split).

use crate::repl::DiagnosticsREPL;
use crate::{repl, server};
use anyhow::Result;
use echidna::dispatch::ProverDispatcher;
use echidna::ProverKind;
use std::path::PathBuf;
use std::sync::Arc;
use tracing::info;

/// Interactive REPL command
pub(crate) async fn interactive_command(
    file: Option<PathBuf>,
    prover_kind: Option<ProverKind>,
    neural: bool,
) -> Result<()> {
    info!("Starting interactive REPL mode");

    repl::start_repl(file, prover_kind, neural).await
}

/// HTTP Server command
pub(crate) async fn server_command(port: u16, host: String, cors: bool) -> Result<()> {
    info!("Starting HTTP server on {}:{}", host, port);

    server::start_server(port, host, cors).await
}

/// Diagnostics command - interactive health monitoring REPL
pub(crate) async fn diagnostics_command() -> Result<()> {
    info!("Starting diagnostics REPL for health monitoring");
    let dispatcher = Arc::new(ProverDispatcher::new());
    let health = dispatcher.health_status()?;
    let mut repl = DiagnosticsREPL::new();
    repl.run(&health).await;
    Ok(())
}
