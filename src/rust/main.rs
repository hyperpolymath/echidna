// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! ECHIDNA CLI - Main binary entry point
//!
//! Provides command-line interface, REPL, and HTTP server for theorem proving

use anyhow::Result;
use clap::Parser;
use std::path::PathBuf;

mod cli;
mod output;
mod repl;
mod server;

use cli::*;

use output::OutputFormatter;

/// Run the selected CLI command after configuring tracing, colours and output.
#[tokio::main]
async fn main() -> Result<()> {
    // Parse CLI arguments
    let cli = Cli::parse();

    // Initialize tracing. With `prove --output json`, stdout carries only the
    // result object, so logs go to stderr.
    let json_stdout = matches!(
        cli.command,
        Commands::Prove {
            output: ProveOutput::Json,
            ..
        }
    );
    init_tracing(cli.verbose, json_stdout);

    // Disable colors if requested
    if cli.no_color {
        colored::control::set_override(false);
    }

    // Create output formatter
    let formatter = OutputFormatter::new(cli.format);

    // Execute command
    match cli.command {
        Commands::Prove {
            file,
            prover,
            timeout,
            neural,
            executable,
            library,
            diagnose,
            project_root,
            sandbox,
            output: ProveOutput::Json,
        } => {
            prove_json_command(
                file,
                prover,
                timeout,
                neural,
                executable,
                library,
                diagnose,
                project_root,
                sandbox,
            )
            .await;
        },

        Commands::Prove {
            file,
            prover,
            timeout,
            neural,
            executable,
            library,
            diagnose,
            project_root,
            sandbox,
            output: ProveOutput::Human,
        } => {
            prove_command(
                file,
                prover,
                timeout,
                neural,
                executable,
                library,
                diagnose,
                project_root,
                sandbox,
                &formatter,
            )
            .await?;
        },

        Commands::Verify {
            file,
            prover,
            timeout,
            executable,
            library,
            diagnose,
        } => {
            verify_command(
                file, prover, timeout, executable, library, diagnose, &formatter,
            )
            .await?;
        },

        Commands::Search {
            pattern,
            prover,
            limit,
        } => {
            search_command(pattern, prover, limit, &formatter).await?;
        },

        Commands::Interactive {
            file,
            prover,
            neural,
        } => {
            interactive_command(file, prover, neural).await?;
        },

        Commands::Server { port, host, cors } => {
            server_command(port, host, cors).await?;
        },

        Commands::ListProvers { detailed } => {
            list_provers_command(detailed, &formatter)?;
        },

        Commands::Info { prover } => {
            info_command(prover, &formatter)?;
        },

        Commands::Diagnostics => {
            diagnostics_command().await?;
        },
        Commands::Corpus { op } => {
            corpus_command(op, &formatter)?;
        },

        Commands::Lexicon { op } => {
            lexicon_command(op, &formatter)?;
        },

        Commands::Design { op } => {
            design_command(op, &formatter).await?;
        },

        Commands::Suggest {
            target,
            prover,
            budget,
            top,
            synonyms_dir,
            dry_run,
            max_parallel,
        } => {
            let synonyms_dir = synonyms_dir.unwrap_or_else(|| PathBuf::from("data/synonyms"));
            let config = echidna::suggest::SuggestConfig {
                target,
                prover,
                budget: std::time::Duration::from_secs(budget),
                top,
                synonyms_dir,
                dry_run,
                max_parallel,
            };
            echidna::suggest::run(config).await?;
        },
    }

    Ok(())
}

// We need to add futures crate for the executor
