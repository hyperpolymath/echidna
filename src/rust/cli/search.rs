// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: search. Moved verbatim from main.rs (hotspot split).

use crate::output::OutputFormatter;
use anyhow::Result;
use echidna::{ProverConfig, ProverKind};
use tracing::{info, warn};

/// Search command implementation
pub(crate) async fn search_command(
    pattern: String,
    prover_kind: Option<ProverKind>,
    limit: usize,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Searching for: {}", pattern);

    let provers: Vec<ProverKind> = if let Some(kind) = prover_kind {
        vec![kind]
    } else {
        // Search all provers
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HOLLight,
            ProverKind::Mizar,
            ProverKind::PVS,
            ProverKind::ACL2,
            ProverKind::HOL4,
            ProverKind::Idris2,
        ]
    };

    formatter.info(&format!(
        "Searching {} prover(s) for pattern: {}",
        provers.len(),
        pattern
    ))?;

    let mut total_results = 0;

    for kind in provers {
        let config = ProverConfig::default();

        if let Ok(prover) = echidna::provers::ProverFactory::create(kind, config) {
            formatter.section(&format!("\n{:?} Results:", kind))?;

            match prover.search_theorems(&pattern).await {
                Ok(results) => {
                    total_results += results.len();

                    for (i, result) in results.iter().take(limit).enumerate() {
                        formatter.result(&format!("  {}. {}", i + 1, result))?;
                    }

                    if results.len() > limit {
                        formatter
                            .info(&format!("  ... and {} more results", results.len() - limit))?;
                    }
                },
                Err(e) => {
                    warn!("Failed to search {}: {}", kind, e);
                },
            }
        }
    }

    // After per-backend search, add a cross-prover layer: query VeriSimDB
    // for matches across every prover that has ever recorded an attempt.
    // This compensates for backends without a native search command (the
    // 70+ that legitimately return Vec::new() because their underlying
    // prover doesn't ship a `Search`-equivalent). No-op without the
    // `verisim` feature; logs and continues on Verisim outage.
    let verisim_url =
        std::env::var("VERISIM_URL").unwrap_or_else(|_| "http://localhost:8080".to_string());
    match echidna::vcl_ut::cross_prover_search_names(&verisim_url, &pattern, limit).await {
        Ok(cross) if !cross.is_empty() => {
            formatter.section("\nCross-prover (VeriSimDB) Results:")?;
            total_results += cross.len();
            for (i, result) in cross.iter().take(limit).enumerate() {
                formatter.result(&format!("  {}. {}", i + 1, result))?;
            }
            if cross.len() > limit {
                formatter.info(&format!("  ... and {} more results", cross.len() - limit))?;
            }
        },
        Ok(_) => {},
        Err(e) => {
            warn!("Cross-prover search failed: {}", e);
        },
    }

    formatter.info(&format!("\nTotal results found: {}", total_results))?;

    Ok(())
}
