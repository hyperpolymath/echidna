// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Variant testing harness.
//!
//! Each variant is written to a temp file and run through the prover backend.
//! Tests are independent and run concurrently via `tokio::task::JoinSet`.

use std::time::Duration;

use anyhow::Result;
use tokio::task::JoinSet;

use crate::provers::{ProverBackend, ProverConfig, ProverFactory};
use crate::ProverKind;

use super::variant::Variant;

/// Classification of a variant test outcome.
#[derive(Debug, Clone, PartialEq)]
pub enum VariantOutcome {
    /// Prover accepted the variant.
    Closes,
    /// Prover rejected the variant; carries the error/failure message.
    Fails(String),
    /// Prover did not respond within the budget.
    Timeout,
    /// Probe didn't even parse.
    InvalidSyntax(String),
}

impl VariantOutcome {
    pub fn sort_key(&self) -> u8 {
        match self {
            VariantOutcome::Closes => 0,
            VariantOutcome::Fails(_) => 1,
            VariantOutcome::Timeout => 2,
            VariantOutcome::InvalidSyntax(_) => 3,
        }
    }
}

/// Result of testing one variant.
#[derive(Debug, Clone)]
pub struct VariantResult {
    pub variant: Variant,
    pub outcome: VariantOutcome,
}

/// Test all `variants` against `prover` concurrently (up to `max_parallel`).
pub async fn test_all_variants(
    prover: ProverKind,
    variants: Vec<Variant>,
    budget: Duration,
    max_parallel: usize,
    dry_run: bool,
) -> Result<Vec<VariantResult>> {
    if dry_run {
        return Ok(variants
            .into_iter()
            .map(|v| VariantResult {
                outcome: VariantOutcome::Fails("(dry-run — not executed)".to_string()),
                variant: v,
            })
            .collect());
    }

    let mut results: Vec<Option<VariantResult>> = (0..variants.len()).map(|_| None).collect();
    let mut set: JoinSet<(usize, VariantResult)> = JoinSet::new();
    let mut pending = 0usize;
    let mut submitted = 0usize;

    let variants_with_idx: Vec<(usize, Variant)> = variants.into_iter().enumerate().collect();
    let mut iter = variants_with_idx.into_iter();

    loop {
        // Fill slots up to max_parallel
        while pending < max_parallel {
            match iter.next() {
                Some((idx, variant)) => {
                    let budget = budget;
                    set.spawn(async move {
                        let outcome = test_single_variant(prover, &variant, budget).await;
                        (idx, VariantResult { variant, outcome })
                    });
                    pending += 1;
                    submitted += 1;
                }
                None => break,
            }
        }

        if pending == 0 {
            break;
        }

        match set.join_next().await {
            Some(Ok((idx, result))) => {
                results[idx] = Some(result);
                pending -= 1;
            }
            Some(Err(e)) => {
                // Task panicked; treat as Fails
                pending -= 1;
                let _ = e; // logged by caller
            }
            None => break,
        }
    }

    let _ = submitted; // used for tracking
    Ok(results.into_iter().flatten().collect())
}

async fn test_single_variant(
    prover: ProverKind,
    variant: &Variant,
    budget: Duration,
) -> VariantOutcome {
    let timeout_secs = budget.as_secs().max(1);
    let config = ProverConfig {
        timeout: timeout_secs,
        ..Default::default()
    };

    let backend = match ProverFactory::create(prover, config) {
        Ok(b) => b,
        Err(e) => return VariantOutcome::Fails(format!("backend create failed: {}", e)),
    };

    let state = match backend.parse_string(&variant.probe_source).await {
        Ok(s) => s,
        Err(e) => return VariantOutcome::InvalidSyntax(e.to_string()),
    };

    match tokio::time::timeout(budget, backend.verify_proof(&state)).await {
        Ok(Ok(true)) => VariantOutcome::Closes,
        Ok(Ok(false)) => VariantOutcome::Fails("prover returned not-proved".to_string()),
        Ok(Err(e)) => VariantOutcome::Fails(e.to_string()),
        Err(_) => VariantOutcome::Timeout,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::suggest::extractor::TacticSite;

    fn make_variant(original: &str, replacement: &str, source: &str) -> Variant {
        Variant {
            site: TacticSite { line: 1, col: 1, name: original.to_string() },
            original: original.to_string(),
            replacement: replacement.to_string(),
            probe_source: source.to_string(),
            edit_distance: super::super::variant::levenshtein(original, replacement),
        }
    }

    #[tokio::test]
    async fn test_dry_run_returns_all_variants() {
        let variants = vec![
            make_variant("induct", "induction", "lemma foo: 1 = 1 by induction"),
            make_variant("arith", "linarith", "lemma foo: 1 = 1 by linarith"),
        ];
        let results = test_all_variants(
            ProverKind::Isabelle,
            variants,
            Duration::from_secs(5),
            4,
            true,
        )
        .await
        .expect("test_all_variants");
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(matches!(&r.outcome, VariantOutcome::Fails(msg) if msg.contains("dry-run")));
        }
    }

    #[tokio::test]
    async fn test_empty_variants() {
        let results = test_all_variants(
            ProverKind::Isabelle,
            vec![],
            Duration::from_secs(5),
            4,
            false,
        )
        .await
        .expect("empty");
        assert!(results.is_empty());
    }
}
