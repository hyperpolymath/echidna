// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! `echidna suggest` — mechanical tactic-variant finder.
//!
//! Given a failing lemma, this module:
//!
//! 1. Extracts the lemma from its file into a self-contained `Probe`.
//! 2. Identifies tactic sites (tactic names and lemma references) in the probe.
//! 3. Looks up each site name in the hand-curated synonym table for the prover.
//! 4. Generates one `Variant` per (site, alternative-name) pair.
//! 5. Runs each variant through the prover and classifies the outcome.
//! 6. Prints a ranked Markdown table to stdout.
//!
//! ## V1 limitations
//!
//! - Single-site substitutions only (no combinatorial multi-site).
//! - Preamble extraction is file-local; cross-file dependencies produce an
//!   "unknown definition" error from the prover which is surfaced cleanly.
//! - Prover-version detection is not performed; trust the `--prover` flag.
//! - Does not call `suggest_tactics` on `ProverBackend` — that method is for
//!   ML-ranked suggestions (§4.4 layer); this module is the mechanical baseline.

pub mod extractor;
pub mod report;
pub mod synonyms;
pub mod tester;
pub mod variant;

use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{bail, Context, Result};

use crate::ProverKind;

use extractor::extract;
use report::print_report;
use synonyms::SynonymTable;
use tester::test_all_variants;
use variant::generate_variants;

/// Configuration for a `suggest` run.
pub struct SuggestConfig {
    /// `<file>:<lemma>` target string.
    pub target: String,
    /// Prover to use (auto-detected from extension if None).
    pub prover: Option<ProverKind>,
    /// Time budget per variant attempt.
    pub budget: Duration,
    /// Maximum number of variants to report (truncates after sorting).
    pub top: usize,
    /// Directory containing synonym TOML files.
    pub synonyms_dir: PathBuf,
    /// If true, only list candidate variants; do not execute the prover.
    pub dry_run: bool,
    /// Maximum number of concurrent variant tests.
    pub max_parallel: usize,
}

impl Default for SuggestConfig {
    fn default() -> Self {
        SuggestConfig {
            target: String::new(),
            prover: None,
            budget: Duration::from_secs(60),
            top: 10,
            synonyms_dir: PathBuf::from("data/synonyms"),
            dry_run: false,
            max_parallel: 4,
        }
    }
}

/// Entry point called from `main.rs`.
pub async fn run(config: SuggestConfig) -> Result<()> {
    let (file_path, lemma_name) = parse_target(&config.target)?;

    let prover = match config.prover {
        Some(p) => p,
        None => detect_prover(&file_path)?,
    };

    // Step 1: confirm the probe fails as-is (unless dry_run)
    let probe = extract(prover, &file_path, &lemma_name)
        .with_context(|| format!("Failed to extract lemma '{}' from {}", lemma_name, file_path.display()))?;

    if !config.dry_run {
        // Attempt to verify the original lemma. If it passes, nothing to suggest.
        let config_tmp = crate::ProverConfig {
            timeout: config.budget.as_secs().max(1),
            ..Default::default()
        };
        let backend = crate::provers::ProverFactory::create(prover, config_tmp)
            .context("Failed to create prover backend for baseline check")?;
        let state = backend
            .parse_string(&probe.full_source())
            .await
            .context("Failed to parse probe for baseline check")?;
        match backend.verify_proof(&state).await {
            Ok(true) => {
                println!("ℹ  The lemma already passes — nothing to suggest.");
                println!("   (If you expected it to fail, check that the right lemma was extracted.)");
                return Ok(());
            }
            Ok(false) => {} // expected: it fails, proceed with variants
            Err(e) => {
                eprintln!("warn: baseline check errored ({}); proceeding anyway", e);
            }
        }
    }

    // Step 2: load synonym table
    let table = SynonymTable::load(prover, &config.synonyms_dir)?;
    if table.is_empty() {
        eprintln!(
            "warn: no synonym table found for {:?} at {}",
            prover,
            config.synonyms_dir.display()
        );
        eprintln!("      Run with --dry-run to see what tactic sites were identified.");
    }

    // Step 3: generate variants
    let all_variants = generate_variants(&probe, &table);
    if all_variants.is_empty() {
        println!("No tactic sites matched the synonym table for {:?}.", prover);
        println!(
            "Sites identified: {:?}",
            probe.tactic_sites.iter().map(|s| &s.name).collect::<Vec<_>>()
        );
        println!("Consider adding entries to data/synonyms/{}.toml", prover_table_name(prover));
        return Ok(());
    }

    let variants_to_test = all_variants.into_iter().take(config.top).collect::<Vec<_>>();

    // Step 4: test variants
    let results = test_all_variants(
        prover,
        variants_to_test,
        config.budget,
        config.max_parallel,
        config.dry_run,
    )
    .await?;

    // Step 5: report
    print_report(results, config.dry_run);

    Ok(())
}

fn parse_target(target: &str) -> Result<(PathBuf, String)> {
    let (path_str, lemma) = match target.rsplit_once(':') {
        Some((p, l)) => (p, l),
        None => bail!(
            "TARGET must be in <file>:<lemma> form, e.g. Foo.thy:bar\n\
             Got: {:?}",
            target
        ),
    };
    if lemma.is_empty() {
        bail!("Lemma name cannot be empty in target {:?}", target);
    }
    Ok((PathBuf::from(path_str), lemma.to_string()))
}

fn detect_prover(path: &Path) -> Result<ProverKind> {
    let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    match ext {
        "thy" => Ok(ProverKind::Isabelle),
        "v" => Ok(ProverKind::Coq),
        "lean" => Ok(ProverKind::Lean),
        "idr" => Ok(ProverKind::Idris2),
        "agda" => Ok(ProverKind::Agda),
        _ => bail!(
            "Cannot auto-detect prover from extension .{ext}; use --prover to specify"
        ),
    }
}

fn prover_table_name(prover: ProverKind) -> String {
    match prover {
        ProverKind::Isabelle => "isabelle",
        ProverKind::Coq => "coq",
        ProverKind::Lean => "lean4",
        ProverKind::Idris2 => "idris2",
        ProverKind::Agda => "agda",
        _ => return format!("{:?}", prover).to_lowercase(),
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_target_valid() {
        let (path, lemma) = parse_target("Foo.thy:bar").expect("parse");
        assert_eq!(path, PathBuf::from("Foo.thy"));
        assert_eq!(lemma, "bar");
    }

    #[test]
    fn test_parse_target_with_path() {
        let (path, lemma) = parse_target("tropical-resource-typing/Foo.thy:bar").expect("parse");
        assert_eq!(path, PathBuf::from("tropical-resource-typing/Foo.thy"));
        assert_eq!(lemma, "bar");
    }

    #[test]
    fn test_parse_target_missing_colon() {
        assert!(parse_target("Foo.thy").is_err());
    }

    #[test]
    fn test_parse_target_empty_lemma() {
        assert!(parse_target("Foo.thy:").is_err());
    }

    #[test]
    fn test_detect_prover_extensions() {
        assert_eq!(detect_prover(Path::new("a.thy")).unwrap(), ProverKind::Isabelle);
        assert_eq!(detect_prover(Path::new("a.v")).unwrap(), ProverKind::Coq);
        assert_eq!(detect_prover(Path::new("a.lean")).unwrap(), ProverKind::Lean);
        assert_eq!(detect_prover(Path::new("a.idr")).unwrap(), ProverKind::Idris2);
        assert_eq!(detect_prover(Path::new("a.agda")).unwrap(), ProverKind::Agda);
    }

    #[test]
    fn test_detect_prover_unknown() {
        assert!(detect_prover(Path::new("a.xyz")).is_err());
    }
}
