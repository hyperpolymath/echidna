// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: lexicon. Moved verbatim from main.rs (hotspot split).

use super::*;
use crate::output::OutputFormatter;
use anyhow::{Context, Result};

/// Lexicon command - mine cross-corpus candidates for curation.
///
/// The scan runs on a thread with a large stack: the canonicaliser's parser
/// recurses on nesting depth, and some corpus statements (ACL2 books) nest
/// deeply. Timings go to stderr; the JCS files under `--out` carry none, so
/// two runs over the same data write the same bytes.
///
/// # Errors
///
/// An unknown preset, a malformed `--pair`, no pairs at all, a corpus that
/// fails to load, an output directory that cannot be created or read, an
/// old output file that cannot be removed, or a serialisation or output
/// write failure. Also returns an error if the scan thread cannot be
/// spawned or panics. Failed scans may leave partial output.
pub(crate) fn lexicon_command(op: LexiconOp, formatter: &OutputFormatter) -> Result<()> {
    use echidna::lexicon::scan::{self, RunOptions, ScanOptions};

    let LexiconOp::Scan {
        training_dir,
        pairs,
        preset,
        out,
        keep_generic,
        max_pairs_per_name,
        max_shape_group,
        collision_samples,
    } = op;

    let mut all_pairs = Vec::new();
    if let Some(name) = preset.as_deref() {
        all_pairs.extend(scan::preset_pairs(name).with_context(|| {
            format!("unknown preset `{name}` (learning, spanning, in-family, full)")
        })?);
    }
    for p in &pairs {
        let pair = scan::parse_pair(p)?;
        // A pair is the same pair in either direction; the first spelling
        // requested is the one scanned.
        let seen = all_pairs
            .iter()
            .any(|(a, b)| (a, b) == (&pair.0, &pair.1) || (a, b) == (&pair.1, &pair.0));
        if !seen {
            all_pairs.push(pair);
        }
    }
    let opts = RunOptions {
        training_dir,
        pairs: all_pairs,
        out,
        scan: ScanOptions {
            keep_generic,
            max_pairs_per_name,
            max_shape_group,
        },
        collision_samples,
    };

    let report = std::thread::Builder::new()
        .name("lexicon-scan".into())
        .stack_size(512 * 1024 * 1024)
        .spawn(move || scan::run(&opts).map(|r| (r, opts.out)))
        .context("spawn the scan thread")?
        .join()
        .map_err(|_| anyhow::anyhow!("the scan thread panicked"))??;
    let (report, out) = report;

    if formatter.is_json() {
        // One JCS object on stdout; the timings stay on stderr.
        let summary = serde_json::json!({
            "coverage": report.coverage,
            "pairs": report.pairs,
            "out": out.display().to_string(),
            "total_ms": u64::try_from(report.total.as_millis()).unwrap_or(u64::MAX),
        });
        std::io::Write::write_all(&mut std::io::stdout(), &scan::jcs_line(&summary)?)?;
        eprintln!("total: {:.2?}; output in {}", report.total, out.display());
        return Ok(());
    }

    println!(
        "{:<14} {:>8} {:>8} {:>6} {:>7} {:>6} {:>6} {:>6} {:>8}",
        "corpus", "rows", "names", "hom%", "struct%", "skel%", "text%", "cmpl%", "collide"
    );
    for c in &report.coverage {
        let pct = |n: usize| 100.0 * n as f64 / c.rows.max(1) as f64;
        println!(
            "{:<14} {:>8} {:>8} {:>6.1} {:>7.1} {:>6.1} {:>6.1} {:>6.1} {:>8}",
            c.corpus,
            c.rows,
            c.names,
            100.0 * c.homonym_names as f64 / c.names.max(1) as f64,
            pct(c.tiers.structural),
            pct(c.tiers.skeleton),
            pct(c.tiers.text),
            pct(c.tiers.complete),
            c.collision_keys
        );
    }
    println!();
    println!(
        "{:<26} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>8} {:>7} {:>7} {:>7}",
        "pair",
        "shared",
        "generic",
        "capped",
        "exact",
        "shape",
        "skel",
        "differs",
        "unparsed",
        "syn-tx",
        "syn-sh",
        "syn-sk"
    );
    for s in &report.pairs {
        let names = [&s.candidates.name_exact, &s.candidates.name_folded];
        let sum =
            |f: fn(&scan::CandidateCounts) -> usize| names.iter().map(|c| f(c)).sum::<usize>();
        println!(
            "{:<26} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>8} {:>7} {:>7} {:>7}",
            format!("{}:{}", s.pair[0], s.pair[1]),
            s.folded_names_shared,
            s.generic_names_skipped,
            s.name_pairs_capped,
            sum(|c| c.cognate_exact),
            sum(|c| c.cognate_shape),
            sum(|c| c.cognate_skeleton),
            sum(|c| c.differs),
            sum(|c| c.unparsed),
            s.candidates.text.total(),
            s.candidates.shape.total(),
            s.candidates.skeleton.total()
        );
    }
    for (corpus, t) in &report.load_times {
        eprintln!("load {corpus}: {:.2?}", t);
    }
    for (pair, t) in &report.pair_times {
        eprintln!("scan {pair}: {:.2?}", t);
    }
    eprintln!("total: {:.2?}; output in {}", report.total, out.display());
    Ok(())
}
