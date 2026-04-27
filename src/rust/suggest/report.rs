// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Result formatter for `echidna suggest`.
//!
//! Emits a Markdown table to stdout, sorted by outcome then edit distance.

use super::tester::{VariantOutcome, VariantResult};

/// Print a sorted result table to stdout.
pub fn print_report(mut results: Vec<VariantResult>, dry_run: bool) {
    if results.is_empty() {
        println!("No variants found in synonym tables for the tactic sites in this probe.");
        println!("Consider expanding `data/synonyms/<prover>.toml` with more entries.");
        return;
    }

    // Sort: closes first, then fails, then timeout, then invalid; within each group by edit distance.
    results.sort_by(|a, b| {
        a.outcome
            .sort_key()
            .cmp(&b.outcome.sort_key())
            .then(a.variant.edit_distance.cmp(&b.variant.edit_distance))
    });

    if dry_run {
        println!("| Variant | Site | Edit distance |");
        println!("|---------|------|---------------|");
        for r in &results {
            println!(
                "| `{}` → `{}` | line {} col {} | {} |",
                r.variant.original,
                r.variant.replacement,
                r.variant.site.line,
                r.variant.site.col,
                r.variant.edit_distance,
            );
        }
    } else {
        println!("| Variant | Site | Outcome | Edit |");
        println!("|---------|------|---------|------|");
        for r in &results {
            let outcome_str = match &r.outcome {
                VariantOutcome::Closes => "✅ closes".to_string(),
                VariantOutcome::Fails(msg) => {
                    let short = msg.lines().next().unwrap_or("failed").chars().take(60).collect::<String>();
                    format!("❌ {}", short)
                }
                VariantOutcome::Timeout => "⏱ timeout".to_string(),
                VariantOutcome::InvalidSyntax(msg) => {
                    let short = msg.lines().next().unwrap_or("syntax error").chars().take(60).collect::<String>();
                    format!("⚠ syntax: {}", short)
                }
            };
            println!(
                "| `{}` → `{}` | line {} col {} | {} | {} |",
                r.variant.original,
                r.variant.replacement,
                r.variant.site.line,
                r.variant.site.col,
                outcome_str,
                r.variant.edit_distance,
            );
        }

        let closes_count = results
            .iter()
            .filter(|r| r.outcome == VariantOutcome::Closes)
            .count();

        println!();
        if closes_count > 0 {
            println!("{} variant(s) close the proof.", closes_count);
        } else {
            println!("No variants closed the proof.");
            println!("If all variants fail, the issue may not be tactic-name drift.");
            println!("Try `echidna prove --diagnose` for a deeper failure analysis.");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::suggest::extractor::TacticSite;
    use crate::suggest::variant::Variant;

    fn make_result(original: &str, replacement: &str, outcome: VariantOutcome) -> VariantResult {
        VariantResult {
            variant: Variant {
                site: TacticSite { line: 7, col: 12, name: original.to_string() },
                original: original.to_string(),
                replacement: replacement.to_string(),
                probe_source: String::new(),
                edit_distance: super::super::variant::levenshtein(original, replacement),
            },
            outcome,
        }
    }

    #[test]
    fn test_print_report_empty() {
        // Should not panic
        print_report(vec![], false);
    }

    #[test]
    fn test_print_report_with_results() {
        let results = vec![
            make_result("induct", "induction", VariantOutcome::Closes),
            make_result("auto", "force", VariantOutcome::Fails("tactic failed".to_string())),
        ];
        // Should not panic; output goes to stdout (captured in test harness)
        print_report(results, false);
    }

    #[test]
    fn test_print_report_dry_run() {
        let results = vec![
            make_result("induct", "induction", VariantOutcome::Fails("dry-run".to_string())),
        ];
        print_report(results, true);
    }
}
