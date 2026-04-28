// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Substitution generator.
//!
//! For each tactic site in a probe, look up alternatives in the synonym
//! table and produce one `Variant` per (site, alternative) pair.
//!
//! V1 constraint: single-site substitutions only.  Multi-site combinations
//! are gated behind `--max-substitutions N` (unimplemented in v1).

use super::extractor::{Probe, TacticSite};
use super::synonyms::SynonymTable;

/// A candidate substitution ready for testing.
#[derive(Debug, Clone)]
pub struct Variant {
    pub site: TacticSite,
    /// The original tactic name that was replaced.
    pub original: String,
    /// The alternative name we substituted in.
    pub replacement: String,
    /// Full probe source with the substitution applied.
    pub probe_source: String,
    /// Levenshtein distance between original and replacement (for ranking).
    pub edit_distance: u32,
}

/// Generate all single-site variants for `probe` given synonym `table`.
///
/// Only substitutions where the table knows about `site.name` are generated.
/// The original name is not included as a "variant" (it presumably fails).
pub fn generate_variants(probe: &Probe, table: &SynonymTable) -> Vec<Variant> {
    let mut variants = Vec::new();
    let full_source = probe.full_source();

    for site in &probe.tactic_sites {
        let alts = table.alternatives(&site.name);
        for alt in alts {
            let substituted = substitute_at_site(&full_source, &site.name, &alt, site.line, site.col, probe);
            let ed = levenshtein(&site.name, &alt);
            variants.push(Variant {
                site: site.clone(),
                original: site.name.clone(),
                replacement: alt,
                probe_source: substituted,
                edit_distance: ed,
            });
        }
    }

    // Sort by edit distance ascending so cheapest substitutions come first.
    variants.sort_by_key(|v| v.edit_distance);
    variants
}

/// Replace the first occurrence of `original` at approximately `(line, col)`
/// in `full_source` with `replacement`.
///
/// The search is line-based and replaces the leftmost word-boundary match on
/// the target line.  If the line is not found, falls back to the first global
/// occurrence.  This is the v1 approximation documented in the design brief.
fn substitute_at_site(
    full_source: &str,
    original: &str,
    replacement: &str,
    line: usize,
    _col: usize,
    probe: &Probe,
) -> String {
    // Adjust line to the full source (which may have preamble prepended).
    let preamble_lines = if probe.preamble.is_empty() {
        0
    } else {
        probe.preamble.lines().count() + 1 // +1 for the \n separator
    };
    let target_line = line + preamble_lines;

    let lines: Vec<&str> = full_source.lines().collect();
    if target_line == 0 || target_line > lines.len() {
        // fallback: first occurrence in whole source
        return replace_word_first(full_source, original, replacement);
    }

    let mut result_lines: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
    let idx = target_line - 1;
    result_lines[idx] = replace_word_first(&result_lines[idx], original, replacement);
    result_lines.join("\n")
}

/// Replace the first whole-word occurrence of `word` in `text` with `replacement`.
fn replace_word_first(text: &str, word: &str, replacement: &str) -> String {
    if let Some(pos) = find_word_boundary(text, word) {
        let mut out = String::with_capacity(text.len() + replacement.len());
        out.push_str(&text[..pos]);
        out.push_str(replacement);
        out.push_str(&text[pos + word.len()..]);
        out
    } else {
        text.to_string()
    }
}

/// Find the start position of the first whole-word occurrence of `word` in `text`.
fn find_word_boundary(text: &str, word: &str) -> Option<usize> {
    let mut start = 0;
    while start + word.len() <= text.len() {
        if let Some(pos) = text[start..].find(word) {
            let abs_pos = start + pos;
            let before_ok = abs_pos == 0 || !is_ident_char(text.as_bytes()[abs_pos - 1] as char);
            let after_pos = abs_pos + word.len();
            let after_ok = after_pos >= text.len() || !is_ident_char(text.as_bytes()[after_pos] as char);
            if before_ok && after_ok {
                return Some(abs_pos);
            }
            start = abs_pos + 1;
        } else {
            break;
        }
    }
    None
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Compute Levenshtein edit distance between two strings.
pub fn levenshtein(a: &str, b: &str) -> u32 {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let (n, m) = (a.len(), b.len());
    if n == 0 { return m as u32; }
    if m == 0 { return n as u32; }
    let mut dp = vec![vec![0u32; m + 1]; n + 1];
    for i in 0..=n { dp[i][0] = i as u32; }
    for j in 0..=m { dp[0][j] = j as u32; }
    for i in 1..=n {
        for j in 1..=m {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            dp[i][j] = (dp[i - 1][j] + 1)
                .min(dp[i][j - 1] + 1)
                .min(dp[i - 1][j - 1] + cost);
        }
    }
    dp[n][m]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::suggest::extractor::{Probe, TacticSite};
    use crate::suggest::synonyms::{SynonymEntry, SynonymTable};
    use crate::ProverKind;

    fn make_probe(lemma_source: &str, sites: Vec<TacticSite>) -> Probe {
        Probe {
            prover: ProverKind::Isabelle,
            preamble: String::new(),
            lemma_source: lemma_source.to_string(),
            tactic_sites: sites,
        }
    }

    fn make_table() -> SynonymTable {
        SynonymTable::from_entries(vec![SynonymEntry {
            canonical: "induction".to_string(),
            aliases: vec!["induct".to_string()],
            tactic_class: None,
            notes: None,
            since: None,
            until: None,
            semantic_class: None,
        }])
    }

    #[test]
    fn test_generate_variants_basic() {
        let probe = make_probe(
            "lemma foo:\n  by (induct x)\n  done",
            vec![TacticSite { line: 2, col: 6, name: "induct".to_string() }],
        );
        let table = make_table();
        let variants = generate_variants(&probe, &table);
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].replacement, "induction");
        assert!(variants[0].probe_source.contains("induction"));
        assert!(!variants[0].probe_source.contains("induct ") || variants[0].probe_source.contains("induction"));
    }

    #[test]
    fn test_generate_variants_no_table_match() {
        let probe = make_probe(
            "lemma foo:\n  by auto\n  done",
            vec![TacticSite { line: 2, col: 6, name: "auto".to_string() }],
        );
        let table = make_table();
        // "auto" is not in the table, so no variants
        let variants = generate_variants(&probe, &table);
        assert!(variants.is_empty());
    }

    #[test]
    fn test_levenshtein() {
        assert_eq!(levenshtein("induct", "induction"), 3);
        assert_eq!(levenshtein("", "abc"), 3);
        assert_eq!(levenshtein("abc", "abc"), 0);
        assert_eq!(levenshtein("omega", "lia"), 4);
    }

    #[test]
    fn test_replace_word_boundary() {
        // Should replace "induct" but not "induction" or "inducted"
        let text = "apply (induct x) (induction y) (induced z)";
        let result = replace_word_first(text, "induct", "induction");
        assert!(result.starts_with("apply (induction x)"), "got: {}", result);
        // "induction y" part should be unchanged
        assert!(result.contains("(induction y)"));
    }
}
