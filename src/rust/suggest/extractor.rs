// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Per-prover lemma extractor.
//!
//! Given a file path and a lemma name, each extractor returns a `Probe`
//! containing the lemma source and a preamble of the imports and definitions
//! that appear before it in the file.
//!
//! ## V1 limitations
//!
//! - Preamble extraction is line-based: everything before the target lemma
//!   is included verbatim.  Cross-file dependency tracking is out of scope.
//! - Multi-line constructs are handled heuristically: we detect end-of-block
//!   markers (`qed.`, `:=`, `by`, end-indentation) per prover.
//! - Tactic site detection within the lemma source is keyword-based
//!   (column resolution is approximate).

use anyhow::{bail, Context, Result};
use std::path::Path;

use crate::ProverKind;

/// A tactic or lemma-reference occurrence inside the probe.
#[derive(Debug, Clone)]
pub struct TacticSite {
    /// 1-indexed line within `lemma_source`.
    pub line: usize,
    /// 1-indexed column (byte offset from line start, approximate).
    pub col: usize,
    /// The tactic or lemma name found at this position.
    pub name: String,
}

/// A self-contained proof probe ready for substitution and re-checking.
#[derive(Debug, Clone)]
pub struct Probe {
    pub prover: ProverKind,
    /// The imports / opens / definitions preceding the target lemma in the
    /// same file.  May be empty if the lemma is self-contained.
    pub preamble: String,
    /// The lemma source itself.
    pub lemma_source: String,
    /// Identified tactic occurrences (name + location within `lemma_source`).
    pub tactic_sites: Vec<TacticSite>,
}

impl Probe {
    /// Full source that can be handed to the prover: preamble + lemma.
    pub fn full_source(&self) -> String {
        if self.preamble.is_empty() {
            self.lemma_source.clone()
        } else {
            format!("{}\n{}", self.preamble, self.lemma_source)
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level dispatcher
// ---------------------------------------------------------------------------

/// Extract named lemma from `path` for the given prover.
pub fn extract(prover: ProverKind, path: &Path, lemma_name: &str) -> Result<Probe> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Cannot read {}", path.display()))?;
    match prover {
        ProverKind::Isabelle => extract_isabelle(&content, lemma_name),
        ProverKind::Coq => extract_coq(&content, lemma_name),
        ProverKind::Lean => extract_lean4(&content, lemma_name),
        ProverKind::Idris2 => extract_idris2(&content, lemma_name),
        ProverKind::Agda => extract_agda(&content, lemma_name),
        other => bail!(
            "echidna suggest: no extractor for prover {:?} (unsupported for v1)",
            other
        ),
    }
    .map(|mut p| {
        p.prover = prover;
        p
    })
}

// ---------------------------------------------------------------------------
// Isabelle/HOL  (.thy)
// ---------------------------------------------------------------------------

fn extract_isabelle(content: &str, lemma_name: &str) -> Result<Probe> {
    let lines: Vec<&str> = content.lines().collect();
    let start_pat = format!("lemma {}:", lemma_name);
    let alt_pat = format!("theorem {}:", lemma_name);

    let lemma_start = lines
        .iter()
        .position(|l| {
            let t = l.trim();
            t.starts_with(&start_pat) || t.starts_with(&alt_pat)
        })
        .with_context(|| format!("Lemma '{}' not found in Isabelle file", lemma_name))?;

    // Collect lemma lines until we hit a top-level `qed` or `done` at indent 0
    let mut lemma_lines = vec![lines[lemma_start]];
    let mut depth = 1usize;
    for line in &lines[lemma_start + 1..] {
        lemma_lines.push(line);
        let t = line.trim();
        if t == "proof" || t.starts_with("proof ") {
            depth += 1;
        }
        if t == "qed" || t == "done" || t == "sorry" || t == "oops" {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                break;
            }
        }
    }

    let preamble = lines[..lemma_start].join("\n");
    let lemma_source = lemma_lines.join("\n");
    let tactic_sites = find_tactic_sites_isabelle(&lemma_source);
    Ok(Probe {
        prover: ProverKind::Isabelle,
        preamble,
        lemma_source,
        tactic_sites,
    })
}

fn find_tactic_sites_isabelle(source: &str) -> Vec<TacticSite> {
    // Keywords that appear before a tactic name we want to substitute.
    // Pattern: `apply (TACTIC_NAME ...` or `by TACTIC_NAME` or `using LEMMA_NAME`
    let mut sites = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let line_no = line_idx + 1;
        // apply (tactic ...) or apply tactic
        if let Some(rest) = line.trim().strip_prefix("apply (").or_else(|| line.trim().strip_prefix("apply ")) {
            let name = rest.split_whitespace().next().unwrap_or("").trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
            if !name.is_empty() {
                let col = line.find(name).unwrap_or(0) + 1;
                sites.push(TacticSite { line: line_no, col, name: name.to_string() });
            }
        }
        // by tactic or by (tactic ...)
        if let Some(rest) = line.trim().strip_prefix("by (").or_else(|| line.trim().strip_prefix("by ")) {
            let name = rest.split_whitespace().next().unwrap_or("").trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
            if !name.is_empty() {
                let col = line.find(name).unwrap_or(0) + 1;
                sites.push(TacticSite { line: line_no, col, name: name.to_string() });
            }
        }
        // rule: <lemma_name>
        if let Some(rest) = line.find("rule:").map(|i| &line[i + 5..]) {
            let name = rest.trim().split_whitespace().next().unwrap_or("").trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
            if !name.is_empty() {
                let col = line.find(name).unwrap_or(0) + 1;
                sites.push(TacticSite { line: line_no, col, name: name.to_string() });
            }
        }
    }
    sites
}

// ---------------------------------------------------------------------------
// Coq / Rocq  (.v)
// ---------------------------------------------------------------------------

fn extract_coq(content: &str, lemma_name: &str) -> Result<Probe> {
    let lines: Vec<&str> = content.lines().collect();
    let patterns = [
        format!("Lemma {} ", lemma_name),
        format!("Lemma {}:", lemma_name),
        format!("Theorem {} ", lemma_name),
        format!("Theorem {}:", lemma_name),
        format!("Proposition {} ", lemma_name),
        format!("Proposition {}:", lemma_name),
    ];

    let lemma_start = lines
        .iter()
        .position(|l| {
            let t = l.trim();
            patterns.iter().any(|p| t.starts_with(p.as_str()))
        })
        .with_context(|| format!("Lemma '{}' not found in Coq file", lemma_name))?;

    let mut lemma_lines = vec![lines[lemma_start]];
    for line in &lines[lemma_start + 1..] {
        lemma_lines.push(line);
        let t = line.trim();
        if t == "Qed." || t == "Defined." || t == "Admitted." || t == "Abort." {
            break;
        }
    }

    let preamble = lines[..lemma_start].join("\n");
    let lemma_source = lemma_lines.join("\n");
    let tactic_sites = find_tactic_sites_coq(&lemma_source);
    Ok(Probe {
        prover: ProverKind::Coq,
        preamble,
        lemma_source,
        tactic_sites,
    })
}

fn find_tactic_sites_coq(source: &str) -> Vec<TacticSite> {
    let mut sites = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let line_no = line_idx + 1;
        let t = line.trim();
        // Coq: bare tactic at start of line (after optional spaces/`- ` bullet)
        let t_nobullet = t.trim_start_matches(|c: char| c == '-' || c == '+' || c == '*' || c == ' ');
        let name = t_nobullet.split(|c: char| !c.is_alphanumeric() && c != '_').next().unwrap_or("");
        if !name.is_empty() && !["Proof", "Qed", "Defined", "Admitted", "Abort", "Lemma", "Theorem"].contains(&name) {
            let col = line.find(name).unwrap_or(0) + 1;
            sites.push(TacticSite { line: line_no, col, name: name.to_string() });
        }
    }
    sites
}

// ---------------------------------------------------------------------------
// Lean 4  (.lean)
// ---------------------------------------------------------------------------

fn extract_lean4(content: &str, lemma_name: &str) -> Result<Probe> {
    let lines: Vec<&str> = content.lines().collect();
    let patterns = [
        format!("theorem {} ", lemma_name),
        format!("theorem {}", lemma_name),
        format!("lemma {} ", lemma_name),
        format!("lemma {}", lemma_name),
    ];

    let lemma_start = lines
        .iter()
        .position(|l| {
            let t = l.trim();
            patterns.iter().any(|p| t.starts_with(p.as_str()))
        })
        .with_context(|| format!("Lemma '{}' not found in Lean 4 file", lemma_name))?;

    // Lean 4: theorem ends when next top-level decl starts (no indent) or file ends.
    let mut lemma_lines = vec![lines[lemma_start]];
    for line in &lines[lemma_start + 1..] {
        // A new top-level keyword at column 0 ends the block
        let first_char = line.chars().next().unwrap_or(' ');
        if first_char != ' ' && !first_char.is_control() && !line.trim().is_empty() {
            let t = line.trim();
            if t.starts_with("theorem ") || t.starts_with("lemma ") || t.starts_with("def ") || t.starts_with("#") || t.starts_with("import ") || t.starts_with("open ") {
                break;
            }
        }
        lemma_lines.push(line);
    }

    let preamble = lines[..lemma_start].join("\n");
    let lemma_source = lemma_lines.join("\n");
    let tactic_sites = find_tactic_sites_lean4(&lemma_source);
    Ok(Probe {
        prover: ProverKind::Lean,
        preamble,
        lemma_source,
        tactic_sites,
    })
}

fn find_tactic_sites_lean4(source: &str) -> Vec<TacticSite> {
    let mut sites = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let line_no = line_idx + 1;
        let t = line.trim();
        // Lean 4 tactic block: lines with tactic calls, typically indented
        // Skip structural keywords
        if t.starts_with("theorem ") || t.starts_with("lemma ") || t.starts_with("by") || t.is_empty() {
            if t.starts_with("by ") {
                // "by <tactic>" single-line form
                if let Some(rest) = t.strip_prefix("by ") {
                    let name = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next().unwrap_or("");
                    if !name.is_empty() {
                        let col = line.find(name).unwrap_or(0) + 1;
                        sites.push(TacticSite { line: line_no, col, name: name.to_string() });
                    }
                }
            }
            continue;
        }
        let name = t.split(|c: char| !c.is_alphanumeric() && c != '_').next().unwrap_or("");
        if !name.is_empty() && !["where", "fun", "have", "show", "exact", "rfl", "done"].contains(&name) {
            let col = line.find(name).unwrap_or(0) + 1;
            sites.push(TacticSite { line: line_no, col, name: name.to_string() });
        }
    }
    sites
}

// ---------------------------------------------------------------------------
// Idris 2  (.idr)
// ---------------------------------------------------------------------------

fn extract_idris2(content: &str, lemma_name: &str) -> Result<Probe> {
    let lines: Vec<&str> = content.lines().collect();
    // Idris2: `name : Type` followed by clauses
    let type_pat = format!("{} :", lemma_name);

    let lemma_start = lines
        .iter()
        .position(|l| l.trim().starts_with(&type_pat))
        .with_context(|| format!("Definition '{}' not found in Idris 2 file", lemma_name))?;

    let mut lemma_lines = vec![lines[lemma_start]];
    // Collect clause lines: lines that start with `lemma_name ` or are continuation (indented)
    let clause_prefix = format!("{} ", lemma_name);
    let clause_prefix2 = format!("{}(", lemma_name);
    for line in &lines[lemma_start + 1..] {
        let t = line.trim();
        if t.is_empty() {
            // blank line ends the block
            break;
        }
        if line.starts_with(' ') || line.starts_with('\t') || t.starts_with(&clause_prefix) || t.starts_with(&clause_prefix2) {
            lemma_lines.push(line);
        } else {
            break;
        }
    }

    let preamble = lines[..lemma_start].join("\n");
    let lemma_source = lemma_lines.join("\n");
    let tactic_sites = find_tactic_sites_idris2(&lemma_source);
    Ok(Probe {
        prover: ProverKind::Idris2,
        preamble,
        lemma_source,
        tactic_sites,
    })
}

fn find_tactic_sites_idris2(source: &str) -> Vec<TacticSite> {
    let mut sites = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let line_no = line_idx + 1;
        let t = line.trim();
        // Look for `?proof_name` holes or `believe_me` / tactic names
        for word in t.split_whitespace() {
            let name = word.trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
            if name.starts_with("believe_me") || name.starts_with("rewrite") || name.starts_with("exact") || name.starts_with("Refl") {
                let col = line.find(name).unwrap_or(0) + 1;
                sites.push(TacticSite { line: line_no, col, name: name.to_string() });
                break;
            }
        }
    }
    sites
}

// ---------------------------------------------------------------------------
// Agda  (.agda)
// ---------------------------------------------------------------------------

fn extract_agda(content: &str, lemma_name: &str) -> Result<Probe> {
    let lines: Vec<&str> = content.lines().collect();
    let type_pat = format!("{} :", lemma_name);

    let lemma_start = lines
        .iter()
        .position(|l| l.trim().starts_with(&type_pat))
        .with_context(|| format!("Definition '{}' not found in Agda file", lemma_name))?;

    let mut lemma_lines = vec![lines[lemma_start]];
    let clause_prefix = format!("{} ", lemma_name);
    for line in &lines[lemma_start + 1..] {
        let t = line.trim();
        if t.is_empty() {
            break;
        }
        if line.starts_with(' ') || line.starts_with('\t') || t.starts_with(&clause_prefix) {
            lemma_lines.push(line);
        } else {
            break;
        }
    }

    let preamble = lines[..lemma_start].join("\n");
    let lemma_source = lemma_lines.join("\n");
    let tactic_sites = find_tactic_sites_agda(&lemma_source);
    Ok(Probe {
        prover: ProverKind::Agda,
        preamble,
        lemma_source,
        tactic_sites,
    })
}

fn find_tactic_sites_agda(source: &str) -> Vec<TacticSite> {
    let mut sites = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let line_no = line_idx + 1;
        // Agda: look for common combinator names in term position
        for word in line.split_whitespace() {
            let name = word.trim_matches(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'');
            if ["refl", "sym", "trans", "cong", "subst"].contains(&name) {
                let col = line.find(name).unwrap_or(0) + 1;
                sites.push(TacticSite { line: line_no, col, name: name.to_string() });
            }
        }
    }
    sites
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const ISABELLE_FILE: &str = r#"
theory Foo
imports Main
begin

lemma bar: "a + b = b + a"
  by (simp add: add.commute)

lemma baz: "True"
  by auto

end
"#;

    const COQFILE: &str = r#"
Require Import Arith.

Lemma foo : forall n, n + 0 = n.
Proof.
  intros n. omega.
Qed.
"#;

    const LEAN4_FILE: &str = r#"
import Mathlib.Tactic

theorem my_thm (n : Nat) : n + 0 = n := by
  omega

theorem other : True := by trivial
"#;

    #[test]
    fn test_extract_isabelle_positive() {
        let probe = extract_isabelle(ISABELLE_FILE, "bar").expect("extract bar");
        assert!(probe.lemma_source.contains("lemma bar:"));
        assert!(probe.preamble.contains("imports Main"));
    }

    #[test]
    fn test_extract_isabelle_not_found() {
        assert!(extract_isabelle(ISABELLE_FILE, "nonexistent").is_err());
    }

    #[test]
    fn test_extract_isabelle_tactic_sites() {
        let probe = extract_isabelle(ISABELLE_FILE, "bar").expect("extract");
        // "simp" should be detected via "by (simp add: ...)"
        let has_simp = probe.tactic_sites.iter().any(|s| s.name == "simp");
        assert!(has_simp, "expected simp site in {:?}", probe.tactic_sites);
    }

    #[test]
    fn test_extract_coq_positive() {
        let probe = extract_coq(COQFILE, "foo").expect("extract foo");
        assert!(probe.lemma_source.contains("Lemma foo"));
        assert!(probe.lemma_source.contains("Qed."));
    }

    #[test]
    fn test_extract_coq_not_found() {
        assert!(extract_coq(COQFILE, "missing").is_err());
    }

    #[test]
    fn test_extract_lean4_positive() {
        let probe = extract_lean4(LEAN4_FILE, "my_thm").expect("extract");
        assert!(probe.lemma_source.contains("theorem my_thm"));
        assert!(!probe.lemma_source.contains("theorem other"));
    }

    #[test]
    fn test_extract_lean4_not_found() {
        assert!(extract_lean4(LEAN4_FILE, "no_such").is_err());
    }
}
