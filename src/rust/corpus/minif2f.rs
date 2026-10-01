// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! MiniF2F adapter for the corpus indexer.
//!
//! MiniF2F (Zheng et al., 2021, arXiv:2109.00110) is a 488-problem
//! olympiad/competition benchmark formalised in multiple proof
//! systems. Upstream repository layout is one subdirectory per system:
//!
//! ```text
//! minif2f/
//!   lean/src/*.lean
//!   isabelle/*.thy
//!   hollight/*.ml
//!   metamath/*.mm
//!   coq/*.v
//! ```
//!
//! Naming convention (preserved verbatim): `mathd_<branch>_<id>`,
//! `imo_<year>_p<n>`, `aime_<year>_p<n>`, `amc_<year>_p<n>`, …
//!
//! This adapter is deliberately language-agnostic. Rather than ship
//! five proper grammars we use a uniform line scanner that recognises
//! the common opening tokens (`theorem`, `lemma`, `Theorem`,
//! `Lemma`, `prove`, MetaMath `$p`) and walks until a terminator
//! token (`qed`, `done`, `Qed.`, `End`, `$.`) or a blank line. This
//! costs precision on free-form proofs but the MiniF2F corpus is
//! highly templated — every problem is a single theorem with a known
//! name — and the lossy scan is good enough to feed the corpus
//! indexer.
//!
//! Hazards: `sorry`, `admit`, empty body, `TODO` in comments.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

const SUPPORTED_EXTS: &[&str] = &["lean", "thy", "ml", "mm", "v"];

/// Walk `root` and produce a corpus.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_minif2f(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "minif2f".to_string(),
        ..Default::default()
    };

    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let module_name = rel
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "minif2f".to_string());
        let ext = rel
            .extension()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .to_string();

        let module_idx = corpus.modules.len();
        corpus.modules.push(ModuleEntry {
            name: module_name.clone(),
            path: rel,
            options: vec![ext.clone()],
            imports: Vec::new(),
            entries: Vec::new(),
        });

        for d in parse_uniform(&raw, &ext) {
            let entry_idx = corpus.entries.len();
            let qualified = format!("minif2f.{}.{}", module_name, d.name);
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(CorpusEntry {
                name: d.name,
                qualified,
                module_idx,
                kind: DeclKind::Function,
                statement: d.statement,
                proof: d.proof,
                line: d.line,
                dependencies: Vec::new(),
                axiom_usage: d.axiom_usage,
            });
        }
    }

    corpus.reindex();
    Ok(corpus)
}

fn walk_minif2f(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir).with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name_s = entry.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if matches!(
                name_s.as_str(),
                ".git" | "target" | "_build" | "_target" | "lake-packages" | ".lake"
            ) {
                continue;
            }
            walk_minif2f(&p, out)?;
        } else if let Some(ext) = p.extension().and_then(|s| s.to_str()) {
            if SUPPORTED_EXTS.contains(&ext) {
                out.push(p);
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
struct DraftDecl {
    name: String,
    statement: String,
    proof: Option<String>,
    line: usize,
    axiom_usage: AxiomUsage,
}

/// Per-language opening tokens that introduce a theorem-shaped decl.
/// Order matters only for prefix-matching readability.
fn opening_tokens(ext: &str) -> &'static [&'static str] {
    match ext {
        "lean" => &["theorem ", "lemma ", "example "],
        "thy" => &["theorem ", "lemma ", "Theorem ", "Lemma "],
        "ml" => &["prove ", "let "],
        "mm" => &["$p ", "${ "],
        "v" => &["Theorem ", "Lemma ", "Corollary ", "Fact ", "Proposition "],
        _ => &["theorem ", "lemma ", "Theorem ", "Lemma "],
    }
}

/// Terminator tokens that end a proof body.
fn terminators(ext: &str) -> &'static [&'static str] {
    match ext {
        "lean" => &[], // blank-line terminated; no `qed`
        "thy" => &["qed", "done", "."],
        "ml" => &[";;"],
        "mm" => &["$."],
        "v" => &["Qed.", "Defined.", "Admitted.", "Abort."],
        _ => &["qed", "done", "Qed."],
    }
}

/// Identify the start-of-statement on a line and return
/// `(opening_token_index, name)` if found.
fn match_opening(line: &str, ext: &str) -> Option<(usize, String)> {
    let trim = line.trim_start();
    for kw in opening_tokens(ext) {
        if let Some(rest) = trim.strip_prefix(*kw) {
            // First identifier-shaped token after the keyword is the
            // name. MiniF2F names are ASCII-safe by convention
            // (`mathd_algebra_42`, `imo_1959_p1`).
            let name: String = rest
                .chars()
                .take_while(|c| {
                    !c.is_whitespace()
                        && *c != '('
                        && *c != ':'
                        && *c != '{'
                        && *c != '['
                        && *c != ','
                })
                .collect();
            if !name.is_empty() {
                let kw_offset = line.len() - trim.len();
                return Some((kw_offset, name));
            }
        }
    }
    None
}

fn parse_uniform(raw: &str, ext: &str) -> Vec<DraftDecl> {
    let lines: Vec<&str> = raw.lines().collect();
    let terms = terminators(ext);
    let mut decls: Vec<DraftDecl> = Vec::new();

    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let Some((_, name)) = match_opening(line, ext) else {
            i += 1;
            continue;
        };

        // Statement = this line plus continuation up to one of:
        //   * `:=` (Lean term-mode start)
        //   * `:= by` / `by` (Lean tactic mode)
        //   * `proof` / `Proof.` (Isabelle / Coq)
        //   * blank line
        let mut stmt = line.trim().to_string();
        let mut j = i + 1;
        let mut started_proof = false;
        let split_markers = [":=", " by", " by\n", "proof", "Proof.", "begin"];
        let already_has = |s: &str| split_markers.iter().any(|m| s.contains(m));
        if already_has(&stmt) {
            started_proof = true;
        }
        while !started_proof && j < lines.len() {
            let nl = lines[j];
            if nl.trim().is_empty() {
                j += 1;
                break;
            }
            stmt.push(' ');
            stmt.push_str(nl.trim());
            if already_has(nl) {
                started_proof = true;
                j += 1;
                break;
            }
            j += 1;
        }

        // Proof body = subsequent lines up to a terminator or blank
        // line, or — for `lean` — the next top-level opener.
        let mut body = String::new();
        let mut k = j;
        if started_proof {
            while k < lines.len() {
                let bl = lines[k];
                let trim = bl.trim();
                if trim.is_empty() {
                    k += 1;
                    break;
                }
                if match_opening(bl, ext).is_some() && k != i {
                    break;
                }
                body.push(' ');
                body.push_str(trim);
                if terms.iter().any(|t| trim.ends_with(t) || trim == *t) {
                    k += 1;
                    break;
                }
                k += 1;
            }
        }

        let statement = normalise_ws(&stmt);
        let proof = if body.trim().is_empty() {
            None
        } else {
            Some(normalise_ws(&body))
        };

        let mut hz = AxiomUsage::default();
        let scan = match &proof {
            Some(p) => format!("{} {}", statement, p),
            None => statement.clone(),
        };
        flag_hazards(&scan, &mut hz);
        if proof.is_none() {
            hz.other.push("empty_body".to_string());
        }
        if scan.contains("TODO") {
            hz.other.push("todo".to_string());
        }

        decls.push(DraftDecl {
            name,
            statement,
            proof,
            line: line_no,
            axiom_usage: hz,
        });

        i = k.max(j).max(i + 1);
    }

    decls
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("sorry") {
        hz.sorry = true;
    }
    // Match `admit` as a whole-word-ish token to avoid firing on
    // `admitted by` keywords inside narrative comments — cheap and
    // good enough for a structural scan.
    if text.contains(" admit") || text.starts_with("admit") || text.contains("Admitted") {
        hz.admitted = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_lean_mathd_theorem() {
        let src =
            "theorem mathd_algebra_42 (x : \u{211d}) (h : x + 1 = 2) : x = 1 := by\n  linarith\n";
        let decls = parse_uniform(src, "lean");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "mathd_algebra_42");
        assert!(decls[0].statement.contains("x + 1 = 2"));
        assert!(decls[0].proof.as_deref().unwrap().contains("linarith"));
        assert!(!decls[0].axiom_usage.sorry);
    }

    #[test]
    fn detects_sorry_hazard_in_lean() {
        let src = "theorem imo_1959_p1 (n : \u{2115}) : True := by\n  sorry\n";
        let decls = parse_uniform(src, "lean");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "imo_1959_p1");
        assert!(decls[0].axiom_usage.sorry);
    }

    #[test]
    fn parses_multiple_lean_decls() {
        let src = concat!(
            "theorem mathd_algebra_1 (x : \u{211d}) : x = x := by rfl\n",
            "\n",
            "theorem mathd_algebra_2 (y : \u{2115}) : y + 0 = y := by simp\n",
        );
        let decls = parse_uniform(src, "lean");
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "mathd_algebra_1");
        assert_eq!(decls[1].name, "mathd_algebra_2");
    }

    #[test]
    fn parses_coq_theorem_with_terminator() {
        let src = "Theorem amc_1985_p10 : 1 = 1.\nProof.\n  reflexivity.\nQed.\n";
        let decls = parse_uniform(src, "v");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "amc_1985_p10");
        assert!(decls[0].proof.as_deref().unwrap().contains("reflexivity"));
    }

    #[test]
    fn flags_empty_body() {
        let src = "theorem mathd_empty : True\n";
        let decls = parse_uniform(src, "lean");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].axiom_usage.other.iter().any(|t| t == "empty_body"));
    }
}
