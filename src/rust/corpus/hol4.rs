// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! HOL4 adapter for the corpus indexer.
//!
//! HOL4 is a Standard ML-hosted LCF prover. By convention every theory
//! lives in a file named `FooScript.sml` which declares its theory via
//! `val _ = new_theory "Foo";` near the top and closes it with
//! `val _ = export_theory();`. Building the script generates
//! `FooTheory.{sig,sml}`, which downstream scripts import via
//! `open FooTheory`.
//!
//! ## What we extract
//!
//! - The declared theory name (from `new_theory`).
//! - `open xTheory yTheory;` import edges.
//! - One `CorpusEntry` per top-level declaration:
//!   * `val NAME = store_thm("NAME", <stmt>, <tac>);` → Function
//!   * `Theorem NAME: <stmt> Proof <tac> QED`        → Function
//!   * `val NAME = Define '<eqn>';`                  → Function
//!   * `Definition NAME: <eqn> End`                  → Function
//!   * `val NAME = new_axiom("NAME", <term>);`       → Postulate
//!   * `Datatype: <body> End`                        → Data
//!   * `Inductive NAME: <body> End`                  → Function
//! - Hazards: `new_axiom`, `mk_thm`, `cheat`, `CHEAT_TAC`, and the
//!   non-reducing `Q.MATCH_ABBREV_TAC` (tracked under `other`).

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_sml(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "hol4".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_hol4_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed.theory_name.clone().unwrap_or_else(|| {
            // Derive from filename: `FooScript.sml` → `Foo`.
            let stem = rel
                .file_stem()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            stem.strip_suffix("Script")
                .map(str::to_string)
                .unwrap_or(stem)
        });
        corpus.modules.push(ModuleEntry {
            name: module_name,
            path: rel,
            options: Vec::new(),
            imports: parsed.imports,
            entries: Vec::new(),
        });

        for d in parsed.decls {
            let entry_idx = corpus.entries.len();
            let qualified = format!("{}.{}", corpus.modules[module_idx].name, d.name);
            all_names.insert(d.name.clone());
            all_names.insert(qualified.clone());
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(CorpusEntry {
                name: d.name,
                qualified,
                module_idx,
                kind: d.kind,
                statement: d.statement,
                proof: d.proof,
                line: d.line,
                dependencies: Vec::new(),
                axiom_usage: d.axiom_usage,
            });
        }
    }

    for i in 0..corpus.entries.len() {
        let own_name = corpus.entries[i].name.clone();
        let own_qualified = corpus.entries[i].qualified.clone();
        let mut haystack = corpus.entries[i].statement.clone();
        if let Some(p) = &corpus.entries[i].proof {
            haystack.push(' ');
            haystack.push_str(p);
        }
        let mut deps: HashSet<String> = HashSet::new();
        for tok in tokenise_idents(&haystack) {
            if tok == own_name || tok == own_qualified {
                continue;
            }
            if all_names.contains(tok) {
                deps.insert(tok.to_string());
            }
        }
        let mut deps: Vec<String> = deps.into_iter().collect();
        deps.sort();
        corpus.entries[i].dependencies = deps;
    }

    corpus.reindex();
    Ok(corpus)
}

fn walk_sml(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir).with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name = entry.file_name();
        let name_s = name.to_string_lossy();
        if p.is_dir() {
            if matches!(
                name_s.as_ref(),
                ".git" | "_build" | "target" | ".cache" | "node_modules"
            ) {
                continue;
            }
            walk_sml(&p, out)?;
        } else if name_s.ends_with("Script.sml") && name_s.as_ref() != "Holmakefile" {
            out.push(p);
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    theory_name: Option<String>,
    imports: Vec<String>,
    decls: Vec<DraftDecl>,
}

#[derive(Debug)]
struct DraftDecl {
    name: String,
    kind: DeclKind,
    statement: String,
    proof: Option<String>,
    line: usize,
    axiom_usage: AxiomUsage,
}

/// Strip SML block comments `(* … *)` (nestable). SML has no
/// line-comment syntax.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut depth: usize = 0;
    while i < bytes.len() {
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b')' {
                depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                depth += 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*' {
            depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_hol4_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();
    let mut pf = ParsedFile::default();

    // Theory name from `val _ = new_theory "X";`.
    for line in &lines {
        if let Some(idx) = line.find("new_theory") {
            let rest = &line[idx + "new_theory".len()..];
            if let Some(start) = rest.find('"') {
                if let Some(end_rel) = rest[start + 1..].find('"') {
                    let name = &rest[start + 1..start + 1 + end_rel];
                    if !name.is_empty() {
                        pf.theory_name = Some(name.to_string());
                        break;
                    }
                }
            }
        }
    }

    // Imports: `open xTheory yTheory zTheory;` — tokens ending in
    // "Theory".
    for line in &lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("open ") {
            let cut = rest.find(';').unwrap_or(rest.len());
            for tok in rest[..cut].split_whitespace() {
                let name = tok.trim_end_matches(',').to_string();
                if !name.is_empty() && !pf.imports.contains(&name) {
                    pf.imports.push(name);
                }
            }
        }
    }

    // Decls. Three syntactic families:
    //   (a) `val NAME = store_thm(...)` / `Define …` / `new_axiom(...)`
    //   (b) `Theorem NAME: <stmt> Proof <tac> QED`
    //   (c) `Definition NAME: <eqn> End` / `Inductive NAME: <body> End`
    //       / `Datatype: <body> End`
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let t = line.trim_start();

        // (b) `Theorem NAME:` or `Theorem NAME ...`
        if t.starts_with("Theorem ") && column_of(line) == 0 {
            if let Some((name, head_stmt)) = split_named_block(t, "Theorem") {
                // Accumulate until we see `QED` at column 0.
                let mut stmt = head_stmt.trim().to_string();
                let mut proof_buf = String::new();
                let mut in_proof = false;
                let mut j = i + 1;
                while j < lines.len() {
                    let nl = lines[j];
                    let nlt = nl.trim();
                    if nlt == "QED" || nlt.starts_with("QED ") {
                        break;
                    }
                    if nlt == "Proof" || nlt.starts_with("Proof ") {
                        in_proof = true;
                        let after = nlt.strip_prefix("Proof").unwrap_or("");
                        if !after.is_empty() {
                            proof_buf.push(' ');
                            proof_buf.push_str(after.trim());
                        }
                    } else if in_proof {
                        proof_buf.push(' ');
                        proof_buf.push_str(nlt);
                    } else {
                        stmt.push(' ');
                        stmt.push_str(nlt);
                    }
                    j += 1;
                }
                let mut hz = AxiomUsage::default();
                let from = line_no.saturating_sub(1);
                let to = (j + 1).min(raw_lines.len());
                flag_hazards(&raw_lines[from..to].join("\n"), &mut hz);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Function,
                    statement: normalise_ws(&stmt),
                    proof: if proof_buf.trim().is_empty() {
                        None
                    } else {
                        Some(normalise_ws(&proof_buf))
                    },
                    line: line_no,
                    axiom_usage: hz,
                });
                i = j + 1;
                continue;
            }
        }

        // (c) `Definition NAME:`, `Inductive NAME:`, `Datatype:`
        let mut consumed_c = false;
        for (kw, kind) in [
            ("Definition ", DeclKind::Function),
            ("Inductive ", DeclKind::Function),
            ("Datatype:", DeclKind::Data),
        ] {
            let starts = t.starts_with(kw);
            if starts && column_of(line) == 0 {
                let (name, head_body) = if kw == "Datatype:" {
                    // `Datatype:` is anonymous in the same sense as
                    // `type t = …` in SML — we synthesise a name from
                    // the first identifier in the body.
                    let after = t.strip_prefix("Datatype:").unwrap_or("").trim();
                    let n = after
                        .chars()
                        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                        .collect::<String>();
                    (
                        if n.is_empty() {
                            format!("datatype_L{line_no}")
                        } else {
                            n
                        },
                        after.to_string(),
                    )
                } else if let Some((n, h)) = split_named_block(t, kw.trim_end_matches(' ')) {
                    (n, h)
                } else {
                    continue;
                };
                let mut body = head_body.trim().to_string();
                let mut j = i + 1;
                while j < lines.len() {
                    let nl = lines[j];
                    let nlt = nl.trim();
                    if nlt == "End" || nlt.starts_with("End ") {
                        break;
                    }
                    body.push(' ');
                    body.push_str(nlt);
                    j += 1;
                }
                let mut hz = AxiomUsage::default();
                let from = line_no.saturating_sub(1);
                let to = (j + 1).min(raw_lines.len());
                flag_hazards(&raw_lines[from..to].join("\n"), &mut hz);
                pf.decls.push(DraftDecl {
                    name,
                    kind,
                    statement: normalise_ws(&body),
                    proof: None,
                    line: line_no,
                    axiom_usage: hz,
                });
                i = j + 1;
                consumed_c = true;
                break;
            }
        }
        if consumed_c {
            continue;
        }

        // (a) `val NAME = …;` family.
        if column_of(line) == 0 && (t.starts_with("val ") || t.starts_with("and ")) {
            if let Some((name, rhs)) = split_val(t) {
                // Accumulate until terminating `;` (top-level SML).
                let mut body = rhs;
                let mut j = i;
                while !body.contains(';') && j + 1 < lines.len() {
                    j += 1;
                    body.push(' ');
                    body.push_str(lines[j].trim());
                }
                // `val _ = new_theory …` / `val _ = export_theory ()`
                // are bookkeeping, not corpus entries.
                if name == "_" {
                    i = j + 1;
                    continue;
                }
                let kind = classify_rhs(&body);
                let (statement, proof) = split_statement_proof(&body, kind);
                let mut hz = AxiomUsage::default();
                if matches!(kind, DeclKind::Postulate) {
                    hz.postulate = true;
                }
                let from = line_no.saturating_sub(1);
                let to = (j + 1).min(raw_lines.len());
                flag_hazards(&raw_lines[from..to].join("\n"), &mut hz);
                pf.decls.push(DraftDecl {
                    name,
                    kind,
                    statement: normalise_ws(&statement),
                    proof: proof.map(|s| normalise_ws(&s)),
                    line: line_no,
                    axiom_usage: hz,
                });
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }

    pf
}

fn column_of(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

/// Parse `KEYWORD NAME[: REST]` (or `KEYWORD NAME REST`). Returns
/// `(NAME, REST-after-name)`. `:` is preferred as the separator (HOL4's
/// modern Theorem syntax), but bare space is accepted too.
fn split_named_block(line: &str, keyword: &str) -> Option<(String, String)> {
    let after = line.strip_prefix(keyword)?.trim_start();
    let name: String = after
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
        .collect();
    if name.is_empty() {
        return None;
    }
    let tail = after[name.len()..].trim_start();
    let tail = tail.strip_prefix(':').unwrap_or(tail).trim();
    Some((name, tail.to_string()))
}

/// Parse `val NAME = REST` or `and NAME = REST`. The `val _ = …`
/// bookkeeping idiom is preserved as `_`.
fn split_val(line: &str) -> Option<(String, String)> {
    let after = line
        .strip_prefix("val ")
        .or_else(|| line.strip_prefix("and "))?;
    let eq = after.find('=')?;
    let lhs = after[..eq].trim();
    let rhs = after[eq + 1..].trim().to_string();
    let name = if lhs == "_" {
        "_".to_string()
    } else {
        lhs.chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
            .collect::<String>()
    };
    if name.is_empty() {
        return None;
    }
    Some((name, rhs))
}

fn classify_rhs(rhs: &str) -> DeclKind {
    let t = rhs.trim_start();
    if t.starts_with("new_axiom") {
        return DeclKind::Postulate;
    }
    if t.starts_with("new_type") {
        return DeclKind::Data;
    }
    DeclKind::Function
}

/// For `store_thm("NAME", `STMT`, TAC)` we want STMT as statement and
/// TAC as proof. HOL4 uses backquotes to delimit terms, like HOL Light.
fn split_statement_proof(rhs: &str, kind: DeclKind) -> (String, Option<String>) {
    if matches!(kind, DeclKind::Data) {
        return (rhs.trim().to_string(), None);
    }
    if let Some(bt1) = rhs.find('`') {
        if let Some(bt2_rel) = rhs[bt1 + 1..].find('`') {
            let stmt = rhs[bt1 + 1..bt1 + 1 + bt2_rel].trim().to_string();
            let tail = rhs[bt1 + 1 + bt2_rel + 1..].trim();
            let tail = tail.trim_start_matches(',').trim();
            let tail = tail.trim_end_matches(';').trim_end_matches(')').trim();
            if matches!(kind, DeclKind::Postulate) {
                return (stmt, None);
            }
            if tail.is_empty() {
                return (stmt, None);
            }
            return (stmt, Some(tail.to_string()));
        }
    }
    (rhs.trim().to_string(), None)
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '`' | '=' | ':' | '|'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("new_axiom") {
        hz.postulate = true;
        hz.other.push("new_axiom".to_string());
    }
    if text.contains("mk_thm") {
        hz.trustme = true;
        hz.other.push("mk_thm".to_string());
    }
    // HOL4's `cheat` and `CHEAT_TAC` close any goal — admit-grade.
    if text.contains("cheat") || text.contains("CHEAT_TAC") {
        hz.admitted = true;
        hz.other.push("cheat".to_string());
    }
    // Doesn't reduce in the solver — flag for review but not as an
    // axiom-class hazard.
    if text.contains("Q.MATCH_ABBREV_TAC") {
        hz.other.push("Q.MATCH_ABBREV_TAC".to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_store_thm_and_imports() {
        let src = "open boolTheory arithmeticTheory;\n\
                   val _ = new_theory \"FOO\";\n\
                   val ADD_SYM = store_thm(\"ADD_SYM\",\n\
                     `!m n. m + n = n + m`,\n\
                     METIS_TAC[ADD_COMM]);\n\
                   val _ = export_theory();\n";
        let pf = parse_hol4_file(src);
        assert_eq!(pf.theory_name.as_deref(), Some("FOO"));
        assert!(pf.imports.iter().any(|i| i == "boolTheory"));
        assert!(pf.imports.iter().any(|i| i == "arithmeticTheory"));
        let names: Vec<&str> = pf.decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"ADD_SYM"), "missing ADD_SYM in {names:?}");
        let d = pf.decls.iter().find(|d| d.name == "ADD_SYM").unwrap();
        assert_eq!(d.kind, DeclKind::Function);
        assert!(d.statement.contains("m + n"));
        assert!(d.proof.as_deref().unwrap_or("").contains("METIS_TAC"));
    }

    #[test]
    fn detects_cheat_hazard() {
        let src = "val _ = new_theory \"BAD\";\n\
                   val FAKE = store_thm(\"FAKE\",\n\
                     `!x. F`,\n\
                     cheat);\n";
        let pf = parse_hol4_file(src);
        let d = pf.decls.iter().find(|d| d.name == "FAKE").unwrap();
        assert!(d.axiom_usage.admitted, "cheat must flag admitted");
        assert!(d.axiom_usage.other.iter().any(|s| s == "cheat"));
    }

    #[test]
    fn detects_new_axiom() {
        let src = "val EM = new_axiom(\"EM\", `!p. p \\/ ~p`);\n";
        let pf = parse_hol4_file(src);
        let d = pf.decls.iter().find(|d| d.name == "EM").unwrap();
        assert_eq!(d.kind, DeclKind::Postulate);
        assert!(d.axiom_usage.postulate);
    }

    #[test]
    fn parses_modern_theorem_qed() {
        let src = "val _ = new_theory \"T\";\n\
                   Theorem TRIV:\n\
                     !x. x = x\n\
                   Proof\n\
                     REWRITE_TAC[]\n\
                   QED\n";
        let pf = parse_hol4_file(src);
        let d = pf.decls.iter().find(|d| d.name == "TRIV").unwrap();
        assert_eq!(d.kind, DeclKind::Function);
        assert!(d.statement.contains("x = x"));
        assert!(d.proof.as_deref().unwrap_or("").contains("REWRITE_TAC"));
    }
}
