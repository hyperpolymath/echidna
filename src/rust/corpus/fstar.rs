// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! F* adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.fst` (implementation) and
//! `*.fsti` (interface) file, and extracts a structural index in the
//! same shape as `agda.rs` / `coq.rs`. Heuristic, not authoritative:
//!
//! - Strips line (`//`), docstring (`///`), and nestable block
//!   (`(* … *)`) comments. Newlines are preserved so line numbers in
//!   `DraftDecl::line` track the original source.
//! - Recognises `module M`, `module M = N`, and `open M` / `include M`.
//! - Recognises top-level decl introducers at column 0:
//!   `let` / `let rec` (functions, lemmas), `val` (declarations),
//!   `type` / `inductive` (datatypes), `assume val` / `assume Ax: …` /
//!   `assume new type` (postulates / axioms — HAZARD), `effect` /
//!   `total` modifiers (kept as part of the statement).
//! - Detects banned-pattern axiom usage (`assume`, `admit()`, `magic()`,
//!   `Obj.magic`, unsafe `coerce`, `lemma` with `admit`).
//!
//! Output is structural: it answers "what decls live in this project,
//! who uses whom, and which ones touch a hazard?" — enough for
//! curriculum scaffolding and SA design search.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `target`, `_build`, `output`,
/// `_cache`, `node_modules` regardless of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_fstar(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "fstar".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_fstar_file(&raw);

        let module_idx = corpus.modules.len();
        let module_entry = ModuleEntry {
            name: parsed.module_name.clone().unwrap_or_else(|| {
                rel.with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join(".")
            }),
            path: rel,
            options: parsed.options,
            imports: parsed.imports,
            entries: Vec::new(),
        };
        corpus.modules.push(module_entry);

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

    // Pass 2: textual dependency resolution.
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

fn walk_fstar(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "_build" | "output" | "_cache" | "node_modules"
            ) {
                continue;
            }
            walk_fstar(&p, out)?;
        } else {
            match p.extension().and_then(|s| s.to_str()) {
                Some("fst") | Some("fsti") => out.push(p),
                _ => {},
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    module_name: Option<String>,
    options: Vec<String>,
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

/// Strip F* comments, preserving newlines:
///
/// - Block comments `(* … *)` nest (F* convention).
/// - Line comments `// …` (since F* 0.9) and docstring `/// …` are
///   stripped.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut block_depth: usize = 0;
    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b')' {
                block_depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                block_depth += 1;
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
            block_depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_fstar_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();

    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    // Module name: first `module X.Y` or `module X = …`.
    for line in &lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("module ") {
            // Stop at whitespace or `=` so both forms work.
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                .collect();
            if !name.is_empty() {
                pf.module_name = Some(name);
                break;
            }
        }
    }

    // Imports: `open M` / `include M`.
    for line in &lines {
        let t = line.trim_start();
        let candidate = t
            .strip_prefix("open ")
            .or_else(|| t.strip_prefix("include "));
        if let Some(rest) = candidate {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                .collect();
            if !name.is_empty() && !pf.imports.contains(&name) {
                pf.imports.push(name);
            }
        }
    }

    // Top-level decls. F* lines we recognise (all at column 0):
    //   let NAME …                       -> Function
    //   let rec NAME …                   -> Function
    //   val NAME : ty                    -> Function (signature only)
    //   type NAME …                      -> Data
    //   inductive NAME …                 -> Data
    //   assume val NAME : ty             -> Postulate (HAZARD)
    //   assume new type NAME …           -> Postulate (HAZARD)
    //   assume Ax_NAME : ty              -> Postulate (HAZARD)
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let col = column_of(line);
        if col != 0 {
            i += 1;
            continue;
        }
        let trimmed = line.trim_start();

        // assume new type N
        if let Some(rest) = trimmed.strip_prefix("assume new type ") {
            if let Some(name) = leading_ident(rest) {
                let (stmt, next) = collect_continuation(&lines, i);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Postulate,
                    statement: normalise_ws(&stmt),
                    proof: None,
                    line: line_no,
                    axiom_usage: AxiomUsage {
                        postulate: true,
                        ..Default::default()
                    },
                });
                i = next;
                continue;
            }
        }
        // assume val N : ty
        if let Some(rest) = trimmed.strip_prefix("assume val ") {
            if let Some(name) = leading_ident(rest) {
                let (stmt, next) = collect_continuation(&lines, i);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Postulate,
                    statement: normalise_ws(&stmt),
                    proof: None,
                    line: line_no,
                    axiom_usage: AxiomUsage {
                        postulate: true,
                        ..Default::default()
                    },
                });
                i = next;
                continue;
            }
        }
        // assume Ax : ty  /  assume N : ty
        if let Some(rest) = trimmed.strip_prefix("assume ") {
            if let Some(name) = leading_ident(rest) {
                let (stmt, next) = collect_continuation(&lines, i);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Postulate,
                    statement: normalise_ws(&stmt),
                    proof: None,
                    line: line_no,
                    axiom_usage: AxiomUsage {
                        postulate: true,
                        ..Default::default()
                    },
                });
                i = next;
                continue;
            }
        }

        // type N …   /   inductive N …
        let type_match = trimmed
            .strip_prefix("type ")
            .or_else(|| trimmed.strip_prefix("inductive "));
        if let Some(rest) = type_match {
            if let Some(name) = leading_ident(rest) {
                let (stmt, next) = collect_continuation(&lines, i);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Data,
                    statement: normalise_ws(&stmt),
                    proof: None,
                    line: line_no,
                    axiom_usage: AxiomUsage::default(),
                });
                i = next;
                continue;
            }
        }

        // val NAME : ty
        if let Some(rest) = trimmed.strip_prefix("val ") {
            if let Some(name) = leading_ident(rest) {
                let (stmt, next) = collect_continuation(&lines, i);
                let mut hz = AxiomUsage::default();
                let scan = raw_lines[i.min(raw_lines.len())..next.min(raw_lines.len())].join("\n");
                flag_hazards(&scan, &mut hz);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Function,
                    statement: normalise_ws(&stmt),
                    proof: None,
                    line: line_no,
                    axiom_usage: hz,
                });
                i = next;
                continue;
            }
        }

        // let rec NAME … = body
        // let NAME …     = body
        let after_let = trimmed
            .strip_prefix("let rec ")
            .map(|s| (s, true))
            .or_else(|| trimmed.strip_prefix("let ").map(|s| (s, false)));
        if let Some((rest, _rec)) = after_let {
            if let Some(name) = leading_ident(rest) {
                let (full, next) = collect_continuation(&lines, i);
                // Split statement vs proof at the first top-level `=`.
                let (stmt, proof) = split_let_body(&full);
                let mut hz = AxiomUsage::default();
                let scan = raw_lines[i.min(raw_lines.len())..next.min(raw_lines.len())].join("\n");
                flag_hazards(&scan, &mut hz);
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Function,
                    statement: normalise_ws(&stmt),
                    proof: proof.map(|p| normalise_ws(&p)),
                    line: line_no,
                    axiom_usage: hz,
                });
                i = next;
                continue;
            }
        }

        i += 1;
    }

    pf
}

/// Column (chars) of the first non-whitespace character.
fn column_of(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

/// First identifier-looking token of `rest`.
fn leading_ident(rest: &str) -> Option<String> {
    let s = rest.trim_start();
    let name: String = s
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
        .collect();
    if name.is_empty() || !s.starts_with(|c: char| c.is_alphabetic() || c == '_') {
        None
    } else {
        Some(name)
    }
}

/// Collect this column-0 line plus indented continuation lines.
/// Returns `(joined, next_i)` where `next_i` is the first
/// non-continuation index.
fn collect_continuation(lines: &[&str], start: usize) -> (String, usize) {
    let mut out = String::from(lines[start].trim());
    let mut j = start + 1;
    while j < lines.len() {
        let l = lines[j];
        if l.trim().is_empty() {
            j += 1;
            break;
        }
        if column_of(l) == 0 {
            break;
        }
        out.push(' ');
        out.push_str(l.trim());
        j += 1;
    }
    (out, j)
}

/// Split a `let …` body at the first top-level `=` (i.e. not inside
/// parens or square brackets and not `==` / `<=` / `>=` / `=>`).
///
/// Returns `(signature_or_lhs, body_after_eq)`.
fn split_let_body(s: &str) -> (String, Option<String>) {
    let chars: Vec<char> = s.chars().collect();
    let mut depth_paren: i32 = 0;
    let mut depth_brack: i32 = 0;
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        match c {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_brack += 1,
            ']' => depth_brack -= 1,
            '=' if depth_paren == 0 && depth_brack == 0 => {
                let prev = if i > 0 { chars[i - 1] } else { ' ' };
                let next = if i + 1 < chars.len() {
                    chars[i + 1]
                } else {
                    ' '
                };
                // Reject `==`, `<=`, `>=`, `=>`, `:=`.
                if next == '=' || next == '>' {
                    i += 2;
                    continue;
                }
                if prev == '<' || prev == '>' || prev == '!' || prev == ':' || prev == '=' {
                    i += 1;
                    continue;
                }
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return (lhs.trim().to_string(), Some(rhs.trim().to_string()));
            },
            _ => {},
        }
        i += 1;
    }
    (s.trim().to_string(), None)
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Tokenise on whitespace and F* syntactic glue. F* identifiers may
/// contain `_`, `'`, alphanumerics; dotted-qualified names use `.`.
fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | ':' | '=' | '|' | '<' | '>'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("admit()") || text.contains("admit ()") || text.contains("admit_smt_queries") {
        hz.admitted = true;
    }
    if text.contains("magic()") || text.contains("Obj.magic") || text.contains("FStar.Obj.magic") {
        hz.trustme = true;
    }
    if text.contains("unsafe_coerce") || text.contains("unsafeCoerce") {
        hz.trustme = true;
    }
    // `assume` keyword inside a body is a hazard even when the decl
    // itself didn't start with it (e.g. inline `assume (p x)`).
    if text.contains(" assume ") || text.contains("\nassume ") {
        hz.other.push("assume".to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_module_let_val_type() {
        let src = "\
module Smoke\n\
\n\
val foo : nat -> nat\n\
let foo x = x + 1\n\
\n\
type color =\n\
  | Red\n\
  | Green\n\
  | Blue\n\
";
        let pf = parse_fstar_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("Smoke"));
        let names: Vec<(&str, DeclKind)> =
            pf.decls.iter().map(|d| (d.name.as_str(), d.kind)).collect();
        assert!(
            names.iter().any(|(n, k)| *n == "foo" && *k == DeclKind::Function),
            "expected foo function, got {:?}", names
        );
        assert!(
            names.iter().any(|(n, k)| *n == "color" && *k == DeclKind::Data),
            "expected color data, got {:?}", names
        );
    }

    #[test]
    fn detects_assume_and_admit_hazards() {
        let src = "\
module Bad\n\
\n\
assume val sketchy : nat -> nat\n\
\n\
assume Ax_no_lt : forall x. x >= 0\n\
\n\
let cheat (x: nat) : nat = admit ()\n\
";
        let pf = parse_fstar_file(src);
        let sketchy = pf.decls.iter().find(|d| d.name == "sketchy").expect("sketchy");
        assert_eq!(sketchy.kind, DeclKind::Postulate);
        assert!(sketchy.axiom_usage.postulate);

        let ax = pf.decls.iter().find(|d| d.name == "Ax_no_lt").expect("Ax_no_lt");
        assert_eq!(ax.kind, DeclKind::Postulate);
        assert!(ax.axiom_usage.postulate);

        let cheat = pf.decls.iter().find(|d| d.name == "cheat").expect("cheat");
        assert!(cheat.axiom_usage.admitted, "admit() hazard not flagged");
    }

    #[test]
    fn captures_imports_and_let_body() {
        let src = "\
module Lib\n\
\n\
open FStar.List\n\
include FStar.Tactics\n\
\n\
let id (x: 'a) : 'a = x\n\
";
        let pf = parse_fstar_file(src);
        assert!(pf.imports.iter().any(|m| m == "FStar.List"));
        assert!(pf.imports.iter().any(|m| m == "FStar.Tactics"));
        let id_d = pf.decls.iter().find(|d| d.name == "id").expect("id");
        assert!(id_d.proof.is_some(), "let body not captured");
    }
}
