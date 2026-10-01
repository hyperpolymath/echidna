// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! HOL Light adapter for the corpus indexer.
//!
//! HOL Light is an OCaml-hosted LCF-style prover. There is no first-
//! class file-level "theory" construct (cf. HOL4's `Theory.sml` or
//! Coq's `Module`): a HOL Light development is a chain of `.ml` files
//! that load each other via `loadt "foo.ml";;` or `needs "foo.ml";;`,
//! with theorems built up as OCaml `let`-bindings whose right-hand side
//! is a call into the HOL Light kernel (`prove`, `new_definition`,
//! `new_axiom`, …).
//!
//! The walker discriminates HOL Light files from generic OCaml by
//! looking for at least one such kernel call; non-HOL-Light `.ml`
//! files are quietly skipped so this adapter can be pointed at a
//! mixed tree.
//!
//! ## Extraction shape
//!
//! For each surviving file we lift:
//!   * the file's logical "module" name (derived from the file path),
//!   * its `loadt`/`needs` import edges,
//!   * one `CorpusEntry` per `let NAME = <kernel-call> …;;` binding,
//!     classified by `DeclKind` based on the kernel call,
//!   * hazard flags for `new_axiom`, `mk_thm`, free `ASSUME`,
//!     `failwith "not yet"`, and `(* TODO *)`.
//!
//! The textual scan is intentionally heuristic: HOL Light's surface
//! syntax is OCaml plus quoted HOL terms, and a full OCaml parser is
//! way more machinery than this corpus-indexer needs.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `_build`, `target`, `_opam`, and
/// `dune-project` (the last as a file-or-dir guard); only `.ml` files
/// that look like HOL Light scripts are kept.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_ml(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "hol_light".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        if !looks_like_hol_light(&raw) {
            continue;
        }
        let parsed = parse_hol_light_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");
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

fn walk_ml(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "_build" | "target" | "_opam" | ".cache" | "node_modules"
            ) {
                continue;
            }
            walk_ml(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("ml")
            && name_s.as_ref() != "dune-project"
        {
            out.push(p);
        }
    }
    Ok(())
}

/// Coarse HOL Light sniff. Returns true iff the file mentions any of
/// the HOL Light kernel entry points or characteristic tactic suffixes.
/// Used to keep generic OCaml libraries out of the corpus when this
/// adapter is pointed at a mixed tree (e.g. `dune` build).
fn looks_like_hol_light(src: &str) -> bool {
    const NEEDLES: &[&str] = &[
        "prove(",
        "prove (",
        "prove_by_refinement",
        "new_definition",
        "new_recursive_definition",
        "new_inductive_definition",
        "new_axiom",
        "new_specification",
        "new_type_definition",
        "REWRITE_TAC",
        "MESON_TAC",
        "MATCH_MP_TAC",
        "ARITH_TAC",
        "loadt \"",
        "needs \"",
    ];
    NEEDLES.iter().any(|n| src.contains(n))
}

#[derive(Debug, Default)]
struct ParsedFile {
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

/// Strip OCaml block comments `(* … *)` (nestable), preserving line
/// counts so reported line numbers match the original source. There is
/// no line-comment syntax in OCaml.
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

fn parse_hol_light_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();
    let mut pf = ParsedFile::default();

    // Imports: `loadt "X.ml";;` and `needs "X.ml";;` on any line.
    for line in &lines {
        for prefix in ["loadt", "needs"] {
            if let Some(idx) = line.find(prefix) {
                let rest = &line[idx + prefix.len()..];
                if let Some(start) = rest.find('"') {
                    if let Some(end_rel) = rest[start + 1..].find('"') {
                        let name = &rest[start + 1..start + 1 + end_rel];
                        if !name.is_empty() && !pf.imports.contains(&name.to_string()) {
                            pf.imports.push(name.to_string());
                        }
                    }
                }
            }
        }
    }

    // Decls: `let NAME = <kernel-call>(...)` spans, terminated by `;;`.
    //
    // We scan line by line, looking for `let NAME =` at column 0
    // (HOL Light convention), then accumulate following lines until
    // we hit a line containing `;;`.
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        // Top-level `let NAME = …` (possibly preceded by `and`).
        let stripped_lhs = line.trim_start();
        let is_top_let = column_of(line) == 0
            && (stripped_lhs.starts_with("let ") || stripped_lhs.starts_with("and "));
        if is_top_let {
            if let Some((name, rhs)) = split_let(stripped_lhs) {
                // Accumulate lines until `;;` (HOL Light statement
                // terminator) or EOF.
                let mut body = rhs;
                let mut j = i;
                while !body.contains(";;") && j + 1 < lines.len() {
                    j += 1;
                    body.push(' ');
                    body.push_str(lines[j].trim());
                }
                let kind = classify_rhs(&body);
                let (statement, proof) = split_statement_proof(&body, kind);
                let mut hz = AxiomUsage::default();
                if matches!(kind, DeclKind::Postulate) {
                    hz.postulate = true;
                }
                let from = line_no.saturating_sub(1);
                let to = (j + 1).min(raw_lines.len());
                let scan_text = raw_lines[from..to].join("\n");
                flag_hazards(&scan_text, &mut hz);

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

/// Parse a `let NAME = …` (or `and NAME = …`) line, returning
/// `(NAME, rest-after-=)`. The RHS is whatever follows `=` on the
/// originating line, with no further interpretation.
fn split_let(line: &str) -> Option<(String, String)> {
    let after = line
        .strip_prefix("let ")
        .or_else(|| line.strip_prefix("and "))?;
    // OCaml lets can carry `rec`: `let rec foo = …`.
    let after = after.strip_prefix("rec ").unwrap_or(after);
    let eq = after.find('=')?;
    let lhs = after[..eq].trim();
    let rhs = after[eq + 1..].trim().to_string();
    // LHS may carry argument patterns: take the first identifier-ish
    // token.
    let name: String = lhs
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
        .collect();
    if name.is_empty() {
        return None;
    }
    Some((name, rhs))
}

/// Coarse classification of the RHS of a `let NAME = …;;` binding,
/// driven by the leading kernel call.
fn classify_rhs(rhs: &str) -> DeclKind {
    let t = rhs.trim_start();
    if t.starts_with("new_axiom") {
        return DeclKind::Postulate;
    }
    if t.starts_with("new_type") && !t.starts_with("new_type_definition") {
        // bare `new_type` declares a new type constant
        return DeclKind::Data;
    }
    if t.starts_with("new_type_definition") {
        return DeclKind::Data;
    }
    if t.starts_with("new_constant") {
        return DeclKind::Module;
    }
    // Anything else recognisable as a kernel call producing a theorem
    // or definition.
    DeclKind::Function
}

/// Best-effort split: for `prove(`STATEMENT`, TACTICS)` we want the
/// quoted-term to land in `statement` and the tactic tail in `proof`;
/// for `new_definition`/`define`/etc. we want the quoted term as
/// `statement` and `proof = None`.
///
/// HOL Light quotes terms with backticks. We use the first
/// backtick-delimited region as the statement; the rest (if any
/// substantive content remains after the comma) becomes the proof.
fn split_statement_proof(rhs: &str, kind: DeclKind) -> (String, Option<String>) {
    if matches!(kind, DeclKind::Module | DeclKind::Data) {
        return (rhs.trim().to_string(), None);
    }
    // Find the first backtick.
    if let Some(bt1) = rhs.find('`') {
        if let Some(bt2_rel) = rhs[bt1 + 1..].find('`') {
            let stmt = rhs[bt1 + 1..bt1 + 1 + bt2_rel].trim().to_string();
            let tail = rhs[bt1 + 1 + bt2_rel + 1..].trim();
            // Trim leading comma and trailing `);;` / `;;`.
            let tail = tail.trim_start_matches(',').trim();
            let tail = tail.trim_end_matches(";;").trim_end_matches(')').trim();
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

/// Tokenise on whitespace plus OCaml/HOL Light glue. HOL Light
/// identifiers are ASCII with `_` and digits; tactic combinators
/// (`THEN`, `THENL`) and arg lists are all separable on the same set.
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
        // Forging a theorem out of thin air — strictly worse than
        // postulate because it bypasses the public axiom audit trail.
        hz.trustme = true;
        hz.other.push("mk_thm".to_string());
    }
    // `ASSUME` is fine inside tactic positions (it's how MP-style
    // chaining works), but a free occurrence at the top of a `let` RHS
    // is suspect. We flag broadly and rely on human review.
    if text.contains(" ASSUME ") || text.contains("(ASSUME ") || text.contains("\nASSUME ") {
        hz.other.push("ASSUME".to_string());
    }
    if text.contains("is_axiom_call") {
        hz.other.push("is_axiom_call".to_string());
    }
    if text.contains("(* TODO *)") || text.contains("(*TODO*)") {
        hz.admitted = true;
    }
    if text.contains("failwith \"not yet\"") || text.contains("failwith \"TODO\"") {
        hz.admitted = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_prove_block() {
        let src = "needs \"lib.ml\";;\n\
                   let ADD_SYM = prove\n\
                    (`!m n. m + n = n + m`,\n\
                     MESON_TAC[ADD_AC]);;\n";
        let pf = parse_hol_light_file(src);
        assert!(pf.imports.iter().any(|i| i == "lib.ml"));
        assert_eq!(pf.decls.len(), 1);
        let d = &pf.decls[0];
        assert_eq!(d.name, "ADD_SYM");
        assert_eq!(d.kind, DeclKind::Function);
        assert!(d.statement.contains("m + n"));
        let proof = d.proof.as_deref().unwrap_or("");
        assert!(
            proof.contains("MESON_TAC"),
            "proof missing tactics: {proof}"
        );
    }

    #[test]
    fn detects_new_axiom_hazard() {
        let src = "let EXCLUDED_MIDDLE = new_axiom `!p. p \\/ ~p`;;\n";
        let pf = parse_hol_light_file(src);
        assert_eq!(pf.decls.len(), 1);
        let d = &pf.decls[0];
        assert_eq!(d.kind, DeclKind::Postulate);
        assert!(d.axiom_usage.postulate);
        assert!(d.axiom_usage.other.iter().any(|s| s == "new_axiom"));
    }

    #[test]
    fn skips_non_hol_light_ocaml() {
        // Plain OCaml file with no HOL Light kernel calls — sniff fails.
        let src = "let add x y = x + y\nlet () = print_endline (string_of_int (add 1 2))\n";
        assert!(!looks_like_hol_light(src));
    }

    #[test]
    fn classifies_new_definition() {
        let src = "let ONE = new_definition `ONE = SUC 0`;;\n";
        let pf = parse_hol_light_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].kind, DeclKind::Function);
        assert!(pf.decls[0].statement.contains("ONE = SUC 0"));
    }
}
