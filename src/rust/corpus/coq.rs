// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Coq adapter for the corpus indexer — Step 2 of the N-dim plan.
//!
//! Walks a project root, finds every `*.v` file (excluding `_build/`,
//! `target/`, build artefact dirs), and extracts a structural index.
//!
//! Coq's structure is more disciplined than Agda's:
//!
//! - Comments: `(* … *)` nestable, no line-comment syntax.
//! - Statements terminate with `.` at column 0 (effectively).
//! - Top-level keywords: `Theorem`, `Lemma`, `Fact`, `Corollary`,
//!   `Proposition`, `Remark`, `Definition`, `Fixpoint`, `CoFixpoint`,
//!   `Inductive`, `CoInductive`, `Record`, `Axiom`, `Variable`,
//!   `Parameter`, `Hypothesis`, `Module`, `Section`, `Require`,
//!   `Import`, `Export`.
//! - Proof body: `Proof.` … `Qed.` / `Defined.` / `Admitted.`.
//!
//! The parser splits the source into top-level statements at sentence
//! terminators (`.` followed by whitespace/EOF outside comments and
//! strings), then classifies each by its leading keyword.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_v(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "coq".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;
        let parsed = parse_coq_file(&raw, &rel);

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

    // Pass 2: dependency resolution — same textual approach as agda.rs.
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

fn walk_v(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir)
        .with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name_s = entry.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if matches!(
                name_s.as_str(),
                "_build" | ".git" | "node_modules" | "target" | ".cache" | "build"
            ) {
                continue;
            }
            walk_v(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("v") {
            out.push(p);
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

/// Strip Coq comments `(* … *)` (nestable). Replace each comment
/// byte with a space, preserving newlines so reported line numbers
/// align with the original file.
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

/// Build a list of `(start_byte, end_byte_exclusive, line_no)` for
/// each top-level statement. Statements are split at `.` followed by
/// whitespace or EOF, but only when not inside `(* *)` (already
/// stripped) or string literals `"…"`.
fn statement_ranges(stripped: &str) -> Vec<(usize, usize, usize)> {
    let bytes = stripped.as_bytes();
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut start_line = 1usize;
    let mut current_line = 1usize;
    let mut in_string = false;
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'\n' {
            current_line += 1;
        }
        if c == b'"' {
            in_string = !in_string;
            i += 1;
            continue;
        }
        if !in_string && c == b'.' {
            let next_is_ws_or_eof = i + 1 >= bytes.len()
                || bytes[i + 1] == b' '
                || bytes[i + 1] == b'\t'
                || bytes[i + 1] == b'\n'
                || bytes[i + 1] == b'\r';
            // Avoid splitting on dotted module access (`Foo.bar`):
            // a dot preceded by an identifier char and followed by
            // an identifier char is qualifier syntax, not terminator.
            // We've already required ws/eof on the right, so the only
            // ambiguity is end-of-line `Foo.\n` after a qualifier —
            // those are genuine terminators in Coq's grammar.
            if next_is_ws_or_eof {
                let end = i + 1;
                let slice = stripped[start..end].trim();
                if !slice.is_empty() {
                    out.push((start, end, start_line));
                }
                start = end;
                start_line = current_line;
                i += 1;
                continue;
            }
        }
        i += 1;
    }
    if start < bytes.len() {
        let slice = stripped[start..].trim();
        if !slice.is_empty() {
            out.push((start, bytes.len(), start_line));
        }
    }
    out
}

fn parse_coq_file(raw: &str, _rel: &Path) -> ParsedFile {
    let stripped = strip_comments(raw);
    let ranges = statement_ranges(&stripped);
    let mut pf = ParsedFile::default();

    let mut i = 0usize;
    while i < ranges.len() {
        let (s, e, line) = ranges[i];
        let stmt_raw = &stripped[s..e];
        let stmt = stmt_raw.trim();
        let stmt_norm = normalise_ws(stmt);

        // `Module Foo.`
        if let Some(name) = strip_module_open(&stmt_norm) {
            if pf.module_name.is_none() {
                pf.module_name = Some(name);
            }
            i += 1;
            continue;
        }

        // `Require Import M.` / `Require Export M.` / `Import M.`
        if let Some(modules) = strip_imports(&stmt_norm) {
            for m in modules {
                if !pf.imports.contains(&m) {
                    pf.imports.push(m);
                }
            }
            i += 1;
            continue;
        }

        // Theorem / Lemma / Fact / Corollary / Proposition / Remark.
        // These are followed by Proof. ... Qed./Defined./Admitted.
        if let Some((name, ty)) = strip_theorem(&stmt_norm) {
            // Look ahead for the proof block (a sequence of statements
            // until `Qed.` / `Defined.` / `Admitted.`).
            let mut body = String::new();
            let mut admitted = false;
            let mut j = i + 1;
            while j < ranges.len() {
                let (ps, pe, _) = ranges[j];
                let p = stripped[ps..pe].trim().to_string();
                let p_low = p.trim().trim_end_matches('.').trim();
                if !body.is_empty() {
                    body.push(' ');
                }
                body.push_str(&p);
                if p_low == "Qed" || p_low == "Defined" {
                    j += 1;
                    break;
                }
                if p_low == "Admitted" {
                    admitted = true;
                    j += 1;
                    break;
                }
                j += 1;
            }
            let mut hz = AxiomUsage::default();
            if admitted {
                hz.admitted = true;
            }
            flag_hazards(&body, &mut hz);
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Function,
                statement: ty,
                proof: if body.is_empty() { None } else { Some(body) },
                line,
                axiom_usage: hz,
            });
            i = j;
            continue;
        }

        // Definition / Fixpoint / CoFixpoint.
        if let Some((name, ty, body)) = strip_definition(&stmt_norm) {
            let mut hz = AxiomUsage::default();
            if let Some(b) = &body {
                flag_hazards(b, &mut hz);
            }
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Function,
                statement: ty,
                proof: body,
                line,
                axiom_usage: hz,
            });
            i += 1;
            continue;
        }

        // Inductive / CoInductive.
        if let Some((name, ty)) = strip_inductive(&stmt_norm) {
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Data,
                statement: ty,
                proof: None,
                line,
                axiom_usage: AxiomUsage::default(),
            });
            i += 1;
            continue;
        }

        // Record.
        if let Some((name, ty)) = strip_record(&stmt_norm) {
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Record,
                statement: ty,
                proof: None,
                line,
                axiom_usage: AxiomUsage::default(),
            });
            i += 1;
            continue;
        }

        // Axiom / Variable / Parameter / Hypothesis: postulates.
        if let Some((name, ty)) = strip_axiom(&stmt_norm) {
            let hz = AxiomUsage {
                postulate: true,
                ..Default::default()
            };
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Postulate,
                statement: ty,
                proof: None,
                line,
                axiom_usage: hz,
            });
            i += 1;
            continue;
        }

        i += 1;
    }

    pf
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn strip_module_open(s: &str) -> Option<String> {
    let s = s.trim_end_matches('.').trim();
    let rest = s.strip_prefix("Module ")?;
    // `Module Foo.` — name is the first word.
    let name = rest
        .split_whitespace()
        .next()?
        .trim_matches(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
        .to_string();
    if name.is_empty() {
        return None;
    }
    Some(name)
}

fn strip_imports(s: &str) -> Option<Vec<String>> {
    let s = s.trim_end_matches('.').trim();
    let rest = s
        .strip_prefix("Require Import ")
        .or_else(|| s.strip_prefix("Require Export "))
        .or_else(|| s.strip_prefix("Require "))
        .or_else(|| s.strip_prefix("Import "))
        .or_else(|| s.strip_prefix("Export "))?;
    Some(
        rest.split_whitespace()
            .filter(|t| !t.is_empty() && t.chars().next().map(|c| c != '(').unwrap_or(false))
            .map(|t| t.trim_end_matches(',').to_string())
            .filter(|t| !t.is_empty())
            .collect(),
    )
}

const THEOREM_KEYWORDS: &[&str] = &[
    "Theorem ",
    "Lemma ",
    "Fact ",
    "Corollary ",
    "Proposition ",
    "Remark ",
    "Goal ",
    "Example ",
];

fn strip_theorem(s: &str) -> Option<(String, String)> {
    let s = s.trim_end_matches('.').trim();
    for kw in THEOREM_KEYWORDS {
        if let Some(rest) = s.strip_prefix(*kw) {
            return split_name_colon_type(rest);
        }
    }
    None
}

fn strip_definition(s: &str) -> Option<(String, String, Option<String>)> {
    let s = s.trim_end_matches('.').trim();
    let rest = s
        .strip_prefix("Definition ")
        .or_else(|| s.strip_prefix("Fixpoint "))
        .or_else(|| s.strip_prefix("CoFixpoint "))
        .or_else(|| s.strip_prefix("Function "))?;
    // `name [args] [: ty] := body` or `name [args] : ty.` (if axiomatic).
    let assign = rest.find(":=");
    match assign {
        Some(eq) => {
            let head = &rest[..eq];
            let body = rest[eq + 2..].trim().to_string();
            let (name, ty) = split_name_optional_colon_type(head);
            Some((name, ty, Some(body)))
        }
        None => {
            let (name, ty) = split_name_optional_colon_type(rest);
            Some((name, ty, None))
        }
    }
}

fn strip_inductive(s: &str) -> Option<(String, String)> {
    let s = s.trim_end_matches('.').trim();
    let rest = s
        .strip_prefix("Inductive ")
        .or_else(|| s.strip_prefix("CoInductive ")) ?;
    let name: String = rest
        .chars()
        .take_while(|c| !c.is_whitespace() && *c != ':' && *c != '(')
        .collect();
    if name.is_empty() {
        return None;
    }
    Some((name, normalise_ws(rest)))
}

fn strip_record(s: &str) -> Option<(String, String)> {
    let s = s.trim_end_matches('.').trim();
    let rest = s.strip_prefix("Record ").or_else(|| s.strip_prefix("Structure "))?;
    let name: String = rest
        .chars()
        .take_while(|c| !c.is_whitespace() && *c != ':' && *c != '(' && *c != '{')
        .collect();
    if name.is_empty() {
        return None;
    }
    Some((name, normalise_ws(rest)))
}

fn strip_axiom(s: &str) -> Option<(String, String)> {
    let s = s.trim_end_matches('.').trim();
    let rest = s
        .strip_prefix("Axiom ")
        .or_else(|| s.strip_prefix("Variable ")) // common in Sections
        .or_else(|| s.strip_prefix("Parameter "))
        .or_else(|| s.strip_prefix("Hypothesis "))
        .or_else(|| s.strip_prefix("Conjecture "))?;
    split_name_colon_type(rest)
}

/// `name : type` — required colon. Returns None if the colon isn't
/// present or the head is empty.
fn split_name_colon_type(s: &str) -> Option<(String, String)> {
    let colon = top_level_colon(s)?;
    let lhs = s[..colon].trim();
    let rhs = s[colon + 1..].trim();
    let name = lhs.split_whitespace().next()?.to_string();
    if name.is_empty() {
        return None;
    }
    Some((name, normalise_ws(rhs)))
}

/// `name [args] [: type]` — colon optional; if absent, ty is empty.
fn split_name_optional_colon_type(s: &str) -> (String, String) {
    let s = s.trim();
    let name = s
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_string();
    let rest = if let Some(colon) = top_level_colon(s) {
        normalise_ws(s[colon + 1..].trim())
    } else {
        String::new()
    };
    (name, rest)
}

fn top_level_colon(s: &str) -> Option<usize> {
    let mut depth_paren: i32 = 0;
    let mut depth_bracket: i32 = 0;
    let mut depth_brace: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            '{' => depth_brace += 1,
            '}' => depth_brace -= 1,
            ':' if depth_paren == 0 && depth_bracket == 0 && depth_brace == 0 => {
                // Skip `::` (Coq has it for cons in some scopes).
                let mut next_idx = i + ':'.len_utf8();
                if next_idx < s.len() && s[next_idx..].starts_with(':') {
                    continue;
                }
                // Skip `:=`.
                if next_idx < s.len() && s[next_idx..].starts_with('=') {
                    continue;
                }
                let _ = next_idx;
                return Some(i);
            }
            _ => {}
        }
    }
    None
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '=' | ':' | '.' | '"'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("Admitted") {
        hz.admitted = true;
    }
    if text.contains("admit") {
        // `admit` as a tactic — flag conservatively. Will be a false
        // positive on `admitted` substrings; the structural detector
        // below catches the formal `Admitted.` already.
        hz.admitted = true;
    }
    if text.contains("Axiom ") {
        hz.postulate = true;
    }
    let _ = HashMap::<String, String>::new(); // silence unused-import warning if any
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_theorem_with_proof() {
        let src = "Theorem identity : forall A : Prop, A -> A.\n\
                   Proof.\n  intros A H. exact H.\nQed.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "identity");
        assert_eq!(pf.decls[0].kind, DeclKind::Function);
        assert!(pf.decls[0].statement.contains("forall A"));
        assert!(pf.decls[0].proof.as_deref().unwrap().contains("intros"));
        assert!(!pf.decls[0].axiom_usage.any());
    }

    #[test]
    fn flags_admitted() {
        let src = "Theorem todo : True.\nProof.\nAdmitted.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0].axiom_usage.admitted);
    }

    #[test]
    fn parses_definition_with_body() {
        let src = "Definition double (n : nat) : nat := n + n.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "double");
        assert!(pf.decls[0].proof.as_deref().unwrap().contains("n + n"));
    }

    #[test]
    fn parses_inductive() {
        let src = "Inductive nat : Set := O : nat | S : nat -> nat.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "nat");
        assert_eq!(pf.decls[0].kind, DeclKind::Data);
    }

    #[test]
    fn parses_axiom_as_postulate() {
        let src = "Axiom classical : forall P, P \\/ ~ P.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].kind, DeclKind::Postulate);
        assert!(pf.decls[0].axiom_usage.postulate);
    }

    #[test]
    fn handles_nested_comments() {
        let src = "(* outer (* inner *) still outer *) Theorem t : True. Proof. trivial. Qed.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "t");
    }

    #[test]
    fn parses_module_and_imports() {
        let src = "Require Import Coq.Lists.List.\nImport ListNotations.\nModule M.\nDefinition x : nat := 0.\nEnd M.\n";
        let pf = parse_coq_file(src, Path::new("test.v"));
        assert!(pf.imports.iter().any(|m| m == "Coq.Lists.List"));
        assert!(pf.imports.iter().any(|m| m == "ListNotations"));
        assert_eq!(pf.module_name.as_deref(), Some("M"));
        assert!(pf.decls.iter().any(|d| d.name == "x"));
    }
}
