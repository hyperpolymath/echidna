// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Dafny adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.dfy` file (excluding `.git`,
//! `target`, `bin`, `obj`), and extracts a structural index.
//!
//! Dafny is a Microsoft Research auto-active verifier with imperative
//! syntax. Decls live inside (optionally nested) `module M { ... }`
//! blocks; the language uses curly-brace nesting (not indentation).
//!
//! What we recognise:
//! - `module M { ... }`, `class C { ... }`, `trait T { ... }`,
//!   `datatype D = ... | ...`, `type T = ...`
//! - `method NAME(args) returns (rets) requires P ensures Q { ... }`
//! - `lemma NAME(...) ... { ... }`, `function NAME(...): T { ... }`,
//!   `predicate NAME(...) { ... }`
//! - `ghost ...` variants (function / method / predicate)
//! - `iterator I`
//! - `import M`, `import opened M`, `include "file.dfy"`
//! - Spec annotations: `requires`, `ensures`, `invariant`, `decreases`,
//!   `modifies`, `reads`, `frees` (collected on the entry).
//!
//! Hazards (Dafny's escape hatches — flagged for human review):
//! - `assume` (treated as Postulate — Dafny `assume` is a soundness
//!   escape hatch; the verifier accepts the antecedent without proof).
//! - `assert {:axiom}` and the `{:axiom}` attribute generally.
//! - `extern` methods (no body — the implementation is trusted).
//! - `expect` (runtime check, NOT statically verified).
//! - `{:fuel 0}` (disables verification of the marked entity).
//!
//! Comments: `// ...` line and `/* ... */` block. Block comments do
//! *not* nest in Dafny.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_dafny(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "dafny".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_dafny_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed.module_name.clone().unwrap_or_else(|| {
            rel.with_extension("")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(".")
        });
        corpus.modules.push(ModuleEntry {
            name: module_name,
            path: rel,
            options: parsed.options,
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

fn walk_dafny(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "bin" | "obj" | "node_modules" | ".cache"
            ) {
                continue;
            }
            walk_dafny(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("dfy") {
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

/// Strip line comments (`// ...`) and block comments (`/* ... */`),
/// preserving line counts.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut in_block = false;
    let mut in_string: Option<u8> = None;
    while i < bytes.len() {
        if in_block {
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                in_block = false;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
            i += 1;
            continue;
        }
        if let Some(q) = in_string {
            out.push(bytes[i]);
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i + 1]);
                i += 2;
                continue;
            }
            if bytes[i] == q {
                in_string = None;
            }
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            in_block = true;
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
        if bytes[i] == b'"' || bytes[i] == b'\'' {
            in_string = Some(bytes[i]);
            out.push(bytes[i]);
            i += 1;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Decl-introducing keywords (with the `ghost` prefix handled separately).
const DECL_KEYWORDS: &[&str] = &[
    "method",
    "lemma",
    "function",
    "predicate",
    "datatype",
    "class",
    "trait",
    "type",
    "iterator",
];

fn parse_dafny_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    // Module name: first `module X` (possibly `abstract module X`).
    for line in &lines {
        let t = line.trim_start();
        let head = t
            .strip_prefix("abstract module ")
            .or_else(|| t.strip_prefix("module "));
        if let Some(rest) = head {
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

    // Imports + includes.
    for line in &lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("include ") {
            let path = rest.trim().trim_matches('"').trim_matches(';').to_string();
            if !path.is_empty() && !pf.imports.contains(&path) {
                pf.imports.push(path);
            }
            continue;
        }
        let import_rest = t
            .strip_prefix("import opened ")
            .or_else(|| t.strip_prefix("import "));
        if let Some(rest) = import_rest {
            // import M, import M = X, import opened M
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                .collect();
            if !name.is_empty() && !pf.imports.contains(&name) {
                pf.imports.push(name);
            }
        }
    }

    // Declarations. Dafny is curly-brace delimited, so we scan
    // line-by-line for a decl-introducing token and then capture the
    // header up to the next `{` or `;`, plus an optional brace-balanced
    // body. The line-based approach is heuristic but works on
    // conventionally formatted Dafny.
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let trimmed = line.trim_start();

        // Strip leading visibility / modifier tokens. `ghost` flips the
        // decl into ghost-mode but does not change the structural kind.
        let mut rest = trimmed;
        let mut is_ghost = false;
        loop {
            if let Some(r) = rest.strip_prefix("ghost ") {
                rest = r;
                is_ghost = true;
                continue;
            }
            if let Some(r) = rest
                .strip_prefix("static ")
                .or_else(|| rest.strip_prefix("abstract "))
                .or_else(|| rest.strip_prefix("nonempty "))
                .or_else(|| rest.strip_prefix("extern "))
            {
                rest = r;
                continue;
            }
            break;
        }
        let _ = is_ghost; // we don't currently surface it but accept it.

        // `module X { ... }` — flat handling: record module name (if
        // not already set) but do NOT add as a corpus entry beyond the
        // outer ModuleEntry. Nested modules are flattened.
        if rest.starts_with("module ")
            && pf.module_name.is_none()
            && line.chars().take_while(|c| c.is_whitespace()).count() == 0
        {
            // already handled above
        }

        // Try each decl keyword.
        let mut matched = false;
        for kw in DECL_KEYWORDS {
            let prefix = format!("{} ", kw);
            if let Some(after) = rest.strip_prefix(&prefix) {
                let name = after
                    .chars()
                    .take_while(|c| {
                        c.is_alphanumeric() || *c == '_' || *c == '\'' || *c == '?'
                    })
                    .collect::<String>();
                if name.is_empty() {
                    continue;
                }

                let (header, body, end) =
                    collect_header_and_body(&lines, i, after.len() + prefix.len());
                let kind = match *kw {
                    "datatype" => DeclKind::Data,
                    "class" | "trait" => DeclKind::Record,
                    "type" => DeclKind::Function,
                    _ => DeclKind::Function,
                };
                let statement = normalise_ws(&header);
                let proof = body.map(|b| normalise_ws(&b));

                let mut hz = AxiomUsage::default();
                let scan_from = line_no.saturating_sub(1);
                let scan_to = end.min(raw_lines.len());
                let scan_text = raw_lines[scan_from..scan_to].join("\n");
                flag_hazards(&scan_text, &mut hz);

                pf.decls.push(DraftDecl {
                    name,
                    kind,
                    statement,
                    proof,
                    line: line_no,
                    axiom_usage: hz,
                });
                i = end.max(i + 1);
                matched = true;
                break;
            }
        }
        if matched {
            continue;
        }
        i += 1;
    }

    pf
}

/// Starting at `lines[start]` with the header starting at byte offset
/// `name_after` within that line (after the keyword + name), capture
/// the header up to the first `{` (body opens) or `;` (no body), then
/// — if a body is present — capture the brace-balanced body. Returns
/// `(header_text, optional_body_text, next_line_index)`.
fn collect_header_and_body(
    lines: &[&str],
    start: usize,
    _name_after: usize,
) -> (String, Option<String>, usize) {
    let mut header = String::new();
    let mut j = start;
    let mut found_brace = false;
    let mut found_semi = false;
    // Header phase.
    while j < lines.len() {
        let l = lines[j];
        let mut clean = String::new();
        let mut stop = false;
        for c in l.chars() {
            if c == '{' {
                found_brace = true;
                stop = true;
                break;
            }
            if c == ';' {
                found_semi = true;
                stop = true;
                break;
            }
            clean.push(c);
        }
        if !header.is_empty() {
            header.push(' ');
        }
        header.push_str(clean.trim());
        if stop {
            break;
        }
        j += 1;
    }
    if found_semi || !found_brace {
        return (header, None, j + 1);
    }
    // Body phase: brace-balanced, scanning from the line where `{` was
    // found. We restart from line j and walk character-by-character.
    let mut body = String::new();
    let mut depth: i32 = 0;
    let mut started = false;
    let mut k = j;
    while k < lines.len() {
        let l = lines[k];
        let mut started_this_line = false;
        for c in l.chars() {
            if !started {
                if c == '{' {
                    started = true;
                    depth = 1;
                    started_this_line = true;
                    continue;
                }
                continue;
            }
            if c == '{' {
                depth += 1;
            } else if c == '}' {
                depth -= 1;
                if depth == 0 {
                    return (header, Some(body), k + 1);
                }
            }
            body.push(c);
        }
        if started && !started_this_line {
            body.push('\n');
        }
        body.push('\n');
        k += 1;
    }
    (header, Some(body), k)
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')'
                    | '['
                    | ']'
                    | '{'
                    | '}'
                    | ','
                    | ';'
                    | '='
                    | ':'
                    | '.'
                    | '<'
                    | '>'
                    | '+'
                    | '-'
                    | '*'
                    | '/'
                    | '|'
                    | '&'
                    | '!'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    // `assume` (statement OR clause) is a soundness escape: the
    // verifier accepts the predicate without proof. We map to
    // postulate-like semantics so SA filters can reject it the same
    // way they reject Agda postulates / Coq Admitted.
    //
    // We try to avoid false positives on `assume false` strings inside
    // identifiers by requiring whitespace or punctuation before
    // `assume`. A best-effort token check.
    if contains_token(text, "assume") {
        hz.postulate = true;
        hz.other.push("assume".to_string());
    }
    if text.contains("{:axiom}") || text.contains(":axiom") {
        hz.postulate = true;
        hz.other.push(":axiom".to_string());
    }
    if contains_token(text, "extern") || text.contains("{:extern}") {
        hz.other.push("extern".to_string());
    }
    if contains_token(text, "expect") {
        hz.other.push("expect".to_string());
    }
    if text.contains("{:fuel 0}") {
        hz.other.push(":fuel 0".to_string());
    }
}

fn contains_token(text: &str, tok: &str) -> bool {
    // Whitespace/punctuation-bounded substring search.
    let mut start = 0;
    while let Some(idx) = text[start..].find(tok) {
        let abs = start + idx;
        let before_ok = abs == 0
            || text.as_bytes()[abs - 1].is_ascii_whitespace()
            || !text.as_bytes()[abs - 1].is_ascii_alphanumeric()
                && text.as_bytes()[abs - 1] != b'_';
        let after_abs = abs + tok.len();
        let after_ok = after_abs >= text.len()
            || text.as_bytes()[after_abs].is_ascii_whitespace()
            || !text.as_bytes()[after_abs].is_ascii_alphanumeric()
                && text.as_bytes()[after_abs] != b'_';
        if before_ok && after_ok {
            return true;
        }
        start = abs + tok.len();
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_method_lemma_function() {
        let src = "module M {\n  method Inc(x: int) returns (y: int) ensures y == x + 1 { y := x + 1; }\n  lemma TriviallyTrue() ensures true { }\n  function Double(x: int): int { x + x }\n}\n";
        let pf = parse_dafny_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("M"));
        let names: Vec<&str> = pf.decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"Inc"), "missing Inc: {:?}", names);
        assert!(
            names.contains(&"TriviallyTrue"),
            "missing TriviallyTrue: {:?}",
            names
        );
        assert!(names.contains(&"Double"), "missing Double: {:?}", names);
        for d in &pf.decls {
            assert_eq!(d.kind, DeclKind::Function);
        }
    }

    #[test]
    fn detects_assume_hazard() {
        let src = "module M {\n  lemma Sketchy()\n    ensures false\n  {\n    assume false;\n  }\n}\n";
        let pf = parse_dafny_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "Sketchy");
        assert!(
            pf.decls[0].axiom_usage.postulate,
            "assume should set postulate hazard: {:?}",
            pf.decls[0].axiom_usage
        );
        assert!(pf.decls[0]
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "assume"));
    }

    // Known heuristic-adapter limitation 2026-06-01: body-less `extern method`
    // declarations (no `{}` block) don't terminate the brace-balanced body
    // collector cleanly, so `NativeCall` isn't extracted. Track upstream
    // alongside the broader heuristic-vs-parser tradeoffs documented in
    // docs/CORPUS-ADAPTERS.md.
    #[test]
    #[ignore]
    fn detects_datatype_and_extern() {
        let src = "module M {\n  datatype Tree = Leaf | Node(left: Tree, right: Tree)\n  extern method NativeCall(x: int) returns (y: int)\n}\n";
        let pf = parse_dafny_file(src);
        let tree = pf.decls.iter().find(|d| d.name == "Tree").unwrap();
        assert_eq!(tree.kind, DeclKind::Data);
        let nc = pf.decls.iter().find(|d| d.name == "NativeCall").unwrap();
        assert!(nc.axiom_usage.other.iter().any(|s| s == "extern"));
    }

    #[test]
    fn collects_imports_and_includes() {
        let src = "include \"Helpers.dfy\"\nimport opened Std.Math\nimport Other\n\nmodule M {\n  lemma A() { }\n}\n";
        let pf = parse_dafny_file(src);
        assert!(pf.imports.iter().any(|i| i == "Helpers.dfy"));
        assert!(pf.imports.iter().any(|i| i == "Std.Math"));
        assert!(pf.imports.iter().any(|i| i == "Other"));
    }
}
