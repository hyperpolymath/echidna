// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Why3 adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.mlw` (WhyML / new) and `*.why`
//! (legacy) source file, and extracts a structural index. Why3 is a
//! deductive-verification platform that dispatches goals to a fleet of
//! external SMT/first-order provers (Alt-Ergo, Z3, CVC4/5, E, Vampire,
//! Coq, …). The corpus index is the structural skeleton — `theory` /
//! `module` envelopes plus the named declarations they contain.
//!
//! What we recognise (inside a `theory X ... end` or `module X ... end`
//! envelope):
//! - `predicate P (x: int) = ...`
//! - `function f (x: int) : int = ...`
//! - `lemma L: forall x: int. ...` (proven via automation)
//! - `theorem T: ...` (alias of `lemma` with stronger intent)
//! - `goal G: ...` (proof obligation; dispatched to back-ends)
//! - `axiom A: ...` (HAZARD — unproved assumption)
//! - `type T = ...` (datatype-like or alias)
//! - `use [import|export] X` / `clone [import|export] X with ...`
//!
//! WhyML extras (inside `module M ... end` in `.mlw`):
//! - `let function`, `let lemma`, `let rec`, `val function`,
//!   `val ghost`, `exception E`
//!
//! Hazards (Why3's unproved assumption surface):
//! - `axiom` — by definition, an unproved assumption.
//! - `val function` / `val lemma` — uninterpreted symbol / lemma at the
//!   spec level; equivalent in soundness terms to an axiom.
//! - `assume { ... }` inside code (WhyML).
//! - `absurd` in proof-by-contradiction context.
//!
//! Comments: `(* ... *)`, OCaml-style. They DO nest.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_why3(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "why3".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_why3_file(&raw);

        // A Why3 file can contain multiple `theory` / `module`
        // envelopes; each becomes its own ModuleEntry. If parsing
        // produced none, fall back to a single file-level module.
        if parsed.envelopes.is_empty() {
            corpus.modules.push(ModuleEntry {
                name: rel
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join("."),
                path: rel,
                options: Vec::new(),
                imports: Vec::new(),
                entries: Vec::new(),
            });
            continue;
        }

        for env in parsed.envelopes {
            let module_idx = corpus.modules.len();
            corpus.modules.push(ModuleEntry {
                name: env.name.clone(),
                path: rel.clone(),
                options: Vec::new(),
                imports: env.imports,
                entries: Vec::new(),
            });
            for d in env.decls {
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

fn walk_why3(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "_build" | "node_modules" | ".cache"
            ) {
                continue;
            }
            walk_why3(&p, out)?;
        } else {
            // Skip Why3 session bookkeeping; these are not source.
            if name_s == "why3session.xml" || name_s == "why3shapes.gz" {
                continue;
            }
            match p.extension().and_then(|s| s.to_str()) {
                Some("mlw") | Some("why") => out.push(p),
                _ => {},
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    envelopes: Vec<Envelope>,
}

#[derive(Debug, Default)]
struct Envelope {
    name: String,
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

/// Strip Why3 `(* ... *)` block comments (NESTING). Preserve line
/// breaks so line numbers stay stable.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut depth: usize = 0;
    let mut in_string = false;
    while i < bytes.len() {
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                depth += 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b')' {
                depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
            i += 1;
            continue;
        }
        if in_string {
            out.push(bytes[i]);
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i + 1]);
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
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
        if bytes[i] == b'"' {
            in_string = true;
            out.push(bytes[i]);
            i += 1;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

const ENVELOPE_KEYWORDS: &[&str] = &["theory ", "module "];

fn parse_why3_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim_start();
        // Open envelope?
        let mut header_match: Option<&str> = None;
        for kw in ENVELOPE_KEYWORDS {
            if trimmed.starts_with(kw) {
                header_match = Some(kw);
                break;
            }
        }
        if let Some(kw) = header_match {
            let rest = &trimmed[kw.len()..];
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                .collect();
            if name.is_empty() {
                i += 1;
                continue;
            }
            let (env, next) = parse_envelope(&lines, &raw_lines, i, name);
            pf.envelopes.push(env);
            i = next;
            continue;
        }
        i += 1;
    }

    pf
}

/// Parse a `theory NAME ... end` or `module NAME ... end` envelope
/// starting at `lines[start]`. Returns the envelope and the index of
/// the line AFTER the matching `end`.
fn parse_envelope(
    lines: &[&str],
    raw_lines: &[&str],
    start: usize,
    name: String,
) -> (Envelope, usize) {
    let mut env = Envelope {
        name,
        imports: Vec::new(),
        decls: Vec::new(),
    };

    // Find the matching `end`. Why3 nests `module`/`theory` only at
    // top-level (so this is fine in practice), but to be safe we count
    // any further opener and require a balanced `end`.
    let mut depth: i32 = 1;
    let mut j = start + 1;
    let mut body_end = lines.len();
    while j < lines.len() {
        let t = lines[j].trim_start();
        let opens = ENVELOPE_KEYWORDS.iter().any(|kw| t.starts_with(kw));
        if opens {
            depth += 1;
        } else if t == "end" || t.starts_with("end ") || t.starts_with("end\t") {
            depth -= 1;
            if depth == 0 {
                body_end = j;
                break;
            }
        }
        j += 1;
    }

    // Imports / clones inside the envelope.
    for line in lines.iter().take(body_end).skip(start + 1) {
        let t = line.trim_start();
        let import_rest = t
            .strip_prefix("use import ")
            .or_else(|| t.strip_prefix("use export "))
            .or_else(|| t.strip_prefix("use "))
            .or_else(|| t.strip_prefix("clone import "))
            .or_else(|| t.strip_prefix("clone export "))
            .or_else(|| t.strip_prefix("clone "));
        if let Some(rest) = import_rest {
            let mod_name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                .collect();
            if !mod_name.is_empty() && !env.imports.contains(&mod_name) {
                env.imports.push(mod_name);
            }
        }
    }

    // Declarations inside the envelope.
    let mut k = start + 1;
    while k < body_end {
        let line = lines[k];
        let trimmed = line.trim_start();
        let line_no = k + 1;

        let (kind_kw, hazard, decl_kind) = classify_decl(trimmed);
        if let Some(kw) = kind_kw {
            let after = &trimmed[kw.len()..];
            // Name is the next identifier-shaped token.
            let after_trim = after.trim_start();
            let name: String = after_trim
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                .collect();
            if name.is_empty() {
                k += 1;
                continue;
            }
            let (header, body, end) = collect_decl(lines, k, body_end);
            let statement = normalise_ws(&header);
            let proof = body.map(|b| normalise_ws(&b));

            let mut hz = AxiomUsage::default();
            if hazard {
                hz.postulate = true;
                hz.other.push(kw.trim().to_string());
            }
            // Body-level hazards.
            let scan_from = line_no.saturating_sub(1);
            let scan_to = end.min(raw_lines.len());
            let scan_text = raw_lines[scan_from..scan_to].join("\n");
            flag_body_hazards(&scan_text, &mut hz);

            env.decls.push(DraftDecl {
                name,
                kind: decl_kind,
                statement,
                proof,
                line: line_no,
                axiom_usage: hz,
            });
            k = end.max(k + 1);
            continue;
        }

        k += 1;
    }

    (env, body_end + 1)
}

/// Returns `(keyword_prefix_to_strip, is_hazard, decl_kind)`. The
/// keyword string includes its trailing space so we can `strip_prefix`
/// cleanly. Postulate-class (`axiom`, `val function`, `val lemma`) gets
/// `hazard=true`. Plain `type` is mapped to `Data`.
fn classify_decl(line: &str) -> (Option<&'static str>, bool, DeclKind) {
    // Compound prefixes first so e.g. `let function` doesn't get
    // shadowed by `let`.
    let cases: &[(&str, bool, DeclKind)] = &[
        ("let rec function ", false, DeclKind::Function),
        ("let function ", false, DeclKind::Function),
        ("let lemma ", false, DeclKind::Function),
        ("let predicate ", false, DeclKind::Function),
        ("let rec ", false, DeclKind::Function),
        ("val function ", true, DeclKind::Postulate),
        ("val predicate ", true, DeclKind::Postulate),
        ("val lemma ", true, DeclKind::Postulate),
        ("val ghost ", true, DeclKind::Postulate),
        ("val ", true, DeclKind::Postulate),
        ("predicate ", false, DeclKind::Function),
        ("function ", false, DeclKind::Function),
        ("lemma ", false, DeclKind::Function),
        ("theorem ", false, DeclKind::Function),
        ("goal ", false, DeclKind::Function),
        ("axiom ", true, DeclKind::Postulate),
        ("type ", false, DeclKind::Data),
        ("exception ", false, DeclKind::Function),
    ];
    for (kw, hazard, kind) in cases {
        if line.starts_with(kw) {
            return (Some(kw), *hazard, *kind);
        }
    }
    (None, false, DeclKind::Function)
}

/// Collect a Why3 decl spanning multiple lines. Strategy: gather lines
/// until we hit a blank line OR the next line starts another decl OR
/// we reach the envelope's `end`. Split on `=` (first top-level) into
/// header/body if present.
fn collect_decl(lines: &[&str], start: usize, body_end: usize) -> (String, Option<String>, usize) {
    let mut block = String::new();
    let mut k = start;
    while k < body_end {
        let l = lines[k];
        let t = l.trim_start();
        if k > start {
            if t.is_empty() {
                k += 1;
                break;
            }
            // Stop at next decl keyword.
            if classify_decl(t).0.is_some() {
                break;
            }
            if t == "end" || t.starts_with("end ") {
                break;
            }
        }
        if !block.is_empty() {
            block.push(' ');
        }
        block.push_str(l.trim());
        k += 1;
    }
    // Split at the first top-level `=` not preceded by `:` or `<` etc.
    let header;
    let body;
    if let Some(eq_idx) = find_top_eq(&block) {
        header = block[..eq_idx].to_string();
        body = Some(block[eq_idx + 1..].trim().to_string());
    } else {
        header = block;
        body = None;
    }
    (header, body, k)
}

/// Find the first `=` at paren-depth 0 that isn't part of `==`, `<=`,
/// `>=`, `:=`, or `<>`. Returns its char index in `s` (byte index, ok
/// because we only return positions of ASCII `=`).
fn find_top_eq(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'=' if depth == 0 => {
                let prev = if i > 0 { Some(bytes[i - 1]) } else { None };
                let next = bytes.get(i + 1).copied();
                if matches!(prev, Some(b'<' | b'>' | b':' | b'=' | b'/')) {
                    i += 1;
                    continue;
                }
                if next == Some(b'=') {
                    i += 2;
                    continue;
                }
                return Some(i);
            },
            _ => {},
        }
        i += 1;
    }
    None
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

fn flag_body_hazards(text: &str, hz: &mut AxiomUsage) {
    if contains_token(text, "assume") {
        hz.postulate = true;
        hz.other.push("assume".to_string());
    }
    if contains_token(text, "absurd") {
        hz.other.push("absurd".to_string());
    }
}

fn contains_token(text: &str, tok: &str) -> bool {
    let mut start = 0;
    while let Some(idx) = text[start..].find(tok) {
        let abs = start + idx;
        let before_ok = abs == 0
            || !text.as_bytes()[abs - 1].is_ascii_alphanumeric()
                && text.as_bytes()[abs - 1] != b'_';
        let after_abs = abs + tok.len();
        let after_ok = after_abs >= text.len()
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
    fn parses_theory_with_lemma_and_predicate() {
        let src = "theory T\n  use import int.Int\n  predicate even (x: int) = exists k: int. x = 2 * k\n  function double (x: int) : int = x + x\n  lemma double_even: forall x: int. even (double x)\nend\n";
        let pf = parse_why3_file(src);
        assert_eq!(pf.envelopes.len(), 1);
        let env = &pf.envelopes[0];
        assert_eq!(env.name, "T");
        assert!(env.imports.iter().any(|i| i == "int.Int"));
        let names: Vec<&str> = env.decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"even"), "missing even: {:?}", names);
        assert!(names.contains(&"double"), "missing double: {:?}", names);
        assert!(
            names.contains(&"double_even"),
            "missing double_even: {:?}",
            names
        );
        // None of these should be flagged as hazards.
        for d in &env.decls {
            assert!(
                !d.axiom_usage.any(),
                "{} should not be hazardous: {:?}",
                d.name,
                d.axiom_usage
            );
        }
    }

    #[test]
    fn detects_axiom_hazard() {
        let src = "theory T\n  axiom bad: forall x: int. x = x + 1\n  lemma derived: forall x: int. x = x + 1\nend\n";
        let pf = parse_why3_file(src);
        assert_eq!(pf.envelopes.len(), 1);
        let bad = pf.envelopes[0]
            .decls
            .iter()
            .find(|d| d.name == "bad")
            .expect("bad missing");
        assert_eq!(bad.kind, DeclKind::Postulate);
        assert!(bad.axiom_usage.postulate);
    }

    #[test]
    fn detects_val_function_as_postulate() {
        let src = "module M\n  val function f (x: int) : int\n  let function g (x: int) : int = f x + 1\nend\n";
        let pf = parse_why3_file(src);
        let f = pf.envelopes[0]
            .decls
            .iter()
            .find(|d| d.name == "f")
            .expect("f missing");
        assert_eq!(f.kind, DeclKind::Postulate);
        assert!(f.axiom_usage.postulate);
        let g = pf.envelopes[0]
            .decls
            .iter()
            .find(|d| d.name == "g")
            .expect("g missing");
        assert_eq!(g.kind, DeclKind::Function);
        assert!(!g.axiom_usage.postulate);
    }
}
