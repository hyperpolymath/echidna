// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! SMT-LIB v2 adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.smt2` and `*.smt` file, and
//! extracts a structural index of SMT-LIB commands. Heuristic, not a
//! full parser — matches the Agda / Metamath adapter pattern.
//!
//! SMT-LIB v2 syntax recap (Lisp-like, all top-level forms are
//! parenthesised S-expressions):
//!
//! - `(set-logic LOGIC)` — e.g. QF_LIA, QF_BV, AUFLIA, ALL
//! - `(declare-const NAME TYPE)`
//! - `(declare-fun NAME (args) RET)`
//! - `(declare-sort NAME N)`
//! - `(define-fun NAME ((x t) …) RET body)`
//! - `(define-sort NAME (args) body)`
//! - `(declare-datatypes …)` / `(declare-datatype …)`
//! - `(assert formula)` — assertion (a hypothesis or the goal)
//! - `(check-sat)`, `(get-model)`, `(get-proof)`, `(get-unsat-core)`
//! - `(set-info :status sat|unsat|unknown)` — metadata
//! - `(set-info :source …)`
//! - `(push N)`, `(pop N)`, `(reset)`, `(exit)` — control
//! - Line comments: `; …`
//!
//! Mapping into the generic corpus model:
//!
//! - `declare-fun`, `declare-const`, `declare-sort` → `DeclKind::Module`
//!   (signature info; uninterpreted symbols)
//! - `define-fun`, `define-sort` → `DeclKind::Function`
//! - `assert` → `DeclKind::Function`; one entry per assertion. Name is
//!   the `:named` attribute if present in a `(! body :named NAME)`
//!   pattern, otherwise `assert-N` with N a 0-based index.
//! - `declare-datatypes`, `declare-datatype` → `DeclKind::Data`
//! - `set-logic` → recorded on the module via `options`
//! - `set-info :source` → contributes to the module name
//!
//! Hazards:
//!
//! - `(set-info :status unknown)` → file-level "this problem's status
//!   is unknown"; recorded as `axiom_usage.other.push("status_unknown")`
//!   on every entry in the file.
//! - `(declare-fun NAME (…) TYPE)` with no matching `(define-fun NAME …)`
//!   → uninterpreted symbol (mild) → `axiom_usage.other.push("uninterpreted")`.
//! - `(! body …)` patterns that lack a `:named` attribute → mild,
//!   `axiom_usage.other.push("unnamed_bang_pattern")` on the
//!   surrounding `assert`.
//!
//! Imports: SMT-LIB v2 files are self-contained — `imports` is always
//! empty.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `target`, and `_build` regardless
/// of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_smtlib(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "smtlib".to_string(),
        ..Default::default()
    };

    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_smtlib_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed.module_name.clone().unwrap_or_else(|| {
            rel.with_extension("")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(".")
        });
        let module_entry = ModuleEntry {
            name: module_name.clone(),
            path: rel,
            options: parsed.options,
            imports: Vec::new(),
            entries: Vec::new(),
        };
        corpus.modules.push(module_entry);

        let stamp_unknown = parsed.status_unknown;

        // Build the set of *defined* function/sort names so we can flag
        // declares that have no matching define as "uninterpreted".
        let mut defined: HashSet<String> = HashSet::new();
        for d in &parsed.decls {
            if matches!(d.kind, DeclKind::Function) && d.is_define {
                defined.insert(d.name.clone());
            }
            if matches!(d.kind, DeclKind::Data) {
                defined.insert(d.name.clone());
            }
        }

        for d in parsed.decls {
            let entry_idx = corpus.entries.len();
            let qualified = format!("{}.{}", module_name, d.name);
            let mut hz = d.axiom_usage;
            if stamp_unknown {
                hz.other.push("status_unknown".to_string());
            }
            if matches!(d.kind, DeclKind::Module) && d.is_declare && !defined.contains(&d.name) {
                hz.other.push("uninterpreted".to_string());
            }
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(CorpusEntry {
                name: d.name,
                qualified,
                module_idx,
                kind: d.kind,
                statement: d.statement,
                proof: None,
                line: d.line,
                dependencies: Vec::new(),
                axiom_usage: hz,
            });
        }
    }

    corpus.reindex();
    Ok(corpus)
}

fn walk_smtlib(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
            if matches!(name_s.as_ref(), ".git" | "target" | "_build") {
                continue;
            }
            walk_smtlib(&p, out)?;
        } else {
            let ext = p.extension().and_then(|s| s.to_str());
            if matches!(ext, Some("smt2") | Some("smt")) {
                out.push(p);
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    module_name: Option<String>,
    /// `set-logic` value + any other `set-option`s, one token per
    /// option for parity with the Agda adapter's `OPTIONS` tokens.
    options: Vec<String>,
    decls: Vec<DraftDecl>,
    status_unknown: bool,
}

#[derive(Debug)]
struct DraftDecl {
    name: String,
    kind: DeclKind,
    statement: String,
    line: usize,
    axiom_usage: AxiomUsage,
    /// True for `declare-fun`/`declare-const`/`declare-sort`.
    is_declare: bool,
    /// True for `define-fun`/`define-sort`.
    is_define: bool,
}

/// Strip `;`-to-end-of-line comments, preserving newlines so line
/// numbers stay aligned. Quoted-symbol `|…|` blocks and string
/// literals `"…"` are passed through untouched.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut in_string = false;
    let mut in_pipe = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            out.push(c);
            // SMT-LIB v2 strings: `""` is the escape for `"`. Treat
            // `""` as a no-close.
            if c == b'"' {
                if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                    out.push(bytes[i + 1]);
                    i += 2;
                    continue;
                }
                in_string = false;
            }
            i += 1;
            continue;
        }
        if in_pipe {
            out.push(c);
            if c == b'|' {
                in_pipe = false;
            }
            i += 1;
            continue;
        }
        if c == b'"' {
            in_string = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == b'|' {
            in_pipe = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == b';' {
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_smtlib_file(raw: &str) -> ParsedFile {
    let mut pf = ParsedFile::default();
    let stripped = strip_comments(raw);
    let forms = split_top_sexprs(&stripped);

    let mut assert_idx: usize = 0;
    for (line, body) in forms {
        // body is the content WITHOUT the outer parens. e.g.
        // `set-logic QF_LIA`.
        let toks = tokenise_sexpr(&body);
        if toks.is_empty() {
            continue;
        }
        match toks[0].as_str() {
            "set-logic" => {
                if let Some(logic) = toks.get(1) {
                    pf.options.push(format!("logic:{}", logic));
                }
            },
            "set-info" => {
                // (set-info :key value …)
                if let Some(key) = toks.get(1) {
                    if key == ":status" {
                        if let Some(v) = toks.get(2) {
                            if v == "unknown" {
                                pf.status_unknown = true;
                            }
                        }
                    } else if key == ":source" {
                        // Best-effort: take all remaining tokens
                        // joined as the source identifier.
                        if toks.len() > 2 {
                            let s = toks[2..]
                                .iter()
                                .map(|s| s.as_str())
                                .collect::<Vec<_>>()
                                .join(" ");
                            let s = s.trim_matches(|c: char| c == '"' || c == '|').trim();
                            if !s.is_empty() && pf.module_name.is_none() {
                                pf.module_name = Some(s.to_string());
                            }
                        }
                    }
                }
            },
            "set-option" => {
                if let Some(opt) = toks.get(1) {
                    pf.options.push(opt.clone());
                }
            },
            "declare-const" => {
                if let Some(name) = toks.get(1) {
                    pf.decls.push(DraftDecl {
                        name: name.clone(),
                        kind: DeclKind::Module,
                        statement: normalise_ws(&body),
                        line,
                        axiom_usage: AxiomUsage::default(),
                        is_declare: true,
                        is_define: false,
                    });
                }
            },
            "declare-fun" | "declare-sort" => {
                if let Some(name) = toks.get(1) {
                    pf.decls.push(DraftDecl {
                        name: name.clone(),
                        kind: DeclKind::Module,
                        statement: normalise_ws(&body),
                        line,
                        axiom_usage: AxiomUsage::default(),
                        is_declare: true,
                        is_define: false,
                    });
                }
            },
            "define-fun" | "define-sort" | "define-fun-rec" => {
                if let Some(name) = toks.get(1) {
                    pf.decls.push(DraftDecl {
                        name: name.clone(),
                        kind: DeclKind::Function,
                        statement: normalise_ws(&body),
                        line,
                        axiom_usage: AxiomUsage::default(),
                        is_declare: false,
                        is_define: true,
                    });
                }
            },
            "declare-datatypes" | "declare-datatype" => {
                // Datatype declarations carry one or more names. We
                // pull the first identifiable name token; consumers
                // that need every constructor can re-tokenise the
                // statement.
                let name = extract_datatype_name(&toks).unwrap_or_else(|| "datatype".to_string());
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Data,
                    statement: normalise_ws(&body),
                    line,
                    axiom_usage: AxiomUsage::default(),
                    is_declare: false,
                    is_define: false,
                });
            },
            "assert" => {
                // Try to find a :named attribute inside the asserted
                // formula. Pattern: `(assert (! <body> :named NAME))`.
                let named = extract_named_attr(&body);
                let has_bang = body.contains("(!") || body.contains("( !");
                let mut hz = AxiomUsage::default();
                if has_bang && named.is_none() {
                    hz.other.push("unnamed_bang_pattern".to_string());
                }
                let name = named.unwrap_or_else(|| format!("assert-{}", assert_idx));
                assert_idx += 1;
                // Statement: the asserted formula itself (drop the
                // leading `assert ` keyword).
                let formula = body
                    .trim_start()
                    .strip_prefix("assert")
                    .unwrap_or(&body)
                    .trim();
                pf.decls.push(DraftDecl {
                    name,
                    kind: DeclKind::Function,
                    statement: normalise_ws(formula),
                    line,
                    axiom_usage: hz,
                    is_declare: false,
                    is_define: false,
                });
            },
            // Control / query commands without corpus entries:
            "check-sat" | "check-sat-assuming" | "get-model" | "get-proof" | "get-unsat-core"
            | "get-value" | "get-assertions" | "push" | "pop" | "reset" | "reset-assertions"
            | "exit" | "echo" => {},
            _ => {},
        }
    }

    pf
}

/// Split a top-level S-expression stream into `(line, body)` pairs,
/// where `body` is the content of one top-level `( … )` form WITHOUT
/// the enclosing parens. Tracks line numbers, quotes, and `|…|`
/// quoted symbols.
fn split_top_sexprs(src: &str) -> Vec<(usize, String)> {
    let bytes = src.as_bytes();
    let mut out: Vec<(usize, String)> = Vec::new();
    let mut i = 0;
    let mut cur_line = 1usize;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'\n' {
            cur_line += 1;
            i += 1;
            continue;
        }
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'(' {
            let start_line = cur_line;
            let mut depth = 1i32;
            i += 1;
            let body_start = i;
            let mut in_string = false;
            let mut in_pipe = false;
            while i < bytes.len() && depth > 0 {
                let d = bytes[i];
                if d == b'\n' {
                    cur_line += 1;
                }
                if in_string {
                    if d == b'"' {
                        if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                            i += 2;
                            continue;
                        }
                        in_string = false;
                    }
                    i += 1;
                    continue;
                }
                if in_pipe {
                    if d == b'|' {
                        in_pipe = false;
                    }
                    i += 1;
                    continue;
                }
                match d {
                    b'"' => in_string = true,
                    b'|' => in_pipe = true,
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            let body = &src[body_start..i];
                            out.push((start_line, body.to_string()));
                            i += 1;
                            break;
                        }
                    },
                    _ => {},
                }
                i += 1;
            }
            continue;
        }
        // Skip stray characters at top level.
        i += 1;
    }
    out
}

/// Coarse tokeniser for an S-expression body: splits on whitespace,
/// keeps parens as standalone tokens, preserves `"…"` strings and
/// `|…|` quoted symbols as single tokens.
fn tokenise_sexpr(body: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'(' || c == b')' {
            out.push((c as char).to_string());
            i += 1;
            continue;
        }
        if c == b'"' {
            let start = i;
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'"' {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                        i += 2;
                        continue;
                    }
                    i += 1;
                    break;
                }
                i += 1;
            }
            out.push(String::from_utf8_lossy(&bytes[start..i]).into_owned());
            continue;
        }
        if c == b'|' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != b'|' {
                i += 1;
            }
            if i < bytes.len() {
                i += 1;
            }
            out.push(String::from_utf8_lossy(&bytes[start..i]).into_owned());
            continue;
        }
        let start = i;
        while i < bytes.len()
            && !bytes[i].is_ascii_whitespace()
            && bytes[i] != b'('
            && bytes[i] != b')'
        {
            i += 1;
        }
        out.push(String::from_utf8_lossy(&bytes[start..i]).into_owned());
    }
    out
}

/// Best-effort extraction of the first declared name from a
/// `declare-datatypes` / `declare-datatype` body. Both v2.6 single-
/// form `(declare-datatype NAME …)` and the multi-form
/// `(declare-datatypes ((N1 a1) (N2 a2)) (…))` are handled.
fn extract_datatype_name(toks: &[String]) -> Option<String> {
    if toks.is_empty() {
        return None;
    }
    // Single-arity form: `declare-datatype NAME …`
    if toks[0] == "declare-datatype" {
        return toks.get(1).cloned().filter(|s| s != "(");
    }
    // Multi-arity form: scan past the first `(` for the first
    // identifier-ish token.
    for w in toks.windows(2) {
        if w[0] == "(" {
            let t = &w[1];
            if !t.is_empty() && t != "(" && t != ")" {
                return Some(t.clone());
            }
        }
    }
    None
}

/// Find a `:named NAME` attribute in an asserted formula. Looks for
/// the literal `:named` followed (after whitespace) by an identifier
/// token. Quoted symbols (`|foo bar|`) are returned verbatim, including
/// the bars.
fn extract_named_attr(body: &str) -> Option<String> {
    let needle = ":named";
    let idx = body.find(needle)?;
    let rest = &body[idx + needle.len()..];
    let rest = rest.trim_start();
    if rest.is_empty() {
        return None;
    }
    let bytes = rest.as_bytes();
    let first = bytes[0];
    if first == b'|' {
        // Quoted symbol — read until matching `|`.
        let mut j = 1usize;
        while j < bytes.len() && bytes[j] != b'|' {
            j += 1;
        }
        if j < bytes.len() {
            return Some(rest[..=j].to_string());
        }
        return None;
    }
    let end = rest
        .find(|c: char| c.is_whitespace() || c == ')' || c == '(')
        .unwrap_or(rest.len());
    if end == 0 {
        return None;
    }
    Some(rest[..end].to_string())
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_logic_const_and_assert() {
        let src = "(set-logic QF_LIA)\n\
                   (declare-const x Int)\n\
                   (assert (> x 0))\n\
                   (check-sat)\n";
        let pf = parse_smtlib_file(src);
        assert!(pf.options.iter().any(|o| o == "logic:QF_LIA"));
        // Two decls: the const + one assert.
        assert_eq!(pf.decls.len(), 2);
        let cd = pf.decls.iter().find(|d| d.name == "x").unwrap();
        assert_eq!(cd.kind, DeclKind::Module);
        assert!(cd.is_declare);
        let a = pf.decls.iter().find(|d| d.name == "assert-0").unwrap();
        assert_eq!(a.kind, DeclKind::Function);
        assert!(a.statement.contains("> x 0") || a.statement.contains("(> x 0)"));
        assert!(!pf.status_unknown);
    }

    #[test]
    fn flags_status_unknown_via_ingest() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("u.smt2");
        std::fs::write(
            &p,
            "(set-info :status unknown)\n\
             (declare-const x Int)\n\
             (assert (= x x))\n",
        )
        .unwrap();
        let c = ingest(dir.path()).unwrap();
        assert!(!c.entries.is_empty());
        for e in &c.entries {
            assert!(
                e.axiom_usage.other.iter().any(|s| s == "status_unknown"),
                "entry {} missing status_unknown flag",
                e.name
            );
        }
    }

    #[test]
    fn flags_uninterpreted_when_no_define() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("u.smt2");
        std::fs::write(
            &p,
            "(declare-fun f (Int) Int)\n\
             (assert (= (f 1) 2))\n",
        )
        .unwrap();
        let c = ingest(dir.path()).unwrap();
        let f = c.entries.iter().find(|e| e.name == "f").unwrap();
        assert!(f.axiom_usage.other.iter().any(|s| s == "uninterpreted"));
    }

    #[test]
    fn named_assert_uses_attribute_as_name() {
        let src = "(assert (! (> x 0) :named pos_x))\n";
        let pf = parse_smtlib_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "pos_x");
        // Bang pattern with a name is NOT flagged.
        assert!(!pf.decls[0]
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "unnamed_bang_pattern"));
    }

    #[test]
    fn unnamed_bang_pattern_is_flagged() {
        let src = "(assert (! (> x 0) :pattern ((f x))))\n";
        let pf = parse_smtlib_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0]
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "unnamed_bang_pattern"));
    }

    #[test]
    fn strips_line_comments() {
        let src = "; this is a comment\n\
                   (declare-const x Int) ; trailing\n\
                   (assert (> x 0))\n";
        let pf = parse_smtlib_file(src);
        assert_eq!(pf.decls.len(), 2);
    }

    #[test]
    fn datatype_recognised_as_data_kind() {
        let src = "(declare-datatype Color ((red) (green) (blue)))\n";
        let pf = parse_smtlib_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].kind, DeclKind::Data);
        assert_eq!(pf.decls[0].name, "Color");
    }
}
