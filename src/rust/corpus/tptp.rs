// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! TPTP (Thousands of Problems for Theorem Provers) adapter for the
//! corpus indexer.
//!
//! Walks a project root, finds every `*.p` and `*.tptp` file, and
//! extracts a structural index of TPTP statements. Heuristic, not a
//! full parser — matches the Agda / Metamath adapter pattern.
//!
//! TPTP syntax recap:
//!
//! - `cnf(name, role, formula).` — clause normal form
//! - `fof(name, role, formula).` — first-order form
//! - `tff(name, role, formula).` — typed first-order
//! - `thf(name, role, formula).` — typed higher-order
//! - `tcf(name, role, formula).` — typed clause normal form
//! - `include('file.p').` — imports another problem file
//! - `% …` line comments and `/* … */` block comments
//!
//! Roles:
//!
//! - `axiom`, `hypothesis`, `definition`, `assumption` → the "given facts"
//!   → `DeclKind::Postulate`. (`axiom` is fundamental to TPTP problems
//!   and is NOT itself a hazard.)
//! - `conjecture`, `negated_conjecture`, `theorem`, `lemma`, `corollary`
//!   → the goal(s) to prove → `DeclKind::Function`.
//! - `type` → signature information → `DeclKind::Module` (we don't
//!   create a separate per-type module; we mark the entry as a Module
//!   kind so consumers know it's signature-level).
//! - `unknown`, `plain` (and anything unrecognised) → `DeclKind::Function`.
//!
//! Hazards:
//!
//! - A file that contains only postulate-role entries with no conjecture
//!   / theorem / lemma / corollary / negated_conjecture is flagged on
//!   *every* entry's `axiom_usage.other` with `"no_conjecture"`. The
//!   semantics are "this file states facts but doesn't pose a goal";
//!   downstream prover dispatchers can drop such files from problem
//!   selection.
//!
//! Module name: derived from the `% Problem : NAME` comment header
//! (TPTP convention used by the official problem library) when present;
//! otherwise from the filename stem.
//!
//! Imports: every `include('X').` line contributes one import, with the
//! quoted path stored verbatim (no quote-stripping; consumers handle
//! the lookup).

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `target`, and `_build` regardless
/// of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_tptp(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "tptp".to_string(),
        ..Default::default()
    };

    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_tptp_file(&raw);

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
            options: Vec::new(),
            imports: parsed.imports,
            entries: Vec::new(),
        };
        corpus.modules.push(module_entry);

        // File-scoped hazard: no conjecture-class role anywhere in the
        // file. Detected after parsing so we can stamp every entry.
        let has_goal = parsed.decls.iter().any(|d| d.is_goal);
        let stamp_no_conjecture = !has_goal && !parsed.decls.is_empty();

        for d in parsed.decls {
            let entry_idx = corpus.entries.len();
            let qualified = format!("{}.{}", module_name, d.name);
            let mut hz = d.axiom_usage;
            if stamp_no_conjecture {
                hz.other.push("no_conjecture".to_string());
            }
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(CorpusEntry {
                name: d.name,
                qualified,
                module_idx,
                kind: d.kind,
                statement: d.statement,
                proof: None, // TPTP files do not carry proofs
                line: d.line,
                dependencies: Vec::new(),
                axiom_usage: hz,
            });
        }
    }

    corpus.reindex();
    Ok(corpus)
}

fn walk_tptp(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
            walk_tptp(&p, out)?;
        } else {
            let ext = p.extension().and_then(|s| s.to_str());
            if matches!(ext, Some("p") | Some("tptp")) {
                out.push(p);
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    module_name: Option<String>,
    imports: Vec<String>,
    decls: Vec<DraftDecl>,
}

#[derive(Debug)]
struct DraftDecl {
    name: String,
    kind: DeclKind,
    statement: String,
    line: usize,
    axiom_usage: AxiomUsage,
    /// True if the role is in the conjecture / theorem / lemma /
    /// corollary / negated_conjecture family — used for the
    /// file-level "no_conjecture" hazard.
    is_goal: bool,
}

/// Strip line (`%`) and block (`/* … */`) comments, preserving newlines
/// so line numbers stay aligned.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut in_block = false;
    let mut in_string = false;
    let mut in_squote = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_block {
            if i + 1 < bytes.len() && c == b'*' && bytes[i + 1] == b'/' {
                in_block = false;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            out.push(if c == b'\n' { b'\n' } else { b' ' });
            i += 1;
            continue;
        }
        if in_string {
            out.push(c);
            if c == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if in_squote {
            out.push(c);
            if c == b'\'' {
                in_squote = false;
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
        if c == b'\'' {
            in_squote = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == b'%' {
            // Line comment — skip to end of line, preserving the
            // newline.
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }
        if i + 1 < bytes.len() && c == b'/' && bytes[i + 1] == b'*' {
            in_block = true;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        out.push(c);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_tptp_file(raw: &str) -> ParsedFile {
    let mut pf = ParsedFile::default();

    // Scan raw (un-stripped) lines for the `% Problem : NAME` header.
    // TPTP files routinely use a column-aligned header band, so the
    // whitespace between `Problem` and `:` is variable.
    for line in raw.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix('%') {
            let rest = rest.trim_start();
            if let Some(val) = rest.strip_prefix("Problem") {
                let val = val.trim_start();
                if let Some(after_colon) = val.strip_prefix(':') {
                    let name = after_colon.trim();
                    if !name.is_empty() {
                        pf.module_name = Some(name.to_string());
                        break;
                    }
                }
            }
        } else if !t.is_empty() {
            // Past the header band — bail.
            break;
        }
    }

    // Strip comments before statement parsing.
    let stripped = strip_comments(raw);

    // TPTP statements are terminated by `.` at top level (paren depth
    // 0). We split the file into statements with a small state machine
    // that tracks parens / brackets / quotes.
    let bytes = stripped.as_bytes();
    let mut i = 0usize;
    let mut start = 0usize;
    let mut start_line = 1usize;
    let mut cur_line = 1usize;
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut in_squote = false;

    let mut statements: Vec<(usize, String)> = Vec::new();

    while i < bytes.len() {
        let c = bytes[i];
        if c == b'\n' {
            cur_line += 1;
        }
        if in_string {
            if c == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if in_squote {
            if c == b'\'' {
                in_squote = false;
            }
            i += 1;
            continue;
        }
        match c {
            b'"' => in_string = true,
            b'\'' => in_squote = true,
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'.' if depth <= 0 => {
                let raw_stmt = &stripped[start..i];
                // Skip empty / whitespace-only chunks.
                if raw_stmt.trim().is_empty() {
                    // advance past the dot and reset
                    i += 1;
                    start = i;
                    // start_line tracks the next non-empty char
                    start_line = cur_line;
                    continue;
                }
                statements.push((start_line, raw_stmt.to_string()));
                i += 1;
                start = i;
                // The next statement starts at the next non-whitespace
                // line — but tracking exactly is fiddly; cur_line is
                // close enough for human-facing line reporting.
                start_line = cur_line;
                continue;
            },
            _ => {},
        }
        i += 1;
    }

    for (line, stmt) in statements {
        let stmt_trim = stmt.trim_start();
        // include('path').
        if let Some(rest) = stmt_trim.strip_prefix("include") {
            let rest = rest.trim_start();
            if let Some(args) = rest.strip_prefix('(') {
                // Take content up to matching `)` (single level — TPTP
                // include arguments don't nest).
                if let Some(end) = args.rfind(')') {
                    let inside = args[..end].trim();
                    let path = inside.trim_matches(|c: char| c == '\'' || c == '"').to_string();
                    if !path.is_empty() && !pf.imports.contains(&path) {
                        pf.imports.push(path);
                    }
                }
            }
            continue;
        }
        // Annotated formula: `KIND(name, role, formula [, source])`.
        if let Some(decl) = parse_annotated_formula(stmt_trim, line) {
            pf.decls.push(decl);
        }
    }

    pf
}

/// Parse a top-level annotated formula such as `fof(name, role, formula).`
/// (the trailing `.` is already stripped by the statement splitter).
fn parse_annotated_formula(stmt: &str, line: usize) -> Option<DraftDecl> {
    let kinds = ["cnf", "fof", "tff", "thf", "tcf"];
    let mut head: Option<&str> = None;
    let mut rest: Option<&str> = None;
    for k in &kinds {
        if let Some(r) = stmt.strip_prefix(k) {
            let r2 = r.trim_start();
            if r2.starts_with('(') {
                head = Some(k);
                rest = Some(&r2[1..]);
                break;
            }
        }
    }
    let _head = head?;
    let body = rest?;

    // Split top-level commas. We want at most 3 fields: name, role,
    // formula. Annotated formulae may have a 4th `source` field — we
    // collapse 4+ into the third (formula) since we only need name +
    // role + statement text.
    //
    // Strip exactly ONE trailing `)` to undo the outer `KIND(...)`
    // wrapper; internal parens like `mult(Y, X)` must survive.
    let body = body.trim_end();
    let body = body.strip_suffix(')').unwrap_or(body).trim();
    let parts = split_top_commas(body, 3);
    if parts.len() < 3 {
        return None;
    }
    let name = parts[0].trim().to_string();
    let role = parts[1].trim().to_lowercase();
    let formula = parts[2].trim().to_string();
    if name.is_empty() || role.is_empty() {
        return None;
    }

    let (kind, is_goal, is_postulate) = classify_role(&role);
    let mut hz = AxiomUsage::default();
    if is_postulate {
        // `axiom` role is fundamental in TPTP — NOT itself a hazard.
        // We DO mark `postulate=true` for the consumer's bookkeeping
        // so role counts are visible, mirroring metamath.rs treatment
        // of `$a`.
        hz.postulate = true;
    }

    Some(DraftDecl {
        name,
        kind,
        statement: normalise_ws(&formula),
        line,
        axiom_usage: hz,
        is_goal,
    })
}

/// Split `s` on top-level commas (paren depth == 0, not inside quotes).
/// Returns at most `max` parts; remaining text (commas included) is
/// concatenated into the final part.
fn split_top_commas(s: &str, max: usize) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut in_squote = false;
    for c in s.chars() {
        if in_string {
            cur.push(c);
            if c == '"' {
                in_string = false;
            }
            continue;
        }
        if in_squote {
            cur.push(c);
            if c == '\'' {
                in_squote = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_string = true;
                cur.push(c);
            },
            '\'' => {
                in_squote = true;
                cur.push(c);
            },
            '(' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            },
            ')' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            },
            ',' if depth == 0 && out.len() + 1 < max => {
                out.push(std::mem::take(&mut cur));
            },
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() || !out.is_empty() {
        out.push(cur);
    }
    out
}

fn classify_role(role: &str) -> (DeclKind, bool, bool) {
    // (kind, is_goal, is_postulate)
    match role {
        "axiom" | "hypothesis" | "definition" | "assumption" => (DeclKind::Postulate, false, true),
        "conjecture" | "negated_conjecture" | "theorem" | "lemma" | "corollary" => {
            (DeclKind::Function, true, false)
        },
        "type" => (DeclKind::Module, false, false),
        // `unknown`, `plain`, and anything unrecognised.
        _ => (DeclKind::Function, false, false),
    }
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_axiom_and_conjecture() {
        let src = "% Problem : GRP001+1\n\
                   fof(comm, axiom, ![X,Y]: mult(X,Y) = mult(Y,X)).\n\
                   fof(goal, conjecture, mult(a,b) = mult(b,a)).\n";
        let pf = parse_tptp_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("GRP001+1"));
        assert_eq!(pf.decls.len(), 2);

        let ax = pf.decls.iter().find(|d| d.name == "comm").unwrap();
        assert_eq!(ax.kind, DeclKind::Postulate);
        assert!(ax.axiom_usage.postulate);
        assert!(!ax.is_goal);
        assert!(ax.statement.contains("mult(X,Y)"));

        let goal = pf.decls.iter().find(|d| d.name == "goal").unwrap();
        assert_eq!(goal.kind, DeclKind::Function);
        assert!(goal.is_goal);
        assert!(!goal.axiom_usage.postulate);
    }

    #[test]
    fn flags_no_conjecture_on_axiom_only_file() {
        // Run through the full ingest path via a tempdir so the
        // file-level "no_conjecture" stamp is applied.
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("only_axioms.p");
        std::fs::write(
            &p,
            "fof(a1, axiom, p(a)).\n\
             fof(a2, hypothesis, q(b)).\n",
        )
        .unwrap();
        let c = ingest(dir.path()).unwrap();
        assert_eq!(c.entries.len(), 2);
        for e in &c.entries {
            assert!(
                e.axiom_usage.other.iter().any(|s| s == "no_conjecture"),
                "entry {} missing no_conjecture flag",
                e.name
            );
        }
    }

    #[test]
    fn captures_include_imports() {
        let src = "include('Axioms/SET007+0.ax').\n\
                   fof(goal, conjecture, p).\n";
        let pf = parse_tptp_file(src);
        assert_eq!(pf.imports, vec!["Axioms/SET007+0.ax".to_string()]);
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0].is_goal);
    }

    #[test]
    fn strips_line_and_block_comments() {
        let src = "% header line\n\
                   /* block\n   comment */\n\
                   fof(t, theorem, p & q).\n";
        let pf = parse_tptp_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "t");
        assert_eq!(pf.decls[0].kind, DeclKind::Function);
        assert!(pf.decls[0].is_goal);
    }

    #[test]
    fn type_role_maps_to_module_kind() {
        let src = "tff(nat_type, type, nat: $tType).\n\
                   tff(zero_type, type, zero: nat).\n\
                   tff(g, conjecture, zero = zero).\n";
        let pf = parse_tptp_file(src);
        let nat = pf.decls.iter().find(|d| d.name == "nat_type").unwrap();
        assert_eq!(nat.kind, DeclKind::Module);
        assert!(!nat.is_goal);
    }
}
