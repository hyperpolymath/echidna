// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Isabelle/HOL AFP adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.thy` file (excluding build /
//! VCS / heap caches), and extracts a structural index. Like the Agda
//! and Coq adapters this is a heuristic, not a full parser — Isabelle's
//! actual grammar is famously hairy (Pure + Isar + inner syntax + outer
//! syntax + ML antiquotations), and we only need module-level shape
//! plus hazard flags for downstream consumers.
//!
//! ## Surface forms recognised
//!
//! - Envelope: `theory X imports Y Z begin … end`. The `theory` clause
//!   gives the module name; the `imports` clause feeds `ModuleEntry::imports`.
//! - Comments: `(* … *)` block comments (nestable), `(** … **)` doc
//!   comments. Stripped to spaces before reference scanning, newlines
//!   preserved so line numbers stay aligned.
//! - Top-level declarations:
//!   * `theorem`, `lemma`, `corollary`, `proposition` → [`DeclKind::Function`].
//!     Optionally named (`lemma foo: "…"`) or anonymous (`lemma "…"`).
//!     Proof body is everything up to and including `qed` (matched at any
//!     level) or a single `by …` / `using … by …` / `done` terminator.
//!   * `definition`, `abbreviation`, `fun`, `primrec`, `function`,
//!     `type_synonym` → [`DeclKind::Function`]. Body is `where …` clause
//!     (when present) — usually short single-line.
//!   * `datatype`, `typedef` → [`DeclKind::Data`].
//!   * `record` → [`DeclKind::Record`].
//!   * `axiomatization`, `axiom` → [`DeclKind::Postulate`] (postulate
//!     hazard set).
//!   * `locale`, `class` → [`DeclKind::Function`] (no Module-like kind
//!     in the shared schema; mapping is documented at the call site).
//!   * `inductive`, `coinductive` → [`DeclKind::Data`].
//!
//! ## Hazards
//!
//! - `axiomatization`, `axiom` set `postulate`.
//! - `sorry`, `oops` set `sorry`.
//! - `consts` sets `postulate` (mild — declares a constant without a
//!   definition).
//! - `nitpick`, `quickcheck` invocations set `other` (mild — debugging
//!   tools used inside proofs).
//!
//! The hazard scan runs against the comment-stripped slice covering the
//! decl's lines, so banned tokens inside ML antiquotations or string
//! literals can still be flagged for human review.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `target`, `output`, `browser_info`,
/// `heaps`, and standard build caches regardless of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_thy(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "isabelle".to_string(),
        ..Default::default()
    };

    // Pass 1: parse each file into a draft module + draft entries.
    // Names collected here form the dependency-resolution alphabet.
    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_isabelle_file(&raw);

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
                dependencies: Vec::new(), // filled in pass 2
                axiom_usage: d.axiom_usage,
            });
        }
    }

    // Pass 2: resolve dependencies (textual; identical pattern to the
    // Agda and Coq adapters).
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

fn walk_thy(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git"
                    | "target"
                    | "output"
                    | "browser_info"
                    | "heaps"
                    | "_build"
                    | "node_modules"
                    | ".cache"
            ) {
                continue;
            }
            walk_thy(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("thy") {
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

/// Strip Isabelle comments: `(* … *)` block (nestable) and
/// `(** … **)` doc comments. Each comment byte is replaced with a
/// space; newlines are preserved so line numbers stay aligned with the
/// original file.
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
            // `(** … **)` is a doc-comment variant; we treat it the
            // same as `(* … *)` since the closing `*)` consumes both.
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

fn parse_isabelle_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();

    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    // Theory header: `theory X imports A B C begin`. The clause can
    // wrap multiple lines, so we accumulate from the first `theory`
    // line up to the `begin` keyword.
    let mut header_end_line: usize = 0;
    {
        let mut header = String::new();
        let mut started = false;
        for (idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if !started {
                if trimmed.starts_with("theory ")
                    || trimmed == "theory"
                    || trimmed.starts_with("theory\t")
                {
                    started = true;
                    header.push_str(trimmed);
                }
            } else {
                header.push(' ');
                header.push_str(trimmed);
            }
            if started
                && (trimmed.ends_with(" begin")
                    || trimmed == "begin"
                    || trimmed.contains(" begin ")
                    || trimmed.starts_with("begin "))
            {
                header_end_line = idx + 1;
                break;
            }
        }
        if !header.is_empty() {
            let (name, imports) = parse_theory_header(&header);
            pf.module_name = name;
            pf.imports = imports;
        }
    }

    // Top-level declarations.
    //
    // Isabelle's outer syntax is keyword-led: at the start of a line
    // (modulo leading whitespace) we either see a declaration keyword,
    // a proof keyword, or continuation of the previous decl. We scan
    // sequentially, recognising each keyword and gobbling the
    // declaration's "header" up to either `where` / `:` / `=` / quoted
    // statement, then for theorem-like decls also the proof body up to
    // `qed` / `done` / `oops` / single `by …` line.
    let mut i = header_end_line;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        let trimmed = line.trim_start();

        // Skip blank lines and `end` (theory terminator).
        if trimmed.is_empty() || trimmed == "end" {
            i += 1;
            continue;
        }

        // Recognise the leading keyword.
        let kw = leading_keyword(trimmed);

        match kw {
            Some(k) if is_theorem_like(k) => {
                let (consumed, decl) =
                    parse_theorem_like(&lines, &raw_lines, i, line_no, k);
                if let Some(d) = decl {
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            Some(k) if is_definition_like(k) => {
                let (consumed, decl) =
                    parse_definition_like(&lines, &raw_lines, i, line_no, k);
                if let Some(d) = decl {
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            Some(k) if is_data_like(k) => {
                let (consumed, decl) =
                    parse_data_like(&lines, &raw_lines, i, line_no, k);
                if let Some(d) = decl {
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            Some("record") => {
                let (consumed, decl) =
                    parse_data_like(&lines, &raw_lines, i, line_no, "record");
                if let Some(mut d) = decl {
                    d.kind = DeclKind::Record;
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            Some(k @ ("axiomatization" | "axiom" | "consts")) => {
                let (consumed, decl) =
                    parse_postulate_like(&lines, &raw_lines, i, line_no, k);
                if let Some(d) = decl {
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            Some(k @ ("locale" | "class")) => {
                // Module-like grouping; the shared schema has no
                // Module-like DeclKind for sub-entries (Module is
                // reserved for the file-level entry), so map to
                // Function. Document keyword in the statement.
                let (consumed, decl) =
                    parse_definition_like(&lines, &raw_lines, i, line_no, k);
                if let Some(d) = decl {
                    pf.decls.push(d);
                }
                i += consumed.max(1);
                continue;
            },
            _ => {
                i += 1;
            },
        }
    }

    pf
}

/// Parse the accumulated theory header text: `theory NAME imports A B C begin`.
fn parse_theory_header(header: &str) -> (Option<String>, Vec<String>) {
    let h = header.trim();
    let rest = match h.strip_prefix("theory") {
        Some(r) => r.trim_start(),
        None => return (None, Vec::new()),
    };
    // Name is the first whitespace-delimited token.
    let mut parts = rest.split_whitespace();
    let name = parts.next().map(|s| s.to_string());

    // Imports: everything between `imports` and `begin` (or `keywords`,
    // which we don't model further).
    let mut imports: Vec<String> = Vec::new();
    let imports_idx = h.find(" imports ");
    if let Some(start) = imports_idx {
        let after = &h[start + " imports ".len()..];
        let end = after
            .find(" begin")
            .or_else(|| after.find(" keywords "))
            .unwrap_or(after.len());
        for tok in after[..end].split_whitespace() {
            // Strip any stray punctuation.
            let t = tok.trim_matches(|c: char| !is_ident_char(c) && c != '/' && c != '"');
            // Quoted import path: `"../Foo/Bar"` — keep inner text.
            let t = t.trim_matches('"');
            if !t.is_empty() && !imports.contains(&t.to_string()) {
                imports.push(t.to_string());
            }
        }
    }

    (name, imports)
}

/// Return the leading keyword (single word) on a trimmed line, if any.
fn leading_keyword(trimmed: &str) -> Option<&str> {
    let first: &str = trimmed
        .split(|c: char| c.is_whitespace() || c == ':' || c == '(')
        .next()?;
    if first.is_empty() {
        return None;
    }
    Some(first)
}

fn is_theorem_like(kw: &str) -> bool {
    matches!(
        kw,
        "theorem" | "lemma" | "corollary" | "proposition" | "schematic_goal"
    )
}

fn is_definition_like(kw: &str) -> bool {
    matches!(
        kw,
        "definition"
            | "abbreviation"
            | "fun"
            | "primrec"
            | "function"
            | "type_synonym"
            | "termination"
    )
}

fn is_data_like(kw: &str) -> bool {
    matches!(
        kw,
        "datatype" | "typedef" | "inductive" | "coinductive" | "inductive_set"
    )
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Extract a declaration name from a header line of the form
/// `kw NAME : …` or `kw NAME = …` or `kw "…"` (anonymous → None).
fn extract_decl_name(trimmed: &str, kw: &str) -> Option<String> {
    let rest = trimmed.strip_prefix(kw)?.trim_start();
    // Anonymous: starts with `"` directly.
    if rest.starts_with('"') {
        return None;
    }
    let name: String = rest.chars().take_while(|c| is_ident_char(*c)).collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

/// Parse a theorem-like declaration starting at `lines[start]`. Returns
/// `(lines_consumed, draft)`. Body extends until a proof terminator.
fn parse_theorem_like(
    lines: &[&str],
    raw_lines: &[&str],
    start: usize,
    line_no: usize,
    kw: &str,
) -> (usize, Option<DraftDecl>) {
    let first = lines[start].trim_start();
    let name = extract_decl_name(first, kw)
        .unwrap_or_else(|| format!("<anonymous-{}-L{}>", kw, line_no));

    // Statement: accumulate lines until we see a proof opener
    // (`proof`, `by`, `apply`, `using`, `unfolding`, `including`,
    // `supply`, `note`) on its own or the start of a line. We're being
    // permissive — anything that looks like an Isar proof step.
    let mut statement = String::new();
    statement.push_str(first);
    let mut j = start + 1;
    while j < lines.len() {
        let t = lines[j].trim_start();
        if t.is_empty() {
            j += 1;
            continue;
        }
        if starts_proof_step(t) {
            break;
        }
        // Also break when a new top-level decl keyword appears.
        if let Some(k) = leading_keyword(t) {
            if is_top_level_keyword(k) {
                break;
            }
        }
        statement.push(' ');
        statement.push_str(t);
        j += 1;
    }

    // Proof body: from j up to and including a terminator.
    let mut proof = String::new();
    let mut proof_open_depth: i32 = 0;
    let mut terminated = false;
    while j < lines.len() {
        let t = lines[j].trim_start();
        if t.is_empty() {
            if !proof.is_empty() {
                proof.push(' ');
            }
            j += 1;
            continue;
        }
        if !proof.is_empty() {
            proof.push(' ');
        }
        proof.push_str(t);

        // `proof` opens a structured block; `qed` closes one. Match
        // nesting so nested proofs are absorbed.
        for tok in t.split_whitespace() {
            if tok == "proof" {
                proof_open_depth += 1;
            } else if tok == "qed" {
                proof_open_depth -= 1;
                if proof_open_depth <= 0 {
                    terminated = true;
                }
            }
        }
        // Single-step proofs: a `by …` / `done` / `..` line terminates
        // when not inside a deeper `proof` block.
        if proof_open_depth <= 0 {
            let first_tok = t.split_whitespace().next().unwrap_or("");
            if first_tok == "by"
                || first_tok == "done"
                || first_tok == ".."
                || first_tok == "."
                || first_tok == "oops"
                || first_tok == "sorry"
            {
                terminated = true;
            }
            // `using … by …` and `unfolding … by …` patterns also
            // terminate on the trailing `by`.
            if t.contains(" by ") || t.ends_with(" by") {
                if !t.starts_with("proof") {
                    terminated = true;
                }
            }
        }
        j += 1;
        if terminated {
            break;
        }
        // Guard rail: stop on a new top-level keyword that isn't a
        // proof continuation.
        if j < lines.len() {
            let next_t = lines[j].trim_start();
            if let Some(k) = leading_keyword(next_t) {
                if is_top_level_keyword(k) && !starts_proof_step(next_t) {
                    break;
                }
            }
        }
    }

    let consumed = j - start;

    let mut hz = AxiomUsage::default();
    let scan = {
        let from = line_no.saturating_sub(1);
        let to = (line_no.saturating_sub(1) + consumed).min(raw_lines.len());
        raw_lines[from..to].join("\n")
    };
    flag_hazards(&scan, &mut hz);

    (
        consumed,
        Some(DraftDecl {
            name,
            kind: DeclKind::Function,
            statement: normalise_ws(&statement),
            proof: if proof.trim().is_empty() {
                None
            } else {
                Some(normalise_ws(&proof))
            },
            line: line_no,
            axiom_usage: hz,
        }),
    )
}

fn starts_proof_step(t: &str) -> bool {
    let first = t.split_whitespace().next().unwrap_or("");
    matches!(
        first,
        "proof"
            | "by"
            | "apply"
            | "using"
            | "unfolding"
            | "including"
            | "supply"
            | "note"
            | "done"
            | "sorry"
            | "oops"
            | "qed"
            | "show"
            | "have"
            | "obtain"
            | "then"
            | "thus"
            | "hence"
            | "moreover"
            | "ultimately"
            | "next"
            | "fix"
            | "assume"
            | "case"
            | "let"
            | "{"
            | "}"
    )
}

fn is_top_level_keyword(kw: &str) -> bool {
    is_theorem_like(kw)
        || is_definition_like(kw)
        || is_data_like(kw)
        || matches!(
            kw,
            "record"
                | "axiomatization"
                | "axiom"
                | "consts"
                | "locale"
                | "class"
                | "instantiation"
                | "interpretation"
                | "end"
                | "theory"
        )
}

/// Parse a definition-like decl: gobble until next top-level keyword
/// or blank-line + top-level keyword. Body, if present, lives after a
/// `where` clause or `=` (for `abbreviation`).
fn parse_definition_like(
    lines: &[&str],
    raw_lines: &[&str],
    start: usize,
    line_no: usize,
    kw: &str,
) -> (usize, Option<DraftDecl>) {
    let first = lines[start].trim_start();
    let name = match extract_decl_name(first, kw) {
        Some(n) => n,
        None => return (1, None),
    };

    let mut statement = String::from(first);
    let mut j = start + 1;
    while j < lines.len() {
        let t = lines[j].trim_start();
        if t.is_empty() {
            j += 1;
            break;
        }
        if let Some(k) = leading_keyword(t) {
            if is_top_level_keyword(k) {
                break;
            }
        }
        statement.push(' ');
        statement.push_str(t);
        j += 1;
    }

    let consumed = j - start;
    let mut hz = AxiomUsage::default();
    let scan = {
        let from = line_no.saturating_sub(1);
        let to = (line_no.saturating_sub(1) + consumed).min(raw_lines.len());
        raw_lines[from..to].join("\n")
    };
    flag_hazards(&scan, &mut hz);

    (
        consumed,
        Some(DraftDecl {
            name,
            kind: DeclKind::Function,
            statement: normalise_ws(&statement),
            proof: None,
            line: line_no,
            axiom_usage: hz,
        }),
    )
}

/// Parse a data-like decl (datatype / typedef / inductive). Same
/// gobble strategy as definitions.
fn parse_data_like(
    lines: &[&str],
    raw_lines: &[&str],
    start: usize,
    line_no: usize,
    kw: &str,
) -> (usize, Option<DraftDecl>) {
    let first = lines[start].trim_start();
    let name = match extract_decl_name(first, kw) {
        Some(n) => n,
        None => return (1, None),
    };

    let mut statement = String::from(first);
    let mut j = start + 1;
    while j < lines.len() {
        let t = lines[j].trim_start();
        if t.is_empty() {
            j += 1;
            break;
        }
        if let Some(k) = leading_keyword(t) {
            if is_top_level_keyword(k) {
                break;
            }
        }
        statement.push(' ');
        statement.push_str(t);
        j += 1;
    }

    let consumed = j - start;
    let mut hz = AxiomUsage::default();
    let scan = {
        let from = line_no.saturating_sub(1);
        let to = (line_no.saturating_sub(1) + consumed).min(raw_lines.len());
        raw_lines[from..to].join("\n")
    };
    flag_hazards(&scan, &mut hz);

    (
        consumed,
        Some(DraftDecl {
            name,
            kind: DeclKind::Data,
            statement: normalise_ws(&statement),
            proof: None,
            line: line_no,
            axiom_usage: hz,
        }),
    )
}

/// Parse an axiomatization/axiom/consts block. May span multiple lines
/// with indented `name : ty` entries. We emit one DraftDecl per name
/// found; if none, fall back to one anonymous decl for the block.
fn parse_postulate_like(
    lines: &[&str],
    raw_lines: &[&str],
    start: usize,
    line_no: usize,
    kw: &str,
) -> (usize, Option<DraftDecl>) {
    let first = lines[start].trim_start();
    // For a single-line `axiom foo : "…"`, treat as one decl.
    let header_name = extract_decl_name(first, kw);

    // Accumulate block text up to next top-level keyword.
    let mut block = String::from(first);
    let mut j = start + 1;
    while j < lines.len() {
        let t = lines[j].trim_start();
        if t.is_empty() {
            j += 1;
            break;
        }
        if let Some(k) = leading_keyword(t) {
            if is_top_level_keyword(k) {
                break;
            }
        }
        block.push(' ');
        block.push_str(t);
        j += 1;
    }
    let consumed = j - start;

    let scan = {
        let from = line_no.saturating_sub(1);
        let to = (line_no.saturating_sub(1) + consumed).min(raw_lines.len());
        raw_lines[from..to].join("\n")
    };
    let mut hz = AxiomUsage {
        postulate: true,
        ..Default::default()
    };
    flag_hazards(&scan, &mut hz);

    let name = header_name.unwrap_or_else(|| format!("<{}-block-L{}>", kw, line_no));

    (
        consumed,
        Some(DraftDecl {
            name,
            kind: DeclKind::Postulate,
            statement: normalise_ws(&block),
            proof: None,
            line: line_no,
            axiom_usage: hz,
        }),
    )
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Tokenise on whitespace and Isabelle outer-syntax separators.
/// Isabelle identifiers are alphanumeric + `_` + `'` (apostrophe);
/// inner-syntax punctuation like `=>` and `==>` we treat as separators.
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
                    | '"'
                    | '?'
                    | '!'
                    | '|'
                    | '\\'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("axiomatization") || text.contains("axiom ") {
        hz.postulate = true;
    }
    if text.contains("sorry") {
        hz.sorry = true;
    }
    if text.contains("oops") {
        // Treat `oops` as sorry-class (proof abandoned, theorem
        // remains as named hypothesis).
        hz.sorry = true;
    }
    if text.contains("consts ") {
        // Mild postulate hazard — `consts` declares without defining.
        hz.postulate = true;
    }
    if text.contains("nitpick") && !hz.other.iter().any(|s| s == "nitpick") {
        hz.other.push("nitpick".to_string());
    }
    if text.contains("quickcheck") && !hz.other.iter().any(|s| s == "quickcheck") {
        hz.other.push("quickcheck".to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note on fixtures: don't use Rust line-continuation (`\\\n`) for
    // source — use explicit `\n` so indentation is preserved.

    #[test]
    fn parses_theory_header_and_simple_lemma() {
        let src = "theory Smoke\n  imports Main\nbegin\n\n\
                   definition foo :: \"nat \\<Rightarrow> nat\" where\n  \"foo n = n + 1\"\n\n\
                   lemma foo_id: \"foo 0 = 1\"\n  by (simp add: foo_def)\n\n\
                   end\n";
        let pf = parse_isabelle_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("Smoke"));
        assert!(
            pf.imports.iter().any(|m| m == "Main"),
            "imports missing Main: {:?}",
            pf.imports
        );
        let names: Vec<&str> = pf.decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"foo"), "decls missing foo: {:?}", names);
        assert!(
            names.contains(&"foo_id"),
            "decls missing foo_id: {:?}",
            names
        );
        let foo_id = pf.decls.iter().find(|d| d.name == "foo_id").unwrap();
        assert_eq!(foo_id.kind, DeclKind::Function);
        let body = foo_id.proof.as_deref().unwrap_or("");
        assert!(
            body.contains("simp") || body.contains("by"),
            "proof body missing tactic: {}",
            body
        );
        assert!(!foo_id.axiom_usage.any());
    }

    #[test]
    fn detects_sorry_hazard() {
        let src = "theory Hazard\n  imports Main\nbegin\n\n\
                   lemma still_todo: \"P \\<longrightarrow> P\"\n  sorry\n\n\
                   end\n";
        let pf = parse_isabelle_file(src);
        let lemma = pf
            .decls
            .iter()
            .find(|d| d.name == "still_todo")
            .expect("lemma not parsed");
        assert!(
            lemma.axiom_usage.sorry,
            "sorry hazard not flagged on {:?}",
            lemma
        );
    }

    #[test]
    fn detects_axiomatization_and_datatype() {
        let src = "theory Mix\n  imports Main\nbegin\n\n\
                   datatype tree = Leaf | Node tree tree\n\n\
                   axiomatization where bogus: \"True\"\n\n\
                   end\n";
        let pf = parse_isabelle_file(src);
        let tree = pf.decls.iter().find(|d| d.name == "tree");
        assert!(tree.is_some(), "datatype tree not parsed: {:?}", pf.decls);
        assert_eq!(tree.unwrap().kind, DeclKind::Data);
        let axiom_block = pf.decls.iter().find(|d| d.kind == DeclKind::Postulate);
        assert!(
            axiom_block.is_some(),
            "axiomatization block not flagged: {:?}",
            pf.decls
        );
        assert!(axiom_block.unwrap().axiom_usage.postulate);
    }
}
