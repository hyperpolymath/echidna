// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Ada / SPARK adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.ads` (spec) and `*.adb` (body)
//! file (excluding `.git`, `target`, `obj`, `lib`, `b~`, `gnatprove`),
//! and extracts a structural index.
//!
//! Ada/SPARK is one of the estate's two standard TCB languages, and
//! `ZigProve`'s obligation model is shaped after SPARK's, so this is the
//! adapter whose vocabulary the rest of the trust pipeline is written
//! in. The interesting cases are not "is there a procedure" but "what
//! did the contract say, and was any of it *assumed* rather than
//! proved".
//!
//! What we recognise:
//! - `package P is`, `package body P is` (dotted names included) — the
//!   module and its unit name.
//! - `with A.B;` / `use A.B;` / `limited with A.B;` / `private with`
//!   — imports.
//! - `procedure N (...)`, `function N (...)`, `overriding` forms,
//!   `generic` subprograms, and nested declarations.
//! - `type T is ...`, `subtype S is ...`, `task T`, `protected T`.
//! - Contract aspects: `Pre`, `Post`, `Contract_Cases`,
//!   `Loop_Invariant`, `Loop_Variant`, `Global`, `Depends`,
//!   `SPARK_Mode`, `Ghost`, `Always_Terminates`, `Subprogram_Variant`.
//! - GNATprove / sparklib lemma convention: a `Ghost` procedure named
//!   `Lemma_*` (or `Lemma_*` with a `Post` of `True`), which is how
//!   `sparklib` encodes reusable lemmas. Recorded as
//!   `sparklib:lemma` in `AxiomUsage::other` so the training pipeline
//!   can tell a reusable lemma from an executable subprogram.
//!
//! Hazards (GNATprove's escape hatches — flagged for human review):
//! - `pragma Assume` and the old `--# assume` comment form. Both are
//!   mapped to `AxiomUsage::postulate`: GNATprove accepts the predicate
//!   without proof, which is exactly the semantics of a postulate.
//! - `pragma Annotate (GNATprove, ...)` with `Skip_Proof` /
//!   `Proved => False` / `Check => Disable` — proof obligations switched
//!   off in source.
//! - `pragma Suppress (...)` — runtime checks removed.
//! - `Unchecked_Conversion` / `Unchecked_Deallocation` — the type system
//!   is bypassed at the boundary.
//! - `pragma Import` / `pragma Interface` — the body is trusted, not
//!   proved (`spark:trusted_import`). This is the estate's Zig FFI edge,
//!   so it is tagged rather than banned.
//! - `SPARK_Mode => Off` — the unit is outside the proved subset.
//!
//! ## Heuristics (not a parser)
//!
//! Ada is indentation-insensitive and `end` is heavily overloaded, so
//! subprogram bodies are delimited by the first `end <Name>;` after the
//! body's `is`, and a declaration terminates at the first depth-0 `;`
//! (spec only) or `is` (spec + body). Comments are blanked before
//! structural scanning — but the *original* text is what lands in
//! `statement` / `proof`, so `--#` annotations stay visible to hazard
//! detection and to the discipline detector.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus from every Ada/SPARK unit.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_ada(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "spark_ada".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_ada_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed.unit.clone().unwrap_or_else(|| {
            rel.with_extension("")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(".")
        });
        corpus.modules.push(ModuleEntry {
            name: module_name,
            path: rel,
            options: parsed.options.clone(),
            imports: parsed.imports.clone(),
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

    // A unit's contract lives in the `.ads` and its proof in the `.adb`,
    // so pair them across files before anything indexes the entries.
    merge_cross_file(&mut corpus);

    // Pass 2: textual dependency resolution over the whole project.
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
            if tok.eq_ignore_ascii_case(&own_name) || tok == own_qualified {
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

fn walk_ada(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "obj" | "lib" | "gnatprove" | "node_modules" | ".cache"
            ) {
                continue;
            }
            walk_ada(&p, out)?;
        } else if let Some(ext) = p.extension().and_then(|s| s.to_str()) {
            if ext.eq_ignore_ascii_case("ads") || ext.eq_ignore_ascii_case("adb") {
                out.push(p);
            }
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
pub(crate) struct ParsedFile {
    pub(crate) unit: Option<String>,
    pub(crate) options: Vec<String>,
    pub(crate) imports: Vec<String>,
    pub(crate) decls: Vec<DraftDecl>,
}

#[derive(Debug)]
pub(crate) struct DraftDecl {
    pub(crate) name: String,
    pub(crate) kind: DeclKind,
    pub(crate) statement: String,
    pub(crate) proof: Option<String>,
    pub(crate) line: usize,
    pub(crate) axiom_usage: AxiomUsage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokKind {
    Ident,
    Number,
    Str,
    Punct,
}

#[derive(Debug)]
struct Tok {
    kind: TokKind,
    /// Original spelling (preserves case for statements).
    text: String,
    /// Lowercased copy for keyword comparison.
    lower: String,
    start: usize,
    end: usize,
}

/// Blank out comments and string/char contents, preserving byte offsets
/// and newlines so `clean[i..j]` and `orig[i..j]` describe the same
/// region of the source.
fn clean_source(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = bytes.to_vec();
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            while i < bytes.len() && bytes[i] != b'\n' {
                out[i] = b' ';
                i += 1;
            }
        } else if bytes[i] == b'"' {
            // Keep the quotes, blank the payload. Ada escapes a quote by
            // doubling it.
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'"' {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                        out[i] = b' ';
                        out[i + 1] = b' ';
                        i += 2;
                        continue;
                    }
                    break;
                }
                if bytes[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
            i += 1;
        } else if bytes[i] == b'\'' {
            // Character literal `'a'` or an attribute tick (`X'Length`).
            // Only blank the quoted form; a tick before an identifier is
            // an attribute and must survive.
            if i + 2 < bytes.len() && bytes[i + 2] == b'\'' {
                out[i + 1] = b' ';
                i += 3;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn tokenise(clean: &str) -> Vec<Tok> {
    let bytes = clean.as_bytes();
    let mut toks: Vec<Tok> = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' {
            while i < bytes.len() {
                let d = bytes[i] as char;
                if d.is_ascii_alphanumeric() || d == '_' {
                    i += 1;
                } else {
                    break;
                }
            }
            let text = clean[start..i].to_string();
            toks.push(Tok {
                kind: TokKind::Ident,
                lower: text.to_ascii_lowercase(),
                text,
                start,
                end: i,
            });
        } else if c.is_ascii_digit() {
            while i < bytes.len() {
                let d = bytes[i] as char;
                if d.is_ascii_alphanumeric() || d == '_' || d == '#' || d == '.' {
                    i += 1;
                } else {
                    break;
                }
            }
            let text = clean[start..i].to_string();
            toks.push(Tok {
                kind: TokKind::Number,
                lower: text.to_ascii_lowercase(),
                text,
                start,
                end: i,
            });
        } else if c == '"' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                i += 1;
            }
            i = (i + 1).min(bytes.len());
            let text = clean[start..i].to_string();
            toks.push(Tok {
                kind: TokKind::Str,
                lower: text.to_ascii_lowercase(),
                text,
                start,
                end: i,
            });
        } else {
            i += 1;
            let text = clean[start..i].to_string();
            toks.push(Tok {
                kind: TokKind::Punct,
                lower: text.clone(),
                text,
                start,
                end: i,
            });
        }
    }
    toks
}

fn line_of(src: &str, offset: usize) -> usize {
    src[..offset.min(src.len())].bytes().filter(|b| *b == b'\n').count() + 1
}

fn is_kw(tok: &Tok, kw: &str) -> bool {
    tok.kind == TokKind::Ident && tok.lower == kw
}

fn is_punct(tok: &Tok, p: &str) -> bool {
    tok.kind == TokKind::Punct && tok.text == p
}

/// Read a dotted name starting at `i` (`A`, `A.B`, `A.B.C`).
/// Returns the dotted spelling and the index just past it.
fn dotted_name(toks: &[Tok], i: usize) -> Option<(String, usize)> {
    if i >= toks.len() || toks[i].kind != TokKind::Ident {
        return None;
    }
    let mut name = toks[i].text.clone();
    let mut j = i + 1;
    while j + 1 < toks.len() && is_punct(&toks[j], ".") && toks[j + 1].kind == TokKind::Ident {
        name.push('.');
        name.push_str(&toks[j + 1].text);
        j += 2;
    }
    Some((name, j))
}

/// Parse one Ada source file into unit metadata plus draft declarations.
pub(crate) fn parse_ada_file(src: &str) -> ParsedFile {
    let clean = clean_source(src);
    let toks = tokenise(&clean);
    let mut parsed = ParsedFile::default();

    // Unit name: `package [body] A.B is`.
    let mut i = 0;
    while i < toks.len() {
        if is_kw(&toks[i], "package") {
            let mut j = i + 1;
            if j < toks.len() && is_kw(&toks[j], "body") {
                j += 1;
            }
            if let Some((name, next)) = dotted_name(&toks, j) {
                // `package P is` or `package P with SPARK_Mode is`.
                let mut at = next;
                if at < toks.len() && is_kw(&toks[at], "with") {
                    while at < toks.len() && !is_kw(&toks[at], "is") && !is_punct(&toks[at], ";") {
                        at += 1;
                    }
                }
                if at < toks.len() && is_kw(&toks[at], "is") && parsed.unit.is_none() {
                    parsed.unit = Some(name);
                    if has_pragma(&toks, "spark_mode") {
                        parsed.options.push("SPARK_Mode".to_string());
                    }
                }
            }
        }
        i += 1;
    }

    parsed.imports = collect_imports(&toks);

    // Declarations.
    let mut k = 0;
    while k < toks.len() {
        let mut kind = None;
        let mut name_idx = k + 1;
        let mut allows_body = false;
        if is_kw(&toks[k], "procedure") || is_kw(&toks[k], "function") {
            // `type Cb is access procedure (...)` is a type, not a decl.
            if k > 0 && is_kw(&toks[k - 1], "access") {
                k += 1;
                continue;
            }
            kind = Some(DeclKind::Function);
            allows_body = true;
        } else if is_kw(&toks[k], "type") || is_kw(&toks[k], "subtype") {
            kind = Some(DeclKind::Data);
        } else if is_kw(&toks[k], "task") || is_kw(&toks[k], "protected") {
            kind = Some(DeclKind::Record);
            if name_idx < toks.len() && is_kw(&toks[name_idx], "body") {
                name_idx += 1;
            }
            if name_idx < toks.len() && is_kw(&toks[name_idx], "type") {
                name_idx += 1;
            }
        }
        let Some(kind) = kind else {
            k += 1;
            continue;
        };
        if name_idx >= toks.len() || toks[name_idx].kind != TokKind::Ident {
            k += 1;
            continue;
        }
        // `end Name;` and `for Name'Size` are not declarations.
        if k > 0 && is_kw(&toks[k - 1], "end") {
            k += 1;
            continue;
        }

        let name = toks[name_idx].text.clone();
        let (spec_end, body_start) = decl_extent(&toks, name_idx, allows_body);
        if spec_end <= name_idx {
            k += 1;
            continue;
        }
        let statement = normalise_ws(&src[toks[k].start..toks[spec_end].start]);

        let mut proof = None;
        let mut advance = spec_end;
        if let Some(bs) = body_start {
            let body_end = body_end_idx(&toks, bs, &name);
            let body_text = match body_end {
                Some(e) => &src[toks[bs].start..toks[e].start],
                None => &src[toks[bs].start..],
            };
            proof = Some(body_text.trim().to_string());
            advance = body_end.unwrap_or(bs);
        }

        let mut axiom_usage = AxiomUsage::default();
        flag_spark_hazards(&statement, &mut axiom_usage);
        if let Some(p) = &proof {
            flag_spark_hazards(p, &mut axiom_usage);
        }
        flag_spark_aspects(&statement, &name, &mut axiom_usage);

        parsed.decls.push(DraftDecl {
            name,
            kind,
            statement,
            proof,
            line: line_of(src, toks[k].start),
            axiom_usage,
        });

        k = advance.max(k + 1);
    }

    if !parsed.decls.is_empty() && !parsed.options.iter().any(|o| o == "SPARK_Mode") {
        let has_contract = parsed.decls.iter().any(|d| {
            d.statement.contains("Pre =>")
                || d.statement.contains("Post =>")
                || d.statement.contains("Contract_Cases")
                || d.statement.contains("Loop_Invariant")
        });
        if has_contract {
            parsed.options.push("SPARK".to_string());
        }
    }

    // `--#` annotations and file-level pragmas sit outside the spec/body
    // spans we slice, so attribute them to the nearest declaration.
    apply_out_of_decl_hazards(src, &mut parsed.decls);

    // A SPARK subprogram normally appears twice: the contract in the
    // spec file and the body in the `.adb`. Emitting both would give two
    // entries with the same qualified name, so pair them up — the spec
    // contributes the contract, the body contributes the proof.
    merge_spec_and_body(&mut parsed.decls);

    parsed
}

/// Pair each spec-only entry with the single body entry that shares its
/// qualified name. Unambiguous pairs only: Ada overloading means a name
/// match is not a declaration match in general.
fn merge_cross_file(corpus: &mut Corpus) {
    let n = corpus.entries.len();
    let mut drop_flags: Vec<bool> = vec![false; n];
    for i in 0..n {
        if corpus.entries[i].proof.is_some() || drop_flags[i] {
            continue;
        }
        let qualified = corpus.entries[i].qualified.clone();
        let mut body: Option<usize> = None;
        let mut bodies = 0usize;
        for (j, entry) in corpus.entries.iter().enumerate() {
            if j == i {
                continue;
            }
            if entry.qualified == qualified && entry.proof.is_some() {
                bodies += 1;
                body = Some(j);
            }
        }
        if bodies != 1 {
            continue;
        }
        let Some(b) = body else { continue };
        if drop_flags[b] {
            continue;
        }
        let statement = corpus.entries[i].statement.clone();
        let line = corpus.entries[i].line;
        let usage = corpus.entries[i].axiom_usage.clone();
        corpus.entries[b].statement = statement;
        corpus.entries[b].line = line;
        for tag in &usage.other {
            push_once(&mut corpus.entries[b].axiom_usage.other, tag);
        }
        corpus.entries[b].axiom_usage.postulate |= usage.postulate;
        drop_flags[i] = true;
    }
    if !drop_flags.iter().any(|d| *d) {
        return;
    }

    let mut remap: Vec<Option<usize>> = Vec::with_capacity(n);
    let mut next = 0usize;
    for dropped in &drop_flags {
        if *dropped {
            remap.push(None);
        } else {
            remap.push(Some(next));
            next += 1;
        }
    }

    let mut kept: Vec<CorpusEntry> = Vec::with_capacity(next);
    for (i, entry) in corpus.entries.drain(..).enumerate() {
        if remap[i].is_some() {
            kept.push(entry);
        }
    }
    corpus.entries = kept;

    for module in corpus.modules.iter_mut() {
        let entries: Vec<usize> = module.entries.iter().filter_map(|i| remap[*i]).collect();
        module.entries = entries;
    }
}

/// Attribute hazards that live outside any declaration span (the
/// `--# assume` comment form, a trailing `pragma Import`) to the nearest
/// preceding declaration, falling back to the first one.
fn apply_out_of_decl_hazards(src: &str, decls: &mut [DraftDecl]) {
    if decls.is_empty() {
        return;
    }
    for (i, line) in src.lines().enumerate() {
        let lower = line.to_ascii_lowercase();
        let trimmed = line.trim_start();
        // A prose comment explaining an escape hatch is not an escape
        // hatch. Only the `--#` annotation form counts.
        if trimmed.starts_with("--") && !lower.contains("--#") {
            continue;
        }
        let comment_assume = lower.contains("--#") && lower.contains("assume");
        let pragma = lower.contains("pragma ")
            && (lower.contains("import")
                || lower.contains("interface")
                || lower.contains("suppress")
                || lower.contains("machine_attribute")
                || lower.contains("assume")
                || (lower.contains("annotate")
                    && (lower.contains("skip_proof")
                        || lower.contains("proved => false")
                        || lower.contains("check => disable"))));
        if !comment_assume && !pragma {
            continue;
        }
        let ln = i + 1;
        let mut target = 0usize;
        for (idx, d) in decls.iter().enumerate() {
            if d.line <= ln {
                target = idx;
            }
        }
        let mut usage = AxiomUsage::default();
        flag_spark_hazards(line, &mut usage);
        if comment_assume && !usage.postulate {
            usage.postulate = true;
            push_once(&mut usage.other, "spark:pragma_assume");
        }
        for tag in usage.other {
            push_once(&mut decls[target].axiom_usage.other, &tag);
        }
        if usage.postulate {
            decls[target].axiom_usage.postulate = true;
        }
    }
}

/// Collapse `procedure P ... with Pre => ...;` plus `procedure P ... is
/// begin ... end P;` into a single entry. Only pairs that are
/// unambiguous (exactly one spec without a body and one body for that
/// name) are merged, because Ada overloading makes a name-only match
/// unsound in general.
fn merge_spec_and_body(decls: &mut Vec<DraftDecl>) {
    let mut names: Vec<String> = Vec::new();
    for d in decls.iter() {
        if !names.contains(&d.name) {
            names.push(d.name.clone());
        }
    }
    let mut drop_idx: Vec<usize> = Vec::new();
    for name in names {
        let specs: Vec<usize> = decls
            .iter()
            .enumerate()
            .filter(|(_, d)| d.name == name && d.proof.is_none())
            .map(|(i, _)| i)
            .collect();
        let bodies: Vec<usize> = decls
            .iter()
            .enumerate()
            .filter(|(_, d)| d.name == name && d.proof.is_some())
            .map(|(i, _)| i)
            .collect();
        if specs.len() != 1 || bodies.len() != 1 {
            continue;
        }
        let spec = specs[0];
        let body = bodies[0];
        let statement = decls[spec].statement.clone();
        let line = decls[spec].line;
        let mut usage = decls[spec].axiom_usage.clone();
        for tag in &decls[body].axiom_usage.other {
            push_once(&mut usage.other, tag);
        }
        let b = &decls[body].axiom_usage;
        usage.postulate |= b.postulate;
        usage.believe_me |= b.believe_me;
        usage.assert_total |= b.assert_total;
        usage.admitted |= b.admitted;
        usage.sorry |= b.sorry;
        usage.trustme |= b.trustme;
        decls[body].statement = statement;
        decls[body].line = line;
        decls[body].axiom_usage = usage;
        drop_idx.push(spec);
    }
    drop_idx.sort_unstable();
    for i in drop_idx.into_iter().rev() {
        decls.remove(i);
    }
}

/// True when the file sets `name` either as a pragma (`pragma X`) or as
/// an aspect (`with X`), since SPARK spells most things as aspects.
fn has_pragma(toks: &[Tok], name: &str) -> bool {
    toks.windows(2)
        .any(|w| (is_kw(&w[0], "pragma") || is_kw(&w[0], "with")) && is_kw(&w[1], name))
}

/// Collect `with` / `use` / `limited with` clause unit names.
///
/// A clause may list several units (`with A, B.C;`). An aspect
/// (`with Pre => ...`) is rejected by requiring the list to terminate
/// with `;`.
fn collect_imports(toks: &[Tok]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        if !(is_kw(&toks[i], "with") || is_kw(&toks[i], "use")) {
            i += 1;
            continue;
        }
        let mut names: Vec<String> = Vec::new();
        let mut j = i + 1;
        let mut terminated = false;
        loop {
            let Some((name, next)) = dotted_name(&toks, j) else {
                break;
            };
            names.push(name);
            if next < toks.len() && is_punct(&toks[next], ",") {
                j = next + 1;
                continue;
            }
            terminated = next < toks.len() && is_punct(&toks[next], ";");
            break;
        }
        if terminated {
            for name in names {
                if !out.contains(&name) {
                    out.push(name);
                }
            }
        }
        i += 1;
    }
    out
}

/// From the declaration name at `name_idx`, find the end of the spec
/// (index of the terminating `;`) or of the spec-and-`is` of a body.
/// Returns `(spec_end, body_start)` where `body_start` is the index just
/// past `is` when a body follows.
fn decl_extent(toks: &[Tok], name_idx: usize, allows_body: bool) -> (usize, Option<usize>) {
    let mut depth = 0i32;
    let mut j = name_idx;
    while j < toks.len() {
        let t = &toks[j];
        if is_punct(t, "(") {
            depth += 1;
        } else if is_punct(t, ")") {
            depth -= 1;
            if depth < 0 {
                return (j, None);
            }
        } else if depth == 0 && is_punct(t, ";") {
            return (j, None);
        } else if depth == 0 && is_kw(t, "is") && allows_body {
            return (j, Some(j + 1));
        } else if depth == 0 && is_kw(t, "renames") {
            return (j, None);
        }
        j += 1;
    }
    (toks.len(), None)
}

/// End of a subprogram body: the first `end <name>` after the body's
/// `is`, or — for expression functions (`is (X * Y)`) which have no
/// `end` — the first depth-0 `;`.
fn body_end_idx(toks: &[Tok], from: usize, name: &str) -> Option<usize> {
    if let Some(e) = find_end_name(toks, from, name) {
        return Some(e);
    }
    let mut depth = 0i32;
    let mut j = from;
    while j < toks.len() {
        if is_punct(&toks[j], "(") {
            depth += 1;
        } else if is_punct(&toks[j], ")") {
            depth -= 1;
        } else if depth == 0 && is_punct(&toks[j], ";") {
            return Some(j);
        }
        j += 1;
    }
    None
}

/// First `end <name>` at or after `from`, returning the index of `end`.
fn find_end_name(toks: &[Tok], from: usize, name: &str) -> Option<usize> {
    let mut j = from;
    while j + 1 < toks.len() {
        if is_kw(&toks[j], "end") && toks[j + 1].kind == TokKind::Ident {
            if toks[j + 1].text.eq_ignore_ascii_case(name) {
                return Some(j);
            }
        }
        j += 1;
    }
    None
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\'' || c == '.'))
        .filter(|t| !t.is_empty())
        .collect()
}

/// GNATprove escape hatches. `pragma Assume` maps to `postulate`
/// because the tool accepts the predicate without discharging it.
fn flag_spark_hazards(text: &str, hz: &mut AxiomUsage) {
    let lower = text.to_ascii_lowercase();
    if lower.contains("pragma assume") || lower.contains("--# assume") {
        hz.postulate = true;
        push_once(&mut hz.other, "spark:pragma_assume");
    }
    if lower.contains("pragma annotate") {
        let disables = lower.contains("skip_proof")
            || lower.contains("proved => false")
            || lower.contains("check => disable");
        if disables {
            push_once(&mut hz.other, "spark:proof_disabled");
        }
    }
    if lower.contains("pragma suppress") {
        push_once(&mut hz.other, "spark:checks_suppressed");
    }
    if lower.contains("unchecked_conversion") {
        push_once(&mut hz.other, "spark:unchecked_conversion");
    }
    if lower.contains("unchecked_deallocation") {
        push_once(&mut hz.other, "spark:unchecked_deallocation");
    }
    if lower.contains("pragma import") || lower.contains("pragma interface") {
        push_once(&mut hz.other, "spark:trusted_import");
    }
    if lower.contains("pragma machine_attribute") {
        push_once(&mut hz.other, "spark:machine_attribute");
    }
}

/// Aspects worth carrying into the hazard summary: they say something
/// about *where* the proof boundary sits, not just that there is one.
fn flag_spark_aspects(statement: &str, name: &str, hz: &mut AxiomUsage) {
    let lower = statement.to_ascii_lowercase();
    if lower.contains("ghost") {
        push_once(&mut hz.other, "spark:ghost");
        let is_lemma = name.to_ascii_lowercase().starts_with("lemma");
        if is_lemma {
            push_once(&mut hz.other, "sparklib:lemma");
        }
    }
    if lower.contains("spark_mode") && lower.contains("off") {
        push_once(&mut hz.other, "spark:spark_mode_off");
    }
    if lower.contains("always_terminates") {
        push_once(&mut hz.other, "spark:always_terminates");
    }
    if lower.contains("contract_cases") {
        push_once(&mut hz.other, "spark:contract_cases");
    }
    if lower.contains("loop_invariant") {
        push_once(&mut hz.other, "spark:loop_invariant");
    }
    if lower.contains("depends =>") || lower.contains("global =>") {
        push_once(&mut hz.other, "spark:flow_contract");
    }
}

fn push_once(v: &mut Vec<String>, item: &str) {
    if !v.iter().any(|s| s == item) {
        v.push(item.to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPARKLIB: &str = r#"
package SPARK_Utils with SPARK_Mode is

   function Mult_Comm (X, Y : Integer) return Boolean is (X * Y = Y * X);

   procedure Lemma_Mult_Comm (X, Y : Integer)
     with Ghost,
          Pre  => X in Integer'First .. Integer'Last,
          Post => Mult_Comm (X, Y);

end SPARK_Utils;
"#;

    const SPLIT_UNIT_SPEC: &str = r#"
package CPU.Divide with SPARK_Mode is
   procedure Divide (N, D : Integer; R : out Integer)
     with Pre  => D /= 0,
          Post => R = N / D;
end CPU.Divide;
"#;

    const SPLIT_UNIT_BODY: &str = r#"
package body CPU.Divide with SPARK_Mode is
   procedure Divide (N, D : Integer; R : out Integer) is
   begin
      R := N / D;
   end Divide;
end CPU.Divide;
"#;

    fn parse(src: &str) -> ParsedFile {
        parse_ada_file(src)
    }

    #[test]
    fn extracts_unit_name_and_imports() {
        let src = "\
with Ada.Text_IO, Interfaces;
use Interfaces;
limited with System.Storage_Elements;
package CPU.Layout is
   type Offset is mod 2 ** 32;
end CPU.Layout;
";
        let p = parse(src);
        assert_eq!(p.unit.as_deref(), Some("CPU.Layout"));
        assert!(p.imports.contains(&"Ada.Text_IO".to_string()));
        assert!(p.imports.contains(&"Interfaces".to_string()));
        assert!(p.imports.contains(&"System.Storage_Elements".to_string()));
        assert_eq!(p.decls.len(), 1);
        assert_eq!(p.decls[0].name, "Offset");
    }

    #[test]
    fn captures_pre_and_post_aspects() {
        let p = parse(SPARKLIB);
        let lemma = p
            .decls
            .iter()
            .find(|d| d.name == "Lemma_Mult_Comm")
            .expect("lemma");
        assert!(lemma.statement.contains("Pre => X in Integer'First"));
        assert!(lemma.statement.contains("Post => Mult_Comm (X, Y)"));
        assert!(lemma.statement.contains("Ghost"));
    }

    #[test]
    fn expression_function_body_is_captured() {
        let p = parse(SPARKLIB);
        let f = p
            .decls
            .iter()
            .find(|d| d.name == "Mult_Comm")
            .expect("Mult_Comm");
        assert_eq!(f.proof.as_deref(), Some("(X * Y = Y * X)"));
    }

    #[test]
    fn spec_and_body_merge_into_one_entry() {
        let spec = parse(SPLIT_UNIT_SPEC);
        let mut decls = spec.decls;
        let mut body = parse(SPLIT_UNIT_BODY).decls;
        decls.append(&mut body);
        merge_spec_and_body(&mut decls);
        let divide: Vec<&DraftDecl> = decls.iter().filter(|d| d.name == "Divide").collect();
        assert_eq!(divide.len(), 1, "spec and body must collapse to one entry");
        assert!(divide[0].statement.contains("Post => R = N / D"));
        assert!(divide[0].proof.as_deref().unwrap().contains("R := N / D;"));
    }

    #[test]
    fn flags_pragma_assume_as_postulate() {
        let src = r#"
package body Opaque is
   procedure Trust (X : Integer) with Post => X = X is
      pragma Assume (X > 0);
   begin
      null;
   end Trust;
end Opaque;
"#;
        let p = parse(src);
        let d = p.decls.iter().find(|d| d.name == "Trust").unwrap();
        assert!(d.axiom_usage.postulate, "pragma Assume must be a postulate");
        assert!(d
            .axiom_usage
            .other
            .iter()
            .any(|t| t == "spark:pragma_assume"));
    }

    #[test]
    fn old_style_comment_assume_is_also_a_hazard() {
        let src = "\
package Opaque is
   procedure P (X : Integer) with Pre => X > 0;
   --# assume X in 1 .. 100;
end Opaque;
";
        let p = parse(src);
        let d = p.decls.iter().find(|d| d.name == "P").unwrap();
        assert!(d.axiom_usage.postulate);
    }

    #[test]
    fn detects_sparklib_lemma_convention() {
        let p = parse(SPARKLIB);
        let lemma = p
            .decls
            .iter()
            .find(|d| d.name == "Lemma_Mult_Comm")
            .expect("lemma");
        assert!(lemma.axiom_usage.other.iter().any(|t| t == "sparklib:lemma"));
        assert!(lemma.axiom_usage.other.iter().any(|t| t == "spark:ghost"));
    }

    #[test]
    fn flags_trusted_import_and_unchecked_conversion() {
        let src = r#"
package body Edges is
   function Raw (P : Address) return Word is
   begin
      return Unchecked_Conversion (P);
   end Raw;
   pragma Import (C, Raw, "raw_word");
end Edges;
"#;
        let p = parse(src);
        let d = p.decls.iter().find(|d| d.name == "Raw").unwrap();
        assert!(d
            .axiom_usage
            .other
            .iter()
            .any(|t| t == "spark:unchecked_conversion"));
        assert!(d
            .axiom_usage
            .other
            .iter()
            .any(|t| t == "spark:trusted_import"));
    }

    #[test]
    fn comments_and_strings_do_not_create_declarations() {
        let src = r#"
package Quiet is
   -- procedure Ghost_Decl (X : Integer);
   Banner : constant String := "procedure Not_A_Decl; end Nope;";
end Quiet;
"#;
        let p = parse(src);
        assert!(
            p.decls.is_empty(),
            "got unexpected decls: {:?}",
            p.decls.iter().map(|d| &d.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn access_procedure_is_not_a_declaration() {
        let src = "\
package Callbacks is
   type Handler is access procedure (X : Integer);
end Callbacks;
";
        let p = parse(src);
        assert!(p.decls.iter().all(|d| d.name != "X"));
    }

    #[test]
    fn ingest_of_empty_root_is_an_empty_corpus() {
        let tmp = tempfile::tempdir().unwrap();
        let corpus = ingest(tmp.path()).expect("ingest empty tree");
        assert_eq!(corpus.adapter, "spark_ada");
        assert!(corpus.entries.is_empty());
        assert!(corpus.modules.is_empty());
    }
}
