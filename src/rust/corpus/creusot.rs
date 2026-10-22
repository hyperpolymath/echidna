// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Rust / Creusot adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.rs` file (excluding `target`,
//! `.git`, `node_modules`, `.cargo`), and extracts a structural index of
//! the *specified* surface: functions carrying Creusot contracts,
//! `#[logic]` / `#[predicate]` ghost definitions, and the data types
//! those contracts quantify over.
//!
//! Rust is the estate's third TCB language and, per estate policy, the
//! Rust layer is Rust/Creusot — contracts are written, not assumed. So
//! the interesting questions for the index are "which obligations did
//! this function state" and "which of them are trusted rather than
//! proved", not "how many `fn`s are there".
//!
//! What we recognise:
//! - `fn`, `pub fn`, `pub(crate) fn`, `const fn`, `async fn`,
//!   `unsafe fn`, `extern "C" fn` (signature plus body).
//! - Contract attributes: `#[requires(...)]`, `#[ensures(...)]`,
//!   `#[invariant(...)]`, `#[variant(...)]`, `#[maintains(...)]`,
//!   `#[check(...)]`, `#[terminates]`, `#[logic]`, `#[predicate]`,
//!   `#[trusted]`, `#[cfg(creusot)]`. All of them are folded into the
//!   entry's `statement` so the discipline detector and the semantic
//!   layer see the actual specification text.
//! - Spec macros inside contracts or bodies: `pearlite!{...}`,
//!   `proof_assert!{...}`, `snapshot!{...}`.
//! - `struct`, `enum`, `union`, `trait`, `type` aliases, `const`.
//!
//! Hazards:
//! - `#[trusted]` → `AxiomUsage::postulate`. Creusot *skips* the body and
//!   accepts the contract on faith; that is a postulate with a nicer
//!   spelling, and downstream consumers must treat it as one.
//! - `unsafe` blocks / `unsafe fn` → `creusot:unsafe_surface`.
//! - `transmute` → `creusot:transmute`.
//! - `unimplemented!` / `todo!` → `creusot:unimplemented`.
//! - `extern "C"` → `creusot:ffi_edge`. Per estate policy the FFI layer
//!   is Zig, so a Rust `extern "C"` is a boundary to *flag*, not to ban.
//! - `#[cfg(creusot)]` → `creusot:gated_spec`: the specification only
//!   exists for the verifier, so a plain build is not the same artefact.
//!
//! `#[cfg(test)]` / `#[test]` items are skipped: a corpus of proofs
//! should not be dominated by test functions.
//!
//! ## Heuristics (not a parser)
//!
//! A signature ends at the first `{` or `;` at paren depth zero, and a
//! body is brace-matched from there. Comments and string contents are
//! blanked before structural scanning, but `statement`/`proof` are
//! sliced from the original text, so contract expressions keep their
//! spelling.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus from every Rust source file.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_rust(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "creusot".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_rust_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed.module.clone().unwrap_or_else(|| module_name_from_rel(&rel));
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

fn walk_rust(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "node_modules" | ".cargo" | "build" | "dist"
            ) {
                continue;
            }
            walk_rust(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(p);
        }
    }
    Ok(())
}

/// Rust module path for a file: `src/corpus/mod.rs` → `corpus`,
/// `src/abi/layout.rs` → `abi.layout`.
pub(crate) fn module_name_from_rel(rel: &Path) -> String {
    let mut parts: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    if let Some(last) = parts.pop() {
        let stem = last.strip_suffix(".rs").unwrap_or(&last).to_string();
        if stem != "mod" && stem != "lib" && stem != "main" && !stem.is_empty() {
            parts.push(stem);
        }
    }
    parts.retain(|p| p != "src" && p != "." && !p.is_empty());
    if parts.is_empty() {
        "crate".to_string()
    } else {
        parts.join(".")
    }
}

#[derive(Debug, Default)]
pub(crate) struct ParsedFile {
    pub(crate) module: Option<String>,
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
    text: String,
    start: usize,
    end: usize,
}

/// Blank out comments and string/char contents while preserving byte
/// offsets, so `clean` and `orig` describe the same regions.
fn clean_source(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = bytes.to_vec();
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                out[i] = b' ';
                i += 1;
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            // Block comments nest in Rust.
            let mut depth = 0;
            while i < bytes.len() {
                if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    depth += 1;
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    continue;
                }
                if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                    depth -= 1;
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                    continue;
                }
                if bytes[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
        } else if bytes[i] == b'"' {
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    out[i] = b' ';
                    if i + 1 < bytes.len() && bytes[i + 1] != b'\n' {
                        out[i + 1] = b' ';
                    }
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    break;
                }
                if bytes[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
            i += 1;
        } else if bytes[i] == b'\'' {
            // Char literal `'a'`, but leave lifetimes (`'a`) alone.
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
            toks.push(Tok {
                kind: TokKind::Ident,
                text: clean[start..i].to_string(),
                start,
                end: i,
            });
        } else if c.is_ascii_digit() {
            while i < bytes.len() {
                let d = bytes[i] as char;
                if d.is_ascii_alphanumeric() || d == '_' {
                    i += 1;
                } else {
                    break;
                }
            }
            toks.push(Tok {
                kind: TokKind::Number,
                text: clean[start..i].to_string(),
                start,
                end: i,
            });
        } else if c == '"' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                i += 1;
            }
            i = (i + 1).min(bytes.len());
            toks.push(Tok {
                kind: TokKind::Str,
                text: clean[start..i].to_string(),
                start,
                end: i,
            });
        } else {
            i += 1;
            toks.push(Tok {
                kind: TokKind::Punct,
                text: clean[start..i].to_string(),
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
    // Rust keywords are lowercase and case-sensitive: `Fn` is a trait,
    // `fn` is the keyword.
    tok.kind == TokKind::Ident && tok.text == kw
}

fn is_punct(tok: &Tok, p: &str) -> bool {
    tok.kind == TokKind::Punct && tok.text == p
}

#[derive(Debug)]
struct Attr {
    start: usize,
    end: usize,
    line: usize,
    text: String,
}

/// Every `#[...]` attribute in the file, outermost bracket matched.
fn collect_attrs(src: &str, toks: &[Tok]) -> Vec<Attr> {
    let mut attrs: Vec<Attr> = Vec::new();
    let mut i = 0;
    while i + 1 < toks.len() {
        if is_punct(&toks[i], "#") && is_punct(&toks[i + 1], "[") {
            let mut depth = 0i32;
            let mut j = i + 1;
            while j < toks.len() {
                if is_punct(&toks[j], "[") {
                    depth += 1;
                } else if is_punct(&toks[j], "]") {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                j += 1;
            }
            if j < toks.len() {
                let start = toks[i].start;
                let end = toks[j].end;
                attrs.push(Attr {
                    start,
                    end,
                    line: line_of(src, start),
                    text: normalise_ws(&src[start..end]),
                });
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    attrs
}

/// Attributes immediately preceding `start`, nearest last.
fn leading_attrs(attrs: &[Attr], clean: &str, start: usize) -> Vec<&Attr> {
    let mut out: Vec<&Attr> = Vec::new();
    let mut cursor = start;
    for attr in attrs.iter().rev() {
        if attr.end > cursor {
            continue;
        }
        let between = &clean[attr.end..cursor];
        if between.trim().is_empty() {
            out.push(attr);
            cursor = attr.start;
        } else {
            break;
        }
    }
    out.reverse();
    out
}

fn attr_text(attrs: &[&Attr]) -> String {
    attrs
        .iter()
        .map(|a| a.text.clone())
        .collect::<Vec<_>>()
        .join(" ")
}

fn has_attr(attrs: &[&Attr], needle: &str) -> bool {
    attrs.iter().any(|a| a.text.contains(needle))
}

/// Parse one Rust source file into module metadata plus draft decls.
pub(crate) fn parse_rust_file(src: &str) -> ParsedFile {
    let clean = clean_source(src);
    let toks = tokenise(&clean);
    let attrs = collect_attrs(src, &toks);
    let mut parsed = ParsedFile::default();

    parsed.imports = collect_uses(src, &toks);

    let mut k = 0;
    while k < toks.len() {
        let t = &toks[k];
        let (kind, name_idx) = if is_kw(t, "fn") {
            (DeclKind::Function, k + 1)
        } else if is_kw(t, "struct") || is_kw(t, "enum") || is_kw(t, "union") {
            (DeclKind::Data, k + 1)
        } else if is_kw(t, "trait") {
            (DeclKind::Record, k + 1)
        } else if is_kw(t, "type") || is_kw(t, "static") {
            (DeclKind::Data, k + 1)
        } else if is_kw(t, "const") && !(k + 1 < toks.len() && is_kw(&toks[k + 1], "fn")) {
            (DeclKind::Data, k + 1)
        } else {
            k += 1;
            continue;
        };
        if name_idx >= toks.len() || toks[name_idx].kind != TokKind::Ident {
            k += 1;
            continue;
        }
        let name = toks[name_idx].text.clone();
        let first = modifier_start(&toks, k);

        let leading = leading_attrs(&attrs, &clean, toks[first].start);
        // Test scaffolding is not part of the proved surface.
        let is_test = leading
            .iter()
            .any(|a| a.text.contains("cfg(test)") || a.text == "#[test]");
        if is_test {
            k = name_idx + 1;
            continue;
        }

        let (spec_end, body_start) = item_extent(&toks, name_idx);
        if spec_end <= name_idx {
            k += 1;
            continue;
        }

        let attrs_txt = attr_text(&leading);
        let signature = normalise_ws(&src[toks[first].start..toks[spec_end].start]);
        let statement = if attrs_txt.is_empty() {
            signature
        } else {
            format!("{} {}", attrs_txt, signature)
        };

        let mut proof = None;
        let mut advance = spec_end;
        if let Some(bs) = body_start {
            let be = match_brace(&toks, bs);
            if kind == DeclKind::Function {
                let body_text = match be {
                    Some(e) => &src[toks[bs].end..toks[e].start],
                    None => &src[toks[bs].end..],
                };
                proof = Some(body_text.trim().to_string());
                advance = be.unwrap_or(bs);
            } else if kind == DeclKind::Data {
                // Skip the field/variant block: fields are not decls.
                advance = be.unwrap_or(bs);
            }
            // A trait block is walked, so its method signatures are
            // indexed alongside its name.
        }

        let mut axiom_usage = AxiomUsage::default();
        flag_creusot_hazards(&statement, &mut axiom_usage);
        if let Some(p) = &proof {
            flag_creusot_hazards(p, &mut axiom_usage);
        }
        flag_creusot_attrs(&statement, &mut axiom_usage);

        parsed.decls.push(DraftDecl {
            name,
            kind,
            statement,
            proof,
            line: line_of(src, toks[first].start),
            axiom_usage,
        });

        if has_attr(&leading, "cfg(creusot)") {
            if !parsed.options.iter().any(|o| o == "creusot-gated") {
                parsed.options.push("creusot-gated".to_string());
            }
        }

        k = advance.max(k + 1);
    }

    parsed
}

/// Index of the first modifier token of an item (`pub`, `pub(crate)`,
/// `async`, `unsafe`, `const`, `extern "C"`), so an attribute written
/// above the modifiers is still attached to the item.
fn modifier_start(toks: &[Tok], k: usize) -> usize {
    let mut i = k;
    loop {
        if i == 0 {
            return i;
        }
        let p = &toks[i - 1];
        if p.kind == TokKind::Ident
            && matches!(
                p.text.as_str(),
                "pub" | "async" | "unsafe" | "const" | "default" | "extern"
            )
        {
            i -= 1;
            continue;
        }
        if p.kind == TokKind::Str && p.text == "\"C\"" {
            i -= 1;
            continue;
        }
        if is_punct(p, ")") {
            // `pub(crate)` / `pub(super)` — hop over the group.
            let mut depth = 0i32;
            let mut j = i;
            let mut open = None;
            while j > 0 {
                j -= 1;
                let t = &toks[j];
                if is_punct(t, ")") {
                    depth += 1;
                } else if is_punct(t, "(") {
                    depth -= 1;
                    if depth == 0 {
                        open = Some(j);
                        break;
                    }
                }
            }
            if let Some(o) = open {
                if o > 0 && is_kw(&toks[o - 1], "pub") {
                    i = o - 1;
                    continue;
                }
            }
        }
        return i;
    }
}

/// End of a signature / item header: first `{` (body follows) or `;` at
/// paren depth zero. Returns `(end_of_header, body_start)`.
fn item_extent(toks: &[Tok], name_idx: usize) -> (usize, Option<usize>) {
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
        } else if depth == 0 && is_punct(t, "{") {
            return (j, Some(j));
        } else if depth == 0 && is_punct(t, ";") {
            return (j, None);
        }
        j += 1;
    }
    (toks.len(), None)
}

/// Index of the brace closing the one at `open`.
fn match_brace(toks: &[Tok], open: usize) -> Option<usize> {
    if open >= toks.len() || !is_punct(&toks[open], "{") {
        return None;
    }
    let mut depth = 0i32;
    let mut j = open;
    while j < toks.len() {
        if is_punct(&toks[j], "{") {
            depth += 1;
        } else if is_punct(&toks[j], "}") {
            depth -= 1;
            if depth == 0 {
                return Some(j);
            }
        }
        j += 1;
    }
    None
}

/// Collect `use ...;` paths, trimmed to the path (no `::{}` groups).
fn collect_uses(src: &str, toks: &[Tok]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        if !is_kw(&toks[i], "use") {
            i += 1;
            continue;
        }
        let start = toks[i].end;
        let mut j = i + 1;
        while j < toks.len() && !is_punct(&toks[j], ";") {
            j += 1;
        }
        if j < toks.len() {
            let raw = normalise_ws(&src[start..toks[j].start]);
            let base = raw.split("::{").next().unwrap_or("").trim().to_string();
            let base = base.trim_end_matches("::*").trim_end_matches("::").to_string();
            let path = base.split("::").take(3).collect::<Vec<_>>().join("::");
            if !path.is_empty() && !out.contains(&path) {
                out.push(path);
            }
        }
        i = j + 1;
    }
    out
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|t| !t.is_empty())
        .collect()
}

/// `#[trusted]` is Creusot's "accept the contract, skip the body" — the
/// same soundness escape as an Agda postulate, so it maps there.
fn flag_creusot_attrs(statement: &str, hz: &mut AxiomUsage) {
    if statement.contains("#[trusted") {
        hz.postulate = true;
        push_once(&mut hz.other, "creusot:trusted");
    }
    if statement.contains("cfg(creusot)") {
        push_once(&mut hz.other, "creusot:gated_spec");
    }
    if statement.contains("#[logic]") || statement.contains("#[predicate]") {
        push_once(&mut hz.other, "creusot:logic");
    }
    if statement.contains("#[requires") {
        push_once(&mut hz.other, "creusot:requires");
    }
    if statement.contains("#[ensures") {
        push_once(&mut hz.other, "creusot:ensures");
    }
    if statement.contains("#[invariant") || statement.contains("#[maintains") {
        push_once(&mut hz.other, "creusot:invariant");
    }
    if statement.contains("#[variant") || statement.contains("#[terminates") {
        push_once(&mut hz.other, "creusot:termination");
    }
}

fn flag_creusot_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("#[trusted") {
        hz.postulate = true;
        push_once(&mut hz.other, "creusot:trusted");
    }
    if text.contains("pearlite!") {
        push_once(&mut hz.other, "creusot:pearlite");
    }
    if text.contains("proof_assert!") {
        push_once(&mut hz.other, "creusot:proof_assert");
    }
    if text.contains("snapshot!") {
        push_once(&mut hz.other, "creusot:snapshot");
    }
    if text.contains("transmute") {
        push_once(&mut hz.other, "creusot:transmute");
    }
    if text.contains("unimplemented!") || text.contains("todo!") {
        push_once(&mut hz.other, "creusot:unimplemented");
    }
    if text.contains("unsafe") {
        push_once(&mut hz.other, "creusot:unsafe_surface");
    }
    if text.contains("extern \"C\"") || text.contains("extern \"C\" ") {
        push_once(&mut hz.other, "creusot:ffi_edge");
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

    const CONTRACTS: &str = r#"
use creusot_contracts::*;

#[requires(x@ < 1000)]
#[ensures(result@ == x@ + 1)]
pub fn increment(x: u32) -> u32 {
    x + 1
}

#[trusted]
#[requires(n@ > 0)]
#[ensures(result@ == n@)]
fn trusted_identity(n: u32) -> u32 {
    n
}

#[logic]
fn half(x: Int) -> Int {
    pearlite! { x / 2 }
}

#[test]
fn tests_are_not_proofs() {
    assert_eq!(increment(1), 2);
}

pub struct Wrapper {
    inner: u32,
}

pub trait Measured {
    fn measure(&self) -> u32;
}
"#;

    fn parse(src: &str) -> ParsedFile {
        parse_rust_file(src)
    }

    fn find<'a>(p: &'a ParsedFile, name: &str) -> Option<&'a DraftDecl> {
        p.decls.iter().find(|d| d.name == name)
    }

    #[test]
    fn captures_requires_and_ensures() {
        let p = parse(CONTRACTS);
        let inc = find(&p, "increment").expect("increment");
        assert!(inc.statement.contains("requires(x@ < 1000)"));
        assert!(inc.statement.contains("ensures(result@ == x@ + 1)"));
        assert!(inc.axiom_usage.other.iter().any(|t| t == "creusot:requires"));
        assert!(inc.axiom_usage.other.iter().any(|t| t == "creusot:ensures"));
    }

    #[test]
    fn body_is_captured() {
        let p = parse(CONTRACTS);
        let inc = find(&p, "increment").expect("increment");
        assert_eq!(inc.proof.as_deref(), Some("x + 1"));
    }

    #[test]
    fn trusted_is_a_postulate() {
        let p = parse(CONTRACTS);
        let t = find(&p, "trusted_identity").expect("trusted_identity");
        assert!(t.axiom_usage.postulate);
        assert!(t.axiom_usage.other.iter().any(|s| s == "creusot:trusted"));
    }

    #[test]
    fn logic_functions_and_pearlite_are_tagged() {
        let p = parse(CONTRACTS);
        let h = find(&p, "half").expect("half");
        assert!(h.axiom_usage.other.iter().any(|s| s == "creusot:logic"));
        assert!(h
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "creusot:pearlite"));
    }

    #[test]
    fn tests_are_skipped() {
        let p = parse(CONTRACTS);
        assert!(find(&p, "tests_are_not_proofs").is_none());
    }

    #[test]
    fn data_and_trait_decls_are_indexed() {
        let p = parse(CONTRACTS);
        let w = find(&p, "Wrapper").expect("Wrapper");
        assert_eq!(w.kind, DeclKind::Data);
        let t = find(&p, "Measured").expect("Measured");
        assert_eq!(t.kind, DeclKind::Record);
    }

    #[test]
    fn trait_method_signature_has_no_body() {
        let p = parse(CONTRACTS);
        let m = find(&p, "measure").expect("measure");
        assert!(m.proof.is_none());
    }

    #[test]
    fn imports_are_collected() {
        let p = parse(CONTRACTS);
        assert!(p.imports.iter().any(|i| i == "creusot_contracts"));
    }

    #[test]
    fn comments_and_strings_do_not_create_decls() {
        let src = r#"
// fn not_a_decl() {}
/* fn also_not() {} */
const BANNER: &str = "fn nope() {}";
"#;
        let p = parse(src);
        let names: Vec<&String> = p.decls.iter().map(|d| &d.name).collect();
        assert!(names.contains(&&"BANNER".to_string()));
        assert!(!names.contains(&&"not_a_decl".to_string()));
        assert!(!names.contains(&&"nope".to_string()));
    }

    #[test]
    fn unsafe_and_transmute_are_flagged() {
        let src = r#"
fn widen(x: u32) -> u64 {
    unsafe { core::mem::transmute::<u32, u64>(x) }
}
"#;
        let p = parse(src);
        let w = find(&p, "widen").expect("widen");
        assert!(w
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "creusot:unsafe_surface"));
        assert!(w.axiom_usage.other.iter().any(|s| s == "creusot:transmute"));
    }

    #[test]
    fn module_name_from_source_path() {
        assert_eq!(module_name_from_rel(Path::new("src/corpus/mod.rs")), "corpus");
        assert_eq!(module_name_from_rel(Path::new("src/lib.rs")), "crate");
        assert_eq!(
            module_name_from_rel(Path::new("src/abi/layout.rs")),
            "abi.layout"
        );
    }

    #[test]
    fn ingest_of_empty_root_is_an_empty_corpus() {
        let tmp = tempfile::tempdir().unwrap();
        let corpus = ingest(tmp.path()).expect("ingest empty tree");
        assert_eq!(corpus.adapter, "creusot");
        assert!(corpus.entries.is_empty());
    }
}
