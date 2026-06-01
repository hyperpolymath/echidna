// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Mizar adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.miz` (article) and `*.abs`
//! (interface / abstract) file, and extracts a structural index. The
//! extractor is heuristic, not a full Mizar parser:
//!
//! - Strips line comments (`:: …`) before declaration scanning. The
//!   special `::>` comment-error marker is treated as an ordinary
//!   line comment too.
//! - Recognises the `environ` block (vocabularies, notations,
//!   constructors, registrations, requirements, definitions, theorems,
//!   schemes) — the `theorems` and `definitions` lists become the
//!   module's `imports`.
//! - After `begin`, recognises article-body declarations introduced
//!   by `theorem`, `definition`, `scheme`, `cluster`, `registration`,
//!   `notation`, `synonym`, `antonym`, `attr`, `mode`, `func`,
//!   `pred`, `redefine`.
//! - Pairs each declaration with its `proof … end;` body when present.
//! - Detects mild hazards: `@proof` (sketch proof), commented-out
//!   theorem placeholders (`:: theorem`), and `consider … such that
//!   …` clauses with no proof following.
//!
//! Module name: derived from the filename stem (Mizar articles are
//! uppercase ≤8-char names like `FUNCT_1`).
//!
//! Skip directories: `.git`, `mizar`, `mml`, `temp`, `target`.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_mizar(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "mizar".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_mizar_file(&raw);

        let module_idx = corpus.modules.len();
        let module_name = parsed
            .module_name
            .clone()
            .unwrap_or_else(|| article_name_from_path(&rel));
        let module_entry = ModuleEntry {
            name: module_name,
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

    // Pass 2: dependency resolution by simple identifier matching.
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

fn walk_mizar(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "mizar" | "mml" | "temp" | "target"
            ) {
                continue;
            }
            walk_mizar(&p, out)?;
        } else {
            let ext = p.extension().and_then(|s| s.to_str());
            if matches!(ext, Some("miz") | Some("abs")) {
                out.push(p);
            }
        }
    }
    Ok(())
}

/// Extract the article name from a path: filename stem, uppercased.
/// `FUNCT_1.miz` → `FUNCT_1`; `funct_1.miz` → `FUNCT_1`.
fn article_name_from_path(rel: &Path) -> String {
    let stem = rel
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("UNKNOWN");
    stem.to_uppercase()
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

/// Strip line comments (`:: …` to end-of-line) preserving newlines so
/// line counts stay stable. Mizar has no block comments — every
/// comment starts with `::` and runs to end-of-line. The variant `::>`
/// (Mizar's checker-message comment) is treated the same.
fn strip_comments(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    for line in src.split_inclusive('\n') {
        if let Some(idx) = line.find("::") {
            // Preserve everything up to the comment marker, then pad
            // with spaces until end of original content; keep newline.
            let (kept, tail) = line.split_at(idx);
            out.push_str(kept);
            for c in tail.chars() {
                if c == '\n' {
                    out.push('\n');
                } else {
                    out.push(' ');
                }
            }
        } else {
            out.push_str(line);
        }
    }
    out
}

fn parse_mizar_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();

    // Imports: scan the environ block for `theorems` / `definitions`
    // / `schemes` directives. Each is `keyword X, Y, Z ;`.
    //
    // Parse mode: the `environ` block lives at the start of the file
    // (before `begin`). We collect raw text between `environ` and
    // `begin`, then split into directive statements at `;`.
    let env_start = find_keyword_at_word(&stripped, "environ");
    let begin_pos = find_keyword_at_word(&stripped, "begin");
    if let (Some(es), Some(bp)) = (env_start, begin_pos) {
        if bp > es {
            let env_text = &stripped[es + "environ".len()..bp];
            collect_imports(env_text, &mut pf.imports);
        }
    }

    // Body declarations: scan lines after `begin` for declaration
    // keywords. We do a token-level scan rather than a per-line scan
    // because Mizar's keywords can appear anywhere on a line.
    let body_start = begin_pos.map(|b| b + "begin".len()).unwrap_or(0);
    let body_lines: Vec<&str> = stripped[body_start..].lines().collect();
    let body_line_offset = stripped[..body_start].lines().count();

    let raw_lines: Vec<&str> = raw.lines().collect();

    let mut i = 0;
    while i < body_lines.len() {
        let line = body_lines[i];
        let trimmed = line.trim_start();
        let line_no = body_line_offset + i + 1;

        // Recognise declaration heads.
        let head_keyword = leading_keyword(trimmed);
        let is_decl_head = matches!(
            head_keyword.as_deref(),
            Some(
                "theorem"
                | "definition"
                | "scheme"
                | "cluster"
                | "registration"
                | "notation"
                | "synonym"
                | "antonym"
                | "attr"
                | "mode"
                | "func"
                | "pred"
                | "redefine"
            )
        );

        if is_decl_head {
            let kw = head_keyword.unwrap();
            // Collect the statement: from this line until we see
            // `proof`, `;`, or the matching `end;` for definition/
            // scheme/registration/cluster blocks.
            //
            // Statement extends across continuation lines until we
            // either hit `proof`, a `;` at the end of a line, or a
            // top-level keyword line that opens a new block.
            let mut stmt = String::from(trimmed);
            let (name, kind) = classify_decl(&kw, trimmed);
            let mut j = i + 1;
            let mut proof: Option<String> = None;

            // For block-shaped decls (definition / scheme / cluster /
            // registration / notation) collect everything until the
            // matching `end;` at column 0-ish.
            let is_block = matches!(
                kw.as_str(),
                "definition" | "scheme" | "cluster" | "registration" | "notation"
            );

            if is_block {
                let mut body = String::new();
                while j < body_lines.len() {
                    let bl = body_lines[j];
                    body.push(' ');
                    body.push_str(bl.trim());
                    if leading_keyword(bl.trim_start()).as_deref() == Some("end")
                        && bl.contains(';')
                    {
                        j += 1;
                        break;
                    }
                    j += 1;
                }
                if !body.is_empty() {
                    proof = Some(normalise_ws(&body));
                }
            } else {
                // Theorem-shape: gather statement until `proof` or `;`.
                let mut found_proof_kw = false;
                while j < body_lines.len() {
                    let bl = body_lines[j];
                    let bl_trim = bl.trim();
                    if bl_trim.is_empty() {
                        j += 1;
                        continue;
                    }
                    if leading_keyword(bl.trim_start()).as_deref() == Some("proof") {
                        found_proof_kw = true;
                        break;
                    }
                    stmt.push(' ');
                    stmt.push_str(bl_trim);
                    if bl_trim.ends_with(';') {
                        j += 1;
                        break;
                    }
                    j += 1;
                }

                if found_proof_kw {
                    // Collect proof body until matching `end;`.
                    let mut body = String::new();
                    let mut depth: i32 = 0;
                    while j < body_lines.len() {
                        let bl = body_lines[j];
                        body.push(' ');
                        body.push_str(bl.trim());
                        let lk = leading_keyword(bl.trim_start());
                        match lk.as_deref() {
                            Some("proof") | Some("now") => depth += 1,
                            Some("end") if bl.contains(';') => {
                                depth -= 1;
                                if depth <= 0 {
                                    j += 1;
                                    break;
                                }
                            },
                            _ => {},
                        }
                        j += 1;
                    }
                    proof = Some(normalise_ws(&body));
                }
            }

            let statement = normalise_ws(&stmt);
            let mut hz = AxiomUsage::default();
            let scan_from = (line_no.saturating_sub(1)).min(raw_lines.len());
            let scan_to = (body_line_offset + j).min(raw_lines.len());
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
            i = j;
            continue;
        }

        i += 1;
    }

    pf
}

/// Find `kw` as a whole-word match in `s`. Returns byte offset of the
/// start of the keyword, or None.
fn find_keyword_at_word(s: &str, kw: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let kwb = kw.as_bytes();
    let mut i = 0;
    while i + kwb.len() <= bytes.len() {
        if &bytes[i..i + kwb.len()] == kwb {
            let before_ok = i == 0 || !is_ident_byte(bytes[i - 1]);
            let after_ok =
                i + kwb.len() == bytes.len() || !is_ident_byte(bytes[i + kwb.len()]);
            if before_ok && after_ok {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn is_ident_byte(b: u8) -> bool {
    let c = b as char;
    c.is_alphanumeric() || c == '_'
}

/// Read `env_text` and append `theorems`/`definitions`/`schemes`
/// identifiers to `imports`. Each directive is
/// `KEYWORD A, B, C ;` with the keyword at the start of a logical
/// statement (we use line boundaries as a proxy).
fn collect_imports(env_text: &str, imports: &mut Vec<String>) {
    // Coalesce: replace newlines with spaces, then split on `;`.
    let flat = env_text.replace('\n', " ");
    for stmt in flat.split(';') {
        let s = stmt.trim();
        if s.is_empty() {
            continue;
        }
        let head = leading_keyword(s);
        let want = matches!(
            head.as_deref(),
            Some("theorems" | "definitions" | "schemes")
        );
        if !want {
            continue;
        }
        let head_len = head.as_ref().map(|h| h.len()).unwrap_or(0);
        let rest = &s[head_len..];
        for id in rest.split(',') {
            let t = id.trim();
            if !t.is_empty() && is_plausible_article_id(t) && !imports.contains(&t.to_string()) {
                imports.push(t.to_string());
            }
        }
    }
}

fn is_plausible_article_id(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Leading keyword (alphanumeric `_` run) at start of `s`.
fn leading_keyword(s: &str) -> Option<String> {
    let t = s.trim_start();
    let kw: String = t
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if kw.is_empty() {
        None
    } else {
        Some(kw)
    }
}

/// Classify a declaration head line and extract a usable name.
fn classify_decl(kw: &str, head_line: &str) -> (String, DeclKind) {
    // Drop the leading keyword and any whitespace.
    let after_kw = head_line.trim_start();
    let after_kw = after_kw.strip_prefix(kw).unwrap_or(after_kw).trim_start();

    let (name, kind) = match kw {
        "theorem" => {
            // `theorem Th1: ...` (named) or `theorem ...` (unnamed).
            let nm = parse_label_name(after_kw)
                .unwrap_or_else(|| synthetic_name("Theorem", head_line));
            (nm, DeclKind::Function)
        },
        "definition" => {
            // Mizar `definition` blocks may not have a single direct
            // name; try to lift the first introduced func/mode/pred
            // identifier from the head line, else synthesise.
            let nm = parse_first_definiendum(after_kw)
                .unwrap_or_else(|| synthetic_name("Def", head_line));
            (nm, DeclKind::Function)
        },
        "scheme" => {
            // `scheme SchemeName { … } : … provided …`
            let nm = parse_first_ident(after_kw)
                .unwrap_or_else(|| synthetic_name("Scheme", head_line));
            (nm, DeclKind::Record)
        },
        "cluster" | "registration" => {
            // Often anonymous; synthesise a stable name.
            let nm = synthetic_name(if kw == "cluster" { "Cluster" } else { "Reg" }, head_line);
            (nm, DeclKind::Data)
        },
        "notation" => {
            // `notation` blocks introduce synonyms — keep as Function
            // (the introduced thing is a name binding).
            let nm = parse_first_ident(after_kw)
                .unwrap_or_else(|| synthetic_name("Notation", head_line));
            (nm, DeclKind::Function)
        },
        "synonym" | "antonym" => {
            let nm = parse_first_ident(after_kw)
                .unwrap_or_else(|| synthetic_name(kw, head_line));
            (nm, DeclKind::Function)
        },
        "attr" | "mode" | "func" | "pred" => {
            let nm = parse_first_ident(after_kw)
                .unwrap_or_else(|| synthetic_name(kw, head_line));
            (nm, DeclKind::Function)
        },
        "redefine" => {
            let nm = parse_first_ident(after_kw)
                .unwrap_or_else(|| synthetic_name("Redefine", head_line));
            (nm, DeclKind::Function)
        },
        _ => (synthetic_name("Decl", head_line), DeclKind::Function),
    };
    (name, kind)
}

/// `Th1: …` → `Th1`. Returns None if no `:` separator at sensible spot.
fn parse_label_name(s: &str) -> Option<String> {
    let mut chars = s.chars().peekable();
    let mut name = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_ascii_alphanumeric() || c == '_' {
            name.push(c);
            chars.next();
        } else {
            break;
        }
    }
    if name.is_empty() {
        return None;
    }
    // Skip whitespace.
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
    if chars.peek() == Some(&':') {
        Some(name)
    } else {
        None
    }
}

fn parse_first_ident(s: &str) -> Option<String> {
    let id: String = s
        .chars()
        .skip_while(|c| c.is_whitespace())
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if id.is_empty() {
        None
    } else {
        Some(id)
    }
}

/// Try to find the first `func X`, `mode X`, `pred X`, or `attr X`
/// token inside a definition block head line.
fn parse_first_definiendum(s: &str) -> Option<String> {
    for kw in &["func", "mode", "pred", "attr"] {
        if let Some(idx) = find_keyword_at_word(s, kw) {
            let rest = &s[idx + kw.len()..];
            return parse_first_ident(rest);
        }
    }
    None
}

fn synthetic_name(prefix: &str, head_line: &str) -> String {
    // Use a short stable suffix derived from the trimmed head line.
    let h = head_line.trim();
    // Take up to first 16 alphanumeric chars.
    let suffix: String = h
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
        .take(16)
        .collect();
    if suffix.is_empty() {
        prefix.to_string()
    } else {
        format!("{}_{}", prefix, suffix)
    }
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
                    | ':'
                    | '='
                    | '.'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    // `@proof` is the canonical Mizar "sketch / unfinished proof"
    // token. Treat it the same as `sorry` / `Admitted` elsewhere.
    if text.contains("@proof") {
        hz.sorry = true;
        hz.other.push("@proof".to_string());
    }
    // Commented-out theorem markers are a mild hazard — they often
    // mark intentionally-suppressed lemmas. We don't elevate this to
    // `admitted`; just surface it via `other`.
    for line in text.lines() {
        let t = line.trim_start();
        if t.starts_with(":: theorem") || t.starts_with("::theorem") {
            hz.other.push("commented-theorem".to_string());
            break;
        }
    }
    // `consider _ such that _;` without a following proof step is a
    // mild signal. The textual heuristic: a `consider` clause that
    // ends with `;` and has no `by …;` or trailing justification.
    for window in text.split("consider ").skip(1) {
        let head: String = window.chars().take(200).collect();
        let has_st = head.contains("such that");
        let has_by = head.contains(" by ") || head.contains(";by ");
        if has_st && !has_by {
            hz.other.push("consider-without-proof".to_string());
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_environ_begin_theorem_with_proof() {
        let src = "environ\n vocabularies XBOOLE_0;\n theorems TARSKI, XBOOLE_0;\n definitions XBOOLE_0;\n\nbegin\n\ntheorem Th1:\n  for P being set holds P = P\nproof\n  let P be set;\n  thus P = P;\nend;\n";
        let pf = parse_mizar_file(src);
        // Imports gathered from theorems + definitions.
        assert!(pf.imports.contains(&"TARSKI".to_string()));
        assert!(pf.imports.contains(&"XBOOLE_0".to_string()));
        // One theorem-shape declaration captured.
        assert_eq!(pf.decls.len(), 1, "decls = {:?}", pf.decls);
        assert_eq!(pf.decls[0].name, "Th1");
        assert_eq!(pf.decls[0].kind, DeclKind::Function);
        assert!(pf.decls[0].statement.contains("for P being set"));
        let body = pf.decls[0].proof.as_deref().unwrap_or("");
        assert!(body.contains("let P"), "proof body missing 'let P': {}", body);
        assert!(body.contains("thus P = P"));
        assert!(!pf.decls[0].axiom_usage.any());
    }

    #[test]
    fn detects_at_proof_hazard() {
        let src = "environ\nbegin\ntheorem Tx: P implies P\n@proof\nthus thesis;\nend;\n";
        let pf = parse_mizar_file(src);
        assert_eq!(pf.decls.len(), 1);
        // `@proof` should set the sorry flag and append "@proof" to
        // the `other` hazard list.
        assert!(pf.decls[0].axiom_usage.sorry, "sorry flag not set: {:?}", pf.decls[0].axiom_usage);
        assert!(pf.decls[0]
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "@proof"));
    }

    #[test]
    fn article_name_uppercased_from_filename() {
        let p = PathBuf::from("articles/funct_1.miz");
        assert_eq!(article_name_from_path(&p), "FUNCT_1");
        let p2 = PathBuf::from("FUNCT_1.abs");
        assert_eq!(article_name_from_path(&p2), "FUNCT_1");
    }

    #[test]
    fn strips_line_comments_preserving_newlines() {
        let src = "theorem Th: P\n:: a comment line\nproof\n  thus P; :: inline comment\nend;\n";
        let out = strip_comments(src);
        assert_eq!(out.lines().count(), src.lines().count());
        assert!(!out.contains("comment"));
        assert!(out.contains("thus P;"));
    }
}
