// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Agda adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.agda` file (excluding
//! `_build/`), and extracts a structural index. The extractor is
//! deliberately heuristic, not a full parser:
//!
//! - Strips line and block comments.
//! - Recognises the leading `{-# OPTIONS … #-}` pragma.
//! - Recognises `module … where` and `(open) import …`.
//! - Recognises top-level type signatures (`name : ty` at column 0)
//!   and definitions (`name … = …`), pairing them when adjacent.
//! - Recognises `data N : … where`, `record N : … where`, and
//!   `postulate` blocks.
//! - Detects banned-pattern axiom usage (`postulate`, `believe_me`,
//!   `assert_total`, `Admitted`, `sorry`, `unsafeCoerce`, `Obj.magic`,
//!   `trustme`).
//!
//! The output is good enough for echo-types' Buchholz / Brouwer
//! programme — it's the same level of structural awareness Echidna's
//! `suggest` module already needs for cross-file references.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `_build`, `.git`, `node_modules`, and
/// `target` regardless of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_agda(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "agda".to_string(),
        ..Default::default()
    };

    // Pass 1: parse each file into a draft module + draft entries.
    // Names collected here form the dependency-resolution alphabet.
    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;
        let parsed = parse_agda_file(&raw);

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

    // Pass 2: resolve dependencies.
    //
    // For each entry, scan its statement + proof text and record any
    // identifier that matches a known name (and isn't its own name).
    // This is intentionally textual — Agda's Unicode-rich identifiers
    // (`<ᵇ-+2`, `osuc-mono-≤`) make a precise tokeniser more work
    // than the value warrants for a structural index.
    let mut name_lookup: Vec<&str> = all_names.iter().map(String::as_str).collect();
    name_lookup.sort_by_key(|s| std::cmp::Reverse(s.len()));

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

fn walk_agda(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir)
        .with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name = entry.file_name();
        let name_s = name.to_string_lossy();
        if p.is_dir() {
            if matches!(
                name_s.as_ref(),
                "_build" | ".git" | "node_modules" | "target" | ".cache"
            ) {
                continue;
            }
            walk_agda(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("agda") {
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

/// Strip line comments (`-- …`) and block comments (`{- … -}`),
/// preserving line counts (replace with spaces) so line numbers
/// reported in `DraftDecl::line` match the original file.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut block_depth: usize = 0;
    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'}' {
                block_depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' {
                block_depth += 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            // Preserve newlines so line counts are stable.
            out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
            i += 1;
            continue;
        }
        // Pragmas {-# … #-} are NOT comments — keep them so the
        // OPTIONS line is visible to the pragma scanner.
        if i + 2 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' && bytes[i + 2] == b'#' {
            // Copy until matching `#-}`.
            while i < bytes.len() {
                if i + 2 < bytes.len()
                    && bytes[i] == b'#'
                    && bytes[i + 1] == b'-'
                    && bytes[i + 2] == b'}'
                {
                    out.push(bytes[i]);
                    out.push(bytes[i + 1]);
                    out.push(bytes[i + 2]);
                    i += 3;
                    break;
                }
                out.push(bytes[i]);
                i += 1;
            }
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' {
            block_depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            // Skip to end of line.
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_agda_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();

    // The hazard scan is run on the *original* source so banned
    // tokens inside string literals or comments still get flagged
    // for human review. Per-decl hazards are localised below.
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    // Module name: first `module X.Y where` after pragmas.
    for line in &lines {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("module ") {
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

    // Options pragma: collect every token from any `{-# OPTIONS … #-}`.
    for line in &lines {
        if let Some(start) = line.find("{-# OPTIONS") {
            let tail = &line[start + "{-# OPTIONS".len()..];
            if let Some(end) = tail.find("#-}") {
                for tok in tail[..end].split_whitespace() {
                    pf.options.push(tok.to_string());
                }
            }
        }
    }

    // Imports.
    for line in &lines {
        let t = line.trim_start();
        let candidate = t
            .strip_prefix("open import ")
            .or_else(|| t.strip_prefix("import "));
        if let Some(rest) = candidate {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                .collect();
            if !name.is_empty() && !pf.imports.contains(&name) {
                pf.imports.push(name);
            }
        }
    }

    // Top-level declarations.
    let mut i = 0;
    let mut in_postulate_block = false;
    let mut postulate_block_indent: Option<usize> = None;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;

        // Postulate block handling. `postulate` on its own at column 0
        // followed by indented `name : ty` lines.
        if !in_postulate_block && line.trim_start() == "postulate" && column_of(line) == 0 {
            in_postulate_block = true;
            postulate_block_indent = None;
            i += 1;
            continue;
        }
        if in_postulate_block {
            if line.trim().is_empty() {
                i += 1;
                continue;
            }
            let col = column_of(line);
            if postulate_block_indent.is_none() {
                postulate_block_indent = Some(col);
            }
            if Some(col) >= postulate_block_indent && col > 0 {
                if let Some((name, statement)) = split_typesig(line.trim()) {
                    pf.decls.push(DraftDecl {
                        name,
                        kind: DeclKind::Postulate,
                        statement,
                        proof: None,
                        line: line_no,
                        axiom_usage: AxiomUsage {
                            postulate: true,
                            ..Default::default()
                        },
                    });
                }
                i += 1;
                continue;
            } else {
                in_postulate_block = false;
                postulate_block_indent = None;
                // fall through and re-process this line
            }
        }

        // `data N … where`
        if column_of(line) == 0 {
            if let Some(rest) = line.trim_start().strip_prefix("data ") {
                if rest.contains(':') || rest.contains(" where") {
                    let name: String = rest
                        .chars()
                        .take_while(|c| !c.is_whitespace() && *c != ':')
                        .collect();
                    if !name.is_empty() {
                        let mut stmt = String::from(line.trim());
                        let mut j = i + 1;
                        while j < lines.len() && !lines[j].trim().is_empty() && column_of(lines[j]) > 0 {
                            stmt.push(' ');
                            stmt.push_str(lines[j].trim());
                            j += 1;
                        }
                        pf.decls.push(DraftDecl {
                            name,
                            kind: DeclKind::Data,
                            statement: normalise_ws(&stmt),
                            proof: None,
                            line: line_no,
                            axiom_usage: AxiomUsage::default(),
                        });
                        i = j;
                        continue;
                    }
                }
            }
            if let Some(rest) = line.trim_start().strip_prefix("record ") {
                let name: String = rest
                    .chars()
                    .take_while(|c| !c.is_whitespace() && *c != ':')
                    .collect();
                if !name.is_empty() {
                    let stmt = line.trim().to_string();
                    pf.decls.push(DraftDecl {
                        name,
                        kind: DeclKind::Record,
                        statement: stmt,
                        proof: None,
                        line: line_no,
                        axiom_usage: AxiomUsage::default(),
                    });
                    i += 1;
                    continue;
                }
            }
        }

        // `name : ty` at column 0.
        if column_of(line) == 0 {
            if let Some((name, statement_first)) = split_typesig(line) {
                if is_plausible_ident(&name) {
                    let mut statement = statement_first;
                    let mut j = i + 1;
                    // Continuation: indented lines until next column-0 line.
                    while j < lines.len() {
                        let nl = lines[j];
                        if nl.trim().is_empty() {
                            j += 1;
                            break;
                        }
                        if column_of(nl) == 0 {
                            break;
                        }
                        statement.push(' ');
                        statement.push_str(nl.trim());
                        j += 1;
                    }
                    let statement = normalise_ws(&statement);

                    // Look for the defining equation. Search forward
                    // from j for the first column-0 line that starts
                    // with this name.
                    let mut proof: Option<String> = None;
                    let mut k = j;
                    while k < lines.len() && lines[k].trim().is_empty() {
                        k += 1;
                    }
                    if k < lines.len() && column_of(lines[k]) == 0 {
                        let kl = lines[k];
                        let owns = |l: &str| -> bool {
                            let t = l.trim_start();
                            t.starts_with(&format!("{} ", name))
                                || t.starts_with(&format!("{} =", name))
                                || t == name
                        };
                        if owns(kl) {
                            let mut body = String::new();
                            body.push_str(kl.trim());
                            let mut m = k + 1;
                            // Accept indented continuation lines AND
                            // additional column-0 clauses owned by the
                            // same name (multi-clause function bodies
                            // and `where` blocks).
                            while m < lines.len() {
                                let bl = lines[m];
                                if bl.trim().is_empty() {
                                    m += 1;
                                    break;
                                }
                                if column_of(bl) == 0 {
                                    if owns(bl) {
                                        body.push(' ');
                                        body.push_str(bl.trim());
                                        m += 1;
                                        continue;
                                    }
                                    break;
                                }
                                body.push(' ');
                                body.push_str(bl.trim());
                                m += 1;
                            }
                            proof = Some(normalise_ws(&body));
                            j = m;
                        }
                    }

                    let mut hz = AxiomUsage::default();
                    let scan_text = {
                        let from = line_no.saturating_sub(1);
                        let to = j.min(raw_lines.len());
                        raw_lines[from..to].join("\n")
                    };
                    flag_hazards(&scan_text, &mut hz);

                    pf.decls.push(DraftDecl {
                        name,
                        kind: DeclKind::Function,
                        statement,
                        proof,
                        line: line_no,
                        axiom_usage: hz,
                    });
                    i = j;
                    continue;
                }
            }
        }

        i += 1;
    }

    pf
}

/// Column (in chars, not bytes) of the first non-whitespace char.
fn column_of(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

/// Split `name : type` at the first top-level `:`. Returns `None` if
/// the line doesn't look like a type signature. "Top-level" here means
/// not inside parens / brackets / braces — Agda uses `:` inside
/// implicit and instance argument binders too.
fn split_typesig(line: &str) -> Option<(String, String)> {
    let line = line.trim();
    let mut depth_paren: i32 = 0;
    let mut depth_bracket: i32 = 0;
    let mut depth_brace: i32 = 0;
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        match c {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            '{' => depth_brace += 1,
            '}' => depth_brace -= 1,
            ':' if depth_paren == 0 && depth_bracket == 0 && depth_brace == 0 => {
                // Reject `::`.
                if i + 1 < chars.len() && chars[i + 1] == ':' {
                    i += 2;
                    continue;
                }
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                let lhs = lhs.trim();
                if lhs.is_empty() || lhs.contains('=') {
                    return None;
                }
                // Reject keyword starts.
                let keywords = [
                    "module", "data", "record", "open", "import", "where",
                    "postulate", "private", "abstract", "instance", "syntax",
                    "let", "in", "primitive", "macro", "infixl", "infixr",
                    "infix", "{-#",
                ];
                let head = lhs.split_whitespace().next().unwrap_or("");
                if keywords.contains(&head) {
                    return None;
                }
                return Some((lhs.to_string(), rhs.trim().to_string()));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn is_plausible_ident(s: &str) -> bool {
    !s.is_empty()
        && !s.contains(' ')
        && s.chars()
            .next()
            .map(|c| !c.is_whitespace() && c != ':' && c != '=')
            .unwrap_or(false)
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Tokenise on whitespace and Agda-syntax separators that can't appear
/// inside an identifier. Agda allows almost anything in identifiers
/// (subscripts, primes, dashes, Unicode), so the splitter has to be
/// conservative. We split on whitespace plus `()`, `[]`, `{}`, `,`,
/// `;`, `=`, `→`, `≡`, `:` — the syntactic glue.
fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '='
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    // Token-based contains-checks. Substring matches are intentional:
    // we want to flag `believe_me` regardless of surrounding
    // whitespace. False positives in headers or notes are tolerated;
    // see `feedback_code_only_grep_for_banned_patterns` for the
    // estate-wide convention to spot-check rather than chase the
    // count.
    if text.contains("believe_me") {
        hz.believe_me = true;
    }
    if text.contains("assert_total") {
        hz.assert_total = true;
    }
    if text.contains("Admitted") {
        hz.admitted = true;
    }
    if text.contains("sorry") {
        hz.sorry = true;
    }
    if text.contains("unsafeCoerce") || text.contains("Obj.magic") {
        hz.trustme = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note on test fixtures: don't use Rust line-continuation (`\\\n`)
    // for the source — it strips leading whitespace and silently
    // moves indented decls to column 0. Use explicit `\n` plus
    // literal spaces.

    #[test]
    fn parses_module_name_and_options() {
        let src = "{-# OPTIONS --safe --without-K #-}\n\nmodule Ordinal.Brouwer where\n\ndata Ord : Set where\n  oz : Ord\n";
        let pf = parse_agda_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("Ordinal.Brouwer"));
        assert!(pf.options.iter().any(|o| o == "--safe"));
        assert!(pf.options.iter().any(|o| o == "--without-K"));
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "Ord");
        assert_eq!(pf.decls[0].kind, DeclKind::Data);
    }

    #[test]
    fn parses_typesig_with_continuation() {
        let src = "module M where\nwf-< : WellFounded _<_\nwf-< oz       = acc \u{03bb} ()\nwf-< (osuc \u{03b1}) = acc (pred-of-osuc (wf-< \u{03b1}))\n";
        let pf = parse_agda_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "wf-<");
        assert_eq!(pf.decls[0].statement, "WellFounded _<_");
        let body = pf.decls[0].proof.as_deref().unwrap();
        assert!(body.contains("acc"), "body missing 'acc': {}", body);
        // Multi-clause: both equations should be in the body.
        assert!(
            body.contains("pred-of-osuc"),
            "body missing 'pred-of-osuc' (multi-clause not captured): {}",
            body
        );
    }

    #[test]
    fn detects_postulate_block() {
        let src = "module M where\npostulate\n  foo : \u{22a4}\n  bar : \u{2115}\n";
        let pf = parse_agda_file(src);
        let names: Vec<_> = pf.decls.iter().map(|d| (&d.name, d.kind)).collect();
        assert!(names
            .iter()
            .any(|(n, k)| *n == "foo" && *k == DeclKind::Postulate));
        assert!(names
            .iter()
            .any(|(n, k)| *n == "bar" && *k == DeclKind::Postulate));
    }

    #[test]
    fn flags_believe_me_in_proof_body() {
        let src = "module M where\nbad : \u{22a4}\nbad = believe_me\n";
        let pf = parse_agda_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0].axiom_usage.believe_me);
    }
}
