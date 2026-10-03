// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! MetaMath adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.mm` file, and extracts a
//! structural index of MetaMath statements. Follows the same heuristic-
//! over-full-parser approach the Agda adapter uses.
//!
//! MetaMath syntax recap:
//!
//! - `$c <constants> $.` — constant declaration
//! - `$v <variables> $.` — variable declaration
//! - `$f <typecode> <var> $.` — floating hypothesis
//! - `$e <typecode> <expression> $.` — essential hypothesis
//! - `$a <typecode> <expression> $.` — **axiom** (primary hazard)
//! - `$p <typecode> <expression> $= <proof> $.` — provable statement
//! - `$d <vars> $.` — disjoint-variable constraint
//! - `$( ... $)` — block comment (multi-line; nesting not permitted)
//! - `${ ... $}` — scope block (qualifies enclosed labels)
//! - `$j ...` — junk metadata (Metamath proof-explorer extensions)
//!
//! Mapping into the generic corpus model:
//!
//! - `$p` → `DeclKind::Function` (statement = post-`$p` typecode+expr,
//!   proof = the `$=` … `$.` body)
//! - `$a` → `DeclKind::Postulate` (axiom — `axiom_usage.postulate = true`)
//! - `$c`/`$v`/`$f`/`$e` → `DeclKind::Module` (typing infrastructure)
//! - `$d` → not a decl; tracked as scope-level constraint info
//!
//! Hazard detection:
//!
//! - `$a` axiom → `axiom_usage.postulate = true`
//! - `?` token inside a `$p` proof body → `axiom_usage.admitted = true`
//!   (Metamath uses `?` as the "unknown / placeholder step" marker)
//! - `$j` directives are recorded under `axiom_usage.other`.
//!
//! Module name: derived from the first `$( ... $)` comment if it
//! contains a recognisable title line, otherwise from the filename
//! stem. MetaMath is a single flat namespace, so `imports` is always
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
    walk_mm(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "metamath".to_string(),
        ..Default::default()
    };

    // Pass 1: parse each file into draft module + draft entries.
    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_mm_file(&raw);

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
            options: parsed.options, // $j directives / $d constraints
            imports: Vec::new(),     // flat namespace
            entries: Vec::new(),
        };
        corpus.modules.push(module_entry);

        for d in parsed.decls {
            let entry_idx = corpus.entries.len();
            let qualified = if d.scope.is_empty() {
                format!("{}.{}", module_name, d.name)
            } else {
                format!("{}.{}.{}", module_name, d.scope, d.name)
            };
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
                dependencies: Vec::new(), // pass 2
                axiom_usage: d.axiom_usage,
            });
        }
    }

    // Pass 2: resolve dependencies by textual reference.
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

fn walk_mm(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
            walk_mm(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("mm") {
            out.push(p);
        }
    }
    Ok(())
}

#[derive(Debug, Default)]
struct ParsedFile {
    module_name: Option<String>,
    /// `$j` directives + `$d` constraints, recorded verbatim.
    options: Vec<String>,
    decls: Vec<DraftDecl>,
}

#[derive(Debug)]
struct DraftDecl {
    name: String,
    /// Dotted scope path (joined `${...$}` labels), empty at top level.
    scope: String,
    kind: DeclKind,
    statement: String,
    proof: Option<String>,
    line: usize,
    axiom_usage: AxiomUsage,
}

/// A single lexed token: either a chunk of source whitespace-separated,
/// or one of MetaMath's `$X` keywords / `$.` terminators / `${`/`$}`
/// scope markers. Block comments `$( ... $)` are dropped at this stage.
#[derive(Debug, Clone)]
struct Token {
    text: String,
    line: usize,
}

/// Lex `src` into tokens, dropping block comments but preserving line
/// numbers on every emitted token.
fn lex(src: &str) -> Vec<Token> {
    let mut out: Vec<Token> = Vec::new();
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut line: usize = 1;
    let mut in_comment = false;

    let mut tok_start: Option<usize> = None;
    let mut tok_line: usize = 1;

    while i < bytes.len() {
        let c = bytes[i];
        if in_comment {
            // End of block comment is the two-byte sequence "$)".
            if i + 1 < bytes.len() && c == b'$' && bytes[i + 1] == b')' {
                in_comment = false;
                i += 2;
                continue;
            }
            if c == b'\n' {
                line += 1;
            }
            i += 1;
            continue;
        }

        // Detect block-comment open `$(` only when NOT mid-token.
        if tok_start.is_none() && c == b'$' && i + 1 < bytes.len() && bytes[i + 1] == b'(' {
            in_comment = true;
            i += 2;
            continue;
        }

        let is_ws = matches!(c, b' ' | b'\t' | b'\r' | b'\n');
        if is_ws {
            if let Some(s) = tok_start.take() {
                let text = std::str::from_utf8(&bytes[s..i]).unwrap_or("").to_string();
                if !text.is_empty() {
                    out.push(Token {
                        text,
                        line: tok_line,
                    });
                }
            }
            if c == b'\n' {
                line += 1;
            }
            i += 1;
            continue;
        }

        if tok_start.is_none() {
            tok_start = Some(i);
            tok_line = line;
        }
        i += 1;
    }
    if let Some(s) = tok_start.take() {
        let text = std::str::from_utf8(&bytes[s..]).unwrap_or("").to_string();
        if !text.is_empty() {
            out.push(Token {
                text,
                line: tok_line,
            });
        }
    }
    out
}

/// Extract a module name from the first non-empty block comment, if it
/// looks like a title line. MetaMath set.mm starts with a long
/// `$( ... $)` preamble whose first prominent text is the database
/// title.
fn extract_module_name(src: &str) -> Option<String> {
    let bytes = src.as_bytes();
    let mut i = 0;
    // Walk to first `$(`.
    while i + 1 < bytes.len() {
        if bytes[i] == b'$' && bytes[i + 1] == b'(' {
            let start = i + 2;
            // Find closing `$)`.
            let mut j = start;
            while j + 1 < bytes.len() {
                if bytes[j] == b'$' && bytes[j + 1] == b')' {
                    let inner = std::str::from_utf8(&bytes[start..j]).unwrap_or("");
                    for line in inner.lines() {
                        let t = line.trim();
                        if t.is_empty() {
                            continue;
                        }
                        // Heuristic: a "Set theory" / "Title:" / "*" -
                        // style line is the database name.
                        if let Some(rest) = t.strip_prefix("Set theory") {
                            let r = rest.trim_start_matches([':', ' ', '-']).trim();
                            let head = r.split_whitespace().next().unwrap_or("set_theory");
                            return Some(format!("set_theory_{}", head));
                        }
                        if let Some(rest) = t.strip_prefix("Title:") {
                            return Some(
                                rest.trim()
                                    .replace(char::is_whitespace, "_")
                                    .trim_matches('_')
                                    .to_string(),
                            );
                        }
                    }
                    return None;
                }
                j += 1;
            }
            return None;
        }
        i += 1;
    }
    None
}

fn parse_mm_file(raw: &str) -> ParsedFile {
    let mut pf = ParsedFile {
        module_name: extract_module_name(raw),
        ..Default::default()
    };

    let toks = lex(raw);
    let mut scope_stack: Vec<String> = Vec::new();
    let mut auto_scope_idx: usize = 0;

    // Recognised statement keywords.
    let stmt_keywords = ["$c", "$v", "$f", "$e", "$a", "$p", "$d"];

    let mut i = 0;
    while i < toks.len() {
        let t = &toks[i];
        // Scope open.
        if t.text == "${" {
            auto_scope_idx += 1;
            scope_stack.push(format!("scope{}", auto_scope_idx));
            i += 1;
            continue;
        }
        if t.text == "$}" {
            scope_stack.pop();
            i += 1;
            continue;
        }

        // `$j` junk-metadata directive: skip to next `$.`, record it.
        if t.text == "$j" {
            let mut body = String::new();
            let line = t.line;
            i += 1;
            while i < toks.len() && toks[i].text != "$." {
                if !body.is_empty() {
                    body.push(' ');
                }
                body.push_str(&toks[i].text);
                i += 1;
            }
            if i < toks.len() {
                i += 1; // consume $.
            }
            pf.options.push(format!("$j@{} {}", line, body));
            continue;
        }

        // Check whether the next "real" token is a stmt keyword. If
        // yes and there's a token before it, that prior token is the
        // label. (Labels precede `$f`, `$e`, `$a`, `$p`; not `$c`,
        // `$v`, `$d`.)
        let kw = t.text.as_str();
        if stmt_keywords.contains(&kw) {
            // Unlabelled forms: $c / $v / $d (and rare unlabelled $f).
            let line = t.line;
            let mut payload: Vec<String> = Vec::new();
            let mut j = i + 1;
            while j < toks.len() && toks[j].text != "$." && toks[j].text != "$=" {
                payload.push(toks[j].text.clone());
                j += 1;
            }
            // Skip $. terminator.
            if j < toks.len() && toks[j].text == "$." {
                j += 1;
            }
            match kw {
                "$c" | "$v" => {
                    pf.options
                        .push(format!("{}@{} {}", kw, line, payload.join(" ")));
                },
                "$d" => {
                    pf.options
                        .push(format!("$d@{} {}", line, payload.join(" ")));
                },
                _ => {
                    // labelled forms reached without a preceding label
                    // (malformed); record as option for visibility.
                    pf.options
                        .push(format!("{}@{} (no label) {}", kw, line, payload.join(" ")));
                },
            }
            i = j;
            continue;
        }

        // Otherwise this token might be a label followed by `$X`.
        if i + 1 < toks.len() {
            let nxt = &toks[i + 1];
            if stmt_keywords.contains(&nxt.text.as_str()) {
                let label = t.text.clone();
                let kw = nxt.text.clone();
                let line = t.line;
                // Read until $. (and capture $= proof body for $p).
                let mut statement_toks: Vec<String> = Vec::new();
                let mut proof_toks: Vec<String> = Vec::new();
                let mut j = i + 2;
                let mut in_proof = false;
                while j < toks.len() && toks[j].text != "$." {
                    if toks[j].text == "$=" {
                        in_proof = true;
                        j += 1;
                        continue;
                    }
                    if in_proof {
                        proof_toks.push(toks[j].text.clone());
                    } else {
                        statement_toks.push(toks[j].text.clone());
                    }
                    j += 1;
                }
                if j < toks.len() {
                    j += 1; // consume $.
                }

                let scope = scope_stack.join(".");
                let statement = statement_toks.join(" ");
                let proof_body = if proof_toks.is_empty() {
                    None
                } else {
                    Some(proof_toks.join(" "))
                };

                let (kind, hazard) = match kw.as_str() {
                    "$p" => {
                        let mut hz = AxiomUsage::default();
                        if let Some(p) = &proof_body {
                            // `?` in proof body = unknown step.
                            if p.split_whitespace().any(|t| t == "?") {
                                hz.admitted = true;
                            }
                        }
                        (DeclKind::Function, hz)
                    },
                    "$a" => {
                        let hz = AxiomUsage {
                            postulate: true,
                            ..Default::default()
                        };
                        (DeclKind::Postulate, hz)
                    },
                    "$f" | "$e" => (DeclKind::Module, AxiomUsage::default()),
                    _ => (DeclKind::Module, AxiomUsage::default()),
                };

                pf.decls.push(DraftDecl {
                    name: label,
                    scope,
                    kind,
                    statement,
                    proof: proof_body,
                    line,
                    axiom_usage: hazard,
                });
                i = j;
                continue;
            }
        }

        // Stray token — skip.
        i += 1;
    }

    pf
}

/// Tokenise on whitespace and MetaMath glue. Identifiers (labels and
/// constant/variable symbols) can contain almost any printable ASCII
/// except whitespace and `$`, so the splitter is conservative.
fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| c.is_whitespace() || c == '$')
        .filter(|t| !t.is_empty())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_axiom_and_provable() {
        // Minimal: one $a axiom (mp), one $p theorem that cites it.
        let src = concat!(
            "$( Mini test database $)\n",
            "$c wff |- ( ) -> $.\n",
            "$v ph ps $.\n",
            "wph $f wff ph $.\n",
            "wps $f wff ps $.\n",
            "ax-mp $a |- ps $.\n",
            "id $p |- ( ph -> ph ) $= wph wph ax-mp $.\n",
        );
        let pf = parse_mm_file(src);
        // Names of labelled decls.
        let names: Vec<&str> = pf.decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"ax-mp"), "missing ax-mp: {:?}", names);
        assert!(names.contains(&"id"), "missing id: {:?}", names);

        let ax = pf.decls.iter().find(|d| d.name == "ax-mp").unwrap();
        assert_eq!(ax.kind, DeclKind::Postulate);
        assert!(
            ax.axiom_usage.postulate,
            "ax-mp should be flagged as postulate"
        );

        let id = pf.decls.iter().find(|d| d.name == "id").unwrap();
        assert_eq!(id.kind, DeclKind::Function);
        assert!(id.proof.as_deref().unwrap_or("").contains("ax-mp"));
        assert!(!id.axiom_usage.postulate);
    }

    #[test]
    fn detects_axiom_hazard_via_dollar_a() {
        let src = "$c wff $.\nax-bogus $a wff foo $.\n";
        let pf = parse_mm_file(src);
        let ax = pf.decls.iter().find(|d| d.name == "ax-bogus").unwrap();
        assert_eq!(ax.kind, DeclKind::Postulate);
        assert!(ax.axiom_usage.postulate);
    }

    #[test]
    fn detects_question_mark_admitted_in_proof() {
        let src = "$c wff $.\nopen $p wff foo $= ? $.\n";
        let pf = parse_mm_file(src);
        let open = pf.decls.iter().find(|d| d.name == "open").unwrap();
        assert_eq!(open.kind, DeclKind::Function);
        assert!(
            open.axiom_usage.admitted,
            "`?` in proof body should set admitted=true"
        );
    }

    #[test]
    fn scope_block_qualifies_label() {
        let src = concat!("$c wff $.\n", "${\n", "inner $a wff bar $.\n", "$}\n",);
        let pf = parse_mm_file(src);
        let inner = pf.decls.iter().find(|d| d.name == "inner").unwrap();
        assert!(
            inner.scope.starts_with("scope"),
            "expected scope qualifier, got `{}`",
            inner.scope
        );
    }

    #[test]
    fn block_comment_is_dropped_but_lines_preserved() {
        let src = "$( first line\n   second line $)\nfoo $a wff bar $.\n";
        let pf = parse_mm_file(src);
        // `foo` is on line 3 of the source.
        let foo = pf.decls.iter().find(|d| d.name == "foo").unwrap();
        assert_eq!(foo.line, 3);
    }
}
