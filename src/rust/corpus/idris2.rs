// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Idris 2 adapter for the corpus indexer — Step 2 of the N-dim plan.
//!
//! Idris 2's surface syntax is close to Agda's:
//!
//! - Comments: `-- …` line, `{- … -}` block (nestable). `||| …` is a
//!   documentation comment.
//! - Module declaration: `module M.N` (no `where` keyword).
//! - Imports: `import M.N` / `import public M.N`.
//! - Top-level decls: `name : ty` followed by `name args = body`.
//! - Data: `data Foo : ty where … constructors …`.
//! - Records: `record Foo where …`.
//! - Postulates: rare in Idris (`postulate` is supported but
//!   discouraged; `partial + idris_crash` is the project convention
//!   per memory).
//! - Pragmas: `%foreign`, `%default total`, `%hint`, etc.
//!
//! Hazards: `believe_me`, `assert_total`, `assert_smaller`,
//! `unsafePerformIO`, `idris_crash`, `postulate` block.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_idr(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "idris2".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;
        let parsed = parse_idris_file(&raw);

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

fn walk_idr(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir)
        .with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name_s = entry.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if matches!(
                name_s.as_str(),
                "_build" | ".git" | "node_modules" | "target" | ".cache" | "build" | "depends"
            ) {
                continue;
            }
            walk_idr(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("idr") {
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

/// Strip Idris 2 comments. `-- …` to EOL; `{- … -}` nestable. `||| …`
/// is a doc-comment which we treat as a line comment for stripping.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut depth: usize = 0;
    while i < bytes.len() {
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'}' {
                depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' {
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
        if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' {
            depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        if i + 2 < bytes.len() && bytes[i] == b'|' && bytes[i + 1] == b'|' && bytes[i + 2] == b'|' {
            // Doc comment ||| …, runs to EOL.
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
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

fn parse_idris_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();
    let lines: Vec<&str> = stripped.lines().collect();
    let raw_lines: Vec<&str> = raw.lines().collect();

    // Module declaration.
    for line in &lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("module ") {
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

    // Pragmas (%default, %foreign, ...).
    for line in &lines {
        let t = line.trim_start();
        if t.starts_with('%') {
            let pragma: String = t.split_whitespace().take(2).collect::<Vec<_>>().join(" ");
            if !pragma.is_empty() {
                pf.options.push(pragma);
            }
        }
    }

    // Imports.
    for line in &lines {
        let t = line.trim_start();
        let candidate = t
            .strip_prefix("import public ")
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

    let mut i = 0;
    let mut in_postulate_block = false;
    let mut postulate_block_indent: Option<usize> = None;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;

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
            }
        }

        // Single-line postulate.
        if column_of(line) == 0 {
            if let Some(rest) = line.trim_start().strip_prefix("postulate ") {
                if let Some((name, statement)) = split_typesig(rest) {
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
                    i += 1;
                    continue;
                }
            }
        }

        // `data N : … where` / `data N where`.
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
                    pf.decls.push(DraftDecl {
                        name,
                        kind: DeclKind::Record,
                        statement: line.trim().to_string(),
                        proof: None,
                        line: line_no,
                        axiom_usage: AxiomUsage::default(),
                    });
                    i += 1;
                    continue;
                }
            }
            if let Some(rest) = line.trim_start().strip_prefix("interface ") {
                let name: String = rest
                    .chars()
                    .take_while(|c| !c.is_whitespace() && *c != ':')
                    .collect();
                if !name.is_empty() {
                    pf.decls.push(DraftDecl {
                        name,
                        kind: DeclKind::Record,
                        statement: line.trim().to_string(),
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

fn column_of(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

fn split_typesig(line: &str) -> Option<(String, String)> {
    let line = line.trim();
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            '(' => paren += 1,
            ')' => paren -= 1,
            '[' => bracket += 1,
            ']' => bracket -= 1,
            '{' => brace += 1,
            '}' => brace -= 1,
            ':' if paren == 0 && bracket == 0 && brace == 0 => {
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
                let head = lhs.split_whitespace().next().unwrap_or("");
                let keywords = [
                    "module",
                    "data",
                    "record",
                    "interface",
                    "implementation",
                    "import",
                    "where",
                    "postulate",
                    "private",
                    "public",
                    "export",
                    "covering",
                    "partial",
                    "total",
                    "%default",
                    "%foreign",
                    "%hint",
                    "namespace",
                    "infixl",
                    "infixr",
                    "infix",
                    "prefix",
                ];
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

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '=')
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("believe_me") {
        hz.believe_me = true;
    }
    if text.contains("assert_total") || text.contains("assert_smaller") {
        hz.assert_total = true;
    }
    if text.contains("idris_crash") {
        hz.other.push("idris_crash".into());
    }
    if text.contains("unsafePerformIO") {
        hz.trustme = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_module_and_imports() {
        let src = "module Eclexia.ABI.Foreign\n\nimport Eclexia.ABI.Types\nimport public Eclexia.ABI.Layout\n%default total\n";
        let pf = parse_idris_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("Eclexia.ABI.Foreign"));
        assert!(pf.imports.iter().any(|m| m == "Eclexia.ABI.Types"));
        assert!(pf.imports.iter().any(|m| m == "Eclexia.ABI.Layout"));
        assert!(pf.options.iter().any(|o| o.contains("total")));
    }

    #[test]
    fn parses_function_with_body() {
        let src = "module M\n\nadd : Nat -> Nat -> Nat\nadd Z y = y\nadd (S k) y = S (add k y)\n";
        let pf = parse_idris_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "add");
        assert_eq!(pf.decls[0].statement, "Nat -> Nat -> Nat");
        let body = pf.decls[0].proof.as_deref().unwrap();
        assert!(body.contains("Z y"), "got {}", body);
        assert!(body.contains("S k"), "got {}", body);
    }

    #[test]
    fn flags_believe_me() {
        let src = "module M\n\nbad : a -> b\nbad x = believe_me x\n";
        let pf = parse_idris_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0].axiom_usage.believe_me);
    }

    #[test]
    fn flags_idris_crash() {
        let src = "module M\n\npartial\nstub : Nat\nstub = idris_crash \"todo\"\n";
        let pf = parse_idris_file(src);
        let any_crash = pf
            .decls
            .iter()
            .any(|d| d.axiom_usage.other.iter().any(|s| s == "idris_crash"));
        assert!(any_crash, "should flag idris_crash");
    }

    #[test]
    fn handles_doc_comments() {
        let src = "module M\n\n||| Doc for foo.\nfoo : Nat\nfoo = 0\n";
        let pf = parse_idris_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "foo");
    }

    #[test]
    fn parses_data() {
        let src = "module M\n\ndata Foo : Type where\n  Bar : Foo\n  Baz : Foo\n";
        let pf = parse_idris_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "Foo");
        assert_eq!(pf.decls[0].kind, DeclKind::Data);
    }

    #[test]
    fn parses_record() {
        let src = "module M\n\nrecord Pair where\n  fst : Nat\n  snd : Nat\n";
        let pf = parse_idris_file(src);
        let rec = pf.decls.iter().find(|d| d.name == "Pair");
        assert!(rec.is_some(), "expected Pair record");
        assert_eq!(rec.unwrap().kind, DeclKind::Record);
    }
}
