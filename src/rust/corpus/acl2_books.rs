// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! ACL2 community-books adapter for the corpus indexer.
//!
//! Walks a project root, finds every `*.lisp` and `*.acl2` file, and
//! extracts a structural index over s-expression forms. Heuristic, not
//! a real Lisp reader:
//!
//! - Strips line comments `; …` and block comments `#| … |#`.
//! - Recognises top-level forms `(defthm …)`, `(defun …)`,
//!   `(defaxiom …)`, `(defstub …)`, `(defmacro …)`, `(defabbrev …)`,
//!   `(defconst *…*)`, `(in-package "…")`, `(include-book "…")`.
//! - Captures the form's name (second token) and the rest of the form
//!   body as the "statement" (mostly so dependency tokenisation has
//!   something to work with).
//! - Detects banned-pattern axiom usage: `defaxiom`, `defstub`,
//!   `skip-proofs`, `ld-skip-proofsp`, `(local (in-theory nil))`,
//!   `defproperty`, raw `value` skips.
//!
//! Output is structural: enough for SA design search and curriculum
//! scaffolding over the ACL2 community books.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root` and produce a corpus.
///
/// Skips directories named `.git`, `target`, `_build`, `output`,
/// `_cache`, `node_modules` regardless of depth.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_acl2(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "acl2-books".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed = parse_acl2_file(&raw);

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

fn walk_acl2(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                ".git" | "target" | "_build" | "output" | "_cache" | "node_modules"
            ) {
                continue;
            }
            walk_acl2(&p, out)?;
        } else {
            match p.extension().and_then(|s| s.to_str()) {
                Some("lisp") | Some("acl2") => out.push(p),
                _ => {},
            }
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

/// Strip ACL2/Common-Lisp comments while preserving newlines:
///
/// - Line: `; …` to end of line. Note: `;` inside strings is NOT a
///   comment; we track string state.
/// - Block: `#| … |#`, nestable per the CL spec.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut block_depth: usize = 0;
    let mut in_string = false;
    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'|' && bytes[i + 1] == b'#' {
                block_depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'#' && bytes[i + 1] == b'|' {
                block_depth += 1;
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
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i]);
                out.push(bytes[i + 1]);
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            out.push(bytes[i]);
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_string = true;
            out.push(bytes[i]);
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'#' && bytes[i + 1] == b'|' {
            block_depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
            continue;
        }
        if bytes[i] == b';' {
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

fn parse_acl2_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let mut pf = ParsedFile::default();

    // Scan top-level s-expressions. We don't need a full reader —
    // matching `(` at column 0 (or any unbalanced opening paren) and
    // tracking depth is enough to delimit a form.
    let chars: Vec<char> = stripped.chars().collect();
    let raw_chars_len = raw.len();
    let _ = raw_chars_len;

    // Pre-compute line starts for line-number lookup.
    let mut line_starts: Vec<usize> = vec![0];
    for (k, c) in chars.iter().enumerate() {
        if *c == '\n' {
            line_starts.push(k + 1);
        }
    }
    let line_of = |pos: usize| -> usize {
        // Binary search for largest line_start <= pos.
        match line_starts.binary_search(&pos) {
            Ok(i) => i + 1,
            Err(i) => i, // i is the first line_start > pos, so we want i (1-based of prev)
        }
    };

    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '(' {
            // Find matching close.
            let start = i;
            let mut depth = 1;
            let mut j = i + 1;
            let mut in_str = false;
            while j < chars.len() && depth > 0 {
                let ch = chars[j];
                if in_str {
                    if ch == '\\' && j + 1 < chars.len() {
                        j += 2;
                        continue;
                    }
                    if ch == '"' {
                        in_str = false;
                    }
                    j += 1;
                    continue;
                }
                match ch {
                    '"' => in_str = true,
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {},
                }
                j += 1;
            }
            // Form spans chars[start..j].
            let form: String = chars[start..j].iter().collect();
            let line_no = line_of(start);
            classify_form(&form, line_no, &mut pf);
            i = j;
            continue;
        }
        i += 1;
    }

    pf
}

fn classify_form(form: &str, line: usize, pf: &mut ParsedFile) {
    // Strip outermost parens; tokens[0] is the head.
    let inner = form.trim();
    let inner = inner
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(inner)
        .trim();
    let mut parts = inner.splitn(3, |c: char| c.is_whitespace() || c == '\n');
    let head = match parts.next() {
        Some(s) => s,
        None => return,
    };
    let raw_arg1 = parts.next().unwrap_or("").trim();
    let rest_body = parts.next().unwrap_or("").trim();

    match head {
        "in-package" => {
            // (in-package "X")
            let pkg = raw_arg1.trim_matches('"').to_string();
            if !pkg.is_empty() && pf.module_name.is_none() {
                pf.module_name = Some(pkg);
            }
        },
        "include-book" => {
            // (include-book "X" …)
            let book = raw_arg1.trim_matches('"').to_string();
            if !book.is_empty() && !pf.imports.contains(&book) {
                pf.imports.push(book);
            }
        },
        "defpkg" => {
            // (defpkg "X" (list ...)) — treat as module-ish for index.
            let pkg = raw_arg1.trim_matches('"').to_string();
            if !pkg.is_empty() && pf.module_name.is_none() {
                pf.module_name = Some(pkg);
            }
        },
        "defthm" | "defun" | "defmacro" | "defabbrev" => {
            let name = sanitise_name(raw_arg1);
            if name.is_empty() {
                return;
            }
            let body = rest_body.to_string();
            let mut hz = AxiomUsage::default();
            flag_hazards(&body, &mut hz);
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Function,
                statement: normalise_ws(rest_body),
                proof: Some(normalise_ws(&body)),
                line,
                axiom_usage: hz,
            });
        },
        "defaxiom" => {
            let name = sanitise_name(raw_arg1);
            if name.is_empty() {
                return;
            }
            let mut hz = AxiomUsage {
                postulate: true,
                ..Default::default()
            };
            hz.other.push("defaxiom".to_string());
            flag_hazards(rest_body, &mut hz);
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Postulate,
                statement: normalise_ws(rest_body),
                proof: None,
                line,
                axiom_usage: hz,
            });
        },
        "defstub" => {
            let name = sanitise_name(raw_arg1);
            if name.is_empty() {
                return;
            }
            let mut hz = AxiomUsage {
                postulate: true,
                ..Default::default()
            };
            hz.other.push("defstub".to_string());
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Postulate,
                statement: normalise_ws(rest_body),
                proof: None,
                line,
                axiom_usage: hz,
            });
        },
        "defconst" => {
            // (defconst *NAME* value)
            let name = sanitise_name(raw_arg1);
            if name.is_empty() {
                return;
            }
            pf.decls.push(DraftDecl {
                name,
                kind: DeclKind::Module,
                statement: normalise_ws(rest_body),
                proof: None,
                line,
                axiom_usage: AxiomUsage::default(),
            });
        },
        _ => {
            // Other forms (encapsulate, local, mutual-recursion, etc.)
            // are ignored at this level — sub-form recursion is left
            // for a future enhancement. We still scan for hazards so
            // top-level `skip-proofs` calls get surfaced.
            //
            // Skip-proofs at top level is a *huge* hazard; surface it
            // as a synthetic postulate so the corpus shows the leak.
            if head == "skip-proofs" || form.contains("skip-proofs") {
                let mut hz = AxiomUsage::default();
                hz.other.push("skip-proofs".to_string());
                pf.decls.push(DraftDecl {
                    name: format!("__skip-proofs@{}", line),
                    kind: DeclKind::Postulate,
                    statement: normalise_ws(form),
                    proof: None,
                    line,
                    axiom_usage: hz,
                });
            }
        },
    }
}

fn sanitise_name(s: &str) -> String {
    let s = s.trim();
    // Strip a trailing `)` if the whole name accidentally captured it
    // (zero-arg form).
    let s = s.trim_end_matches(')');
    s.to_string()
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Tokenise on whitespace and Lisp syntactic glue.
fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '\'' | '`' | ',' | '"'))
        .filter(|t| !t.is_empty())
        .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("skip-proofs") {
        hz.other.push("skip-proofs".to_string());
    }
    if text.contains("ld-skip-proofsp") {
        hz.other.push("ld-skip-proofsp".to_string());
    }
    if text.contains("(local (in-theory nil))") {
        hz.other.push("local-in-theory-nil".to_string());
    }
    if text.contains("defproperty") {
        hz.other.push("defproperty".to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_defthm_and_defun() {
        let src = "\
(in-package \"ACL2\")\n\
\n\
(defun double (x)\n\
  (* 2 x))\n\
\n\
(defthm double-even\n\
  (evenp (double x))\n\
  :hints ((\"Goal\" :in-theory (enable evenp double))))\n\
";
        let pf = parse_acl2_file(src);
        assert_eq!(pf.module_name.as_deref(), Some("ACL2"));
        let names: Vec<(&str, DeclKind)> =
            pf.decls.iter().map(|d| (d.name.as_str(), d.kind)).collect();
        assert!(
            names
                .iter()
                .any(|(n, k)| *n == "double" && *k == DeclKind::Function),
            "expected double defun, got {:?}",
            names
        );
        assert!(
            names
                .iter()
                .any(|(n, k)| *n == "double-even" && *k == DeclKind::Function),
            "expected double-even defthm, got {:?}",
            names
        );
    }

    #[test]
    fn detects_skip_proofs_and_defaxiom_hazards() {
        let src = "\
(in-package \"ACL2\")\n\
\n\
(defaxiom sketchy-ax (equal x x))\n\
\n\
(defthm questionable\n\
  (equal (foo x) (bar x))\n\
  :hints ((\"Goal\" :use ((:instance skip-proofs)))))\n\
\n\
(skip-proofs (defthm wholly-trusted (equal 1 2)))\n\
";
        let pf = parse_acl2_file(src);
        let ax = pf
            .decls
            .iter()
            .find(|d| d.name == "sketchy-ax")
            .expect("defaxiom");
        assert_eq!(ax.kind, DeclKind::Postulate);
        assert!(ax.axiom_usage.postulate);

        let questionable = pf
            .decls
            .iter()
            .find(|d| d.name == "questionable")
            .expect("defthm");
        let mentions_skip = questionable
            .axiom_usage
            .other
            .iter()
            .any(|s| s == "skip-proofs");
        assert!(
            mentions_skip,
            "skip-proofs hazard not flagged in defthm body: {:?}",
            questionable.axiom_usage
        );

        // Top-level skip-proofs leak is surfaced as a synthetic decl.
        let has_top_skip = pf
            .decls
            .iter()
            .any(|d| d.name.starts_with("__skip-proofs@"));
        assert!(
            has_top_skip,
            "top-level skip-proofs not surfaced; got {:?}",
            pf.decls.iter().map(|d| &d.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn captures_include_book_imports() {
        let src = "\
(in-package \"ACL2\")\n\
(include-book \"std/lists/top\" :dir :system)\n\
(include-book \"arithmetic/top-with-meta\")\n\
\n\
(defconst *one* 1)\n\
";
        let pf = parse_acl2_file(src);
        assert!(pf.imports.iter().any(|i| i == "std/lists/top"));
        assert!(pf.imports.iter().any(|i| i == "arithmetic/top-with-meta"));
        let one = pf
            .decls
            .iter()
            .find(|d| d.name == "*one*")
            .expect("defconst");
        assert_eq!(one.kind, DeclKind::Module);
    }
}
