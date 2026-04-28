// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Lean 4 adapter for the corpus indexer — Step 2 of the N-dim plan.
//!
//! Lean 4 is whitespace-significant: top-level declarations begin at
//! column 0 with a keyword (`def`, `theorem`, `lemma`, `inductive`,
//! `structure`, `axiom`, `class`, `instance`, `namespace`, `import`,
//! `open`). A declaration runs until the next column-0 keyword line
//! or EOF.
//!
//! Comments: `--` line, `/- … -/` block (nestable), `/-- … -/` doc.
//!
//! Hazards: `sorry` (incomplete proof), `axiom` (unproven postulate).
//! `admit` is a tactic alias for `sorry` and is also flagged.

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_lean(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "lean".to_string(),
        ..Default::default()
    };

    let mut all_names: HashSet<String> = HashSet::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;
        let parsed = parse_lean_file(&raw);

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

fn walk_lean(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
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
                "_build" | ".git" | "node_modules" | "target" | ".cache" | "build" | "lake-packages" | ".lake"
            ) {
                continue;
            }
            walk_lean(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("lean") {
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

/// Strip Lean 4 comments. `--` runs to end-of-line; `/- … -/` is
/// nestable; `/-- … -/` is a doc-comment which we treat the same.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut depth: usize = 0;
    while i < bytes.len() {
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'/' {
                depth -= 1;
                out.push(b' ');
                out.push(b' ');
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
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
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
            depth = 1;
            out.push(b' ');
            out.push(b' ');
            i += 2;
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

const TOPLEVEL_KEYWORDS: &[&str] = &[
    "def ",
    "theorem ",
    "lemma ",
    "example ",
    "abbrev ",
    "inductive ",
    "structure ",
    "class ",
    "instance ",
    "axiom ",
    "constant ",
    "namespace ",
    "section ",
    "end ",
    "import ",
    "open ",
    "variable ",
    "universe ",
    "universes ",
    "set_option ",
    "syntax ",
    "elab ",
    "macro ",
    "notation ",
    "infix ",
    "infixl ",
    "infixr ",
    "prefix ",
    "postfix ",
];

fn parse_lean_file(raw: &str) -> ParsedFile {
    let stripped = strip_comments(raw);
    let lines: Vec<&str> = stripped.lines().collect();
    let mut pf = ParsedFile::default();

    // Imports + namespace + options scanned from any line, since
    // they're column-0 statements whose body is one line.
    for line in &lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("import ") {
            let m: String = rest
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_string();
            if !m.is_empty() && !pf.imports.contains(&m) {
                pf.imports.push(m);
            }
            continue;
        }
        if let Some(rest) = t.strip_prefix("namespace ") {
            let n: String = rest
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_string();
            if !n.is_empty() && pf.module_name.is_none() {
                pf.module_name = Some(n);
            }
            continue;
        }
        if let Some(rest) = t.strip_prefix("set_option ") {
            pf.options.push(rest.split_whitespace().take(2).collect::<Vec<_>>().join(" "));
            continue;
        }
    }

    // Walk the file and accumulate top-level decls. We don't gate on
    // column 0 — the comment stripper turns leading `/- … -/` blocks
    // into spaces, which would push otherwise-top-level decls to a
    // non-zero column. Lean's grammar makes `def`/`theorem`/
    // `inductive`/etc. unambiguous: they never appear inside `let`,
    // `match`, `where` clauses, so trim-start matching is safe.
    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        let line_no = i + 1;
        if line.trim().is_empty() {
            i += 1;
            continue;
        }
        // Strip leading `private`, `protected`, `noncomputable`,
        // `partial`, `unsafe`, `@[…]` attribute brackets.
        let mut t = line.trim_start();
        loop {
            let original = t;
            for prefix in &[
                "private ",
                "protected ",
                "noncomputable ",
                "partial ",
                "unsafe ",
                "mutual ",
                "scoped ",
                "local ",
            ] {
                if let Some(rest) = t.strip_prefix(*prefix) {
                    t = rest.trim_start();
                }
            }
            if let Some(after_attr) = strip_attribute(t) {
                t = after_attr.trim_start();
            }
            if t == original {
                break;
            }
        }

        // Match a top-level keyword.
        let kw_match = TOPLEVEL_KEYWORDS
            .iter()
            .find(|kw| t.starts_with(*kw))
            .copied();
        let kw = match kw_match {
            Some(k) => k,
            None => {
                i += 1;
                continue;
            }
        };

        // Skip imports/namespace/end/open/variable/universe/etc.
        // Those are accounted for above or are noise for the index.
        if matches!(
            kw,
            "import "
                | "namespace "
                | "section "
                | "end "
                | "open "
                | "variable "
                | "universe "
                | "universes "
                | "set_option "
                | "syntax "
                | "elab "
                | "macro "
                | "notation "
                | "infix "
                | "infixl "
                | "infixr "
                | "prefix "
                | "postfix "
        ) {
            i += 1;
            continue;
        }

        // Accumulate the decl: this line + any subsequent lines until
        // the next line whose trim_start starts with a top-level
        // keyword (which signals a new decl).
        let mut buf = t.trim_end().to_string();
        let mut j = i + 1;
        while j < lines.len() {
            let nl = lines[j];
            if nl.trim().is_empty() {
                j += 1;
                continue;
            }
            let nt = strip_attributes_and_modifiers(nl.trim_start());
            if TOPLEVEL_KEYWORDS.iter().any(|k| nt.starts_with(*k)) {
                break;
            }
            buf.push(' ');
            buf.push_str(nl.trim());
            j += 1;
        }

        let decl_text = normalise_ws(&buf);

        // Now parse the accumulated decl text.
        let kind = match kw.trim_end() {
            "inductive" | "class" => DeclKind::Data,
            "structure" => DeclKind::Record,
            "axiom" | "constant" => DeclKind::Postulate,
            _ => DeclKind::Function,
        };

        let body = decl_text.strip_prefix(kw).unwrap_or(&decl_text);
        let (name, statement, proof) = if matches!(kind, DeclKind::Function) {
            split_def(body)
        } else {
            split_inductive_or_record(body)
        };

        let mut hz = AxiomUsage::default();
        if matches!(kind, DeclKind::Postulate) {
            hz.postulate = true;
        }
        flag_hazards(&decl_text, &mut hz);

        if !name.is_empty() {
            pf.decls.push(DraftDecl {
                name,
                kind,
                statement,
                proof,
                line: line_no,
                axiom_usage: hz,
            });
        }

        i = j;
    }

    pf
}

fn column_of(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

fn strip_attribute(s: &str) -> Option<&str> {
    if !s.starts_with("@[") {
        return None;
    }
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[i + 1..]);
                }
            }
            _ => {}
        }
    }
    None
}

fn strip_attributes_and_modifiers(mut s: &str) -> &str {
    let modifiers = [
        "private ",
        "protected ",
        "noncomputable ",
        "partial ",
        "unsafe ",
        "mutual ",
        "scoped ",
        "local ",
    ];
    loop {
        let original = s;
        for m in &modifiers {
            if let Some(r) = s.strip_prefix(*m) {
                s = r.trim_start();
            }
        }
        if let Some(after) = strip_attribute(s) {
            s = after.trim_start();
        }
        if s == original {
            return s;
        }
    }
}

/// `name [args] [: ty] := body` or `name [args] : ty` (axiomatic in
/// some contexts).
fn split_def(body: &str) -> (String, String, Option<String>) {
    let body = body.trim();
    let name = body
        .split(|c: char| c.is_whitespace() || c == '(' || c == '[' || c == '{' || c == ':')
        .next()
        .unwrap_or("")
        .to_string();
    if name.is_empty() {
        return (String::new(), String::new(), None);
    }
    let rest = &body[name.len()..];
    if let Some(eq) = find_top_level_assign(rest) {
        let head = &rest[..eq];
        let tail = rest[eq + 2..].trim().to_string();
        let ty = match top_level_colon(head) {
            Some(c) => normalise_ws(head[c + 1..].trim()),
            None => String::new(),
        };
        (name, ty, Some(tail))
    } else {
        let ty = match top_level_colon(rest) {
            Some(c) => normalise_ws(rest[c + 1..].trim()),
            None => normalise_ws(rest),
        };
        (name, ty, None)
    }
}

/// `Foo [params] [: ty] [where | C1 : ty1 …]`
fn split_inductive_or_record(body: &str) -> (String, String, Option<String>) {
    let body = body.trim();
    let name = body
        .split(|c: char| c.is_whitespace() || c == '(' || c == '[' || c == '{' || c == ':')
        .next()
        .unwrap_or("")
        .to_string();
    let rest = &body[name.len()..];
    (name, normalise_ws(rest), None)
}

fn top_level_colon(s: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut idx = 0;
    while idx < chars.len() {
        let (i, c) = chars[idx];
        match c {
            '(' => paren += 1,
            ')' => paren -= 1,
            '[' => bracket += 1,
            ']' => bracket -= 1,
            '{' => brace += 1,
            '}' => brace -= 1,
            ':' if paren == 0 && bracket == 0 && brace == 0 => {
                // Reject `:=` (we want type-colon, not body-assign).
                if idx + 1 < chars.len() && chars[idx + 1].1 == '=' {
                    idx += 2;
                    continue;
                }
                return Some(i);
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn find_top_level_assign(s: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let bytes = s.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        let c = bytes[i];
        match c {
            b'(' => paren += 1,
            b')' => paren -= 1,
            b'[' => bracket += 1,
            b']' => bracket -= 1,
            b'{' => brace += 1,
            b'}' => brace -= 1,
            b':' if paren == 0 && bracket == 0 && brace == 0 && bytes[i + 1] == b'=' => {
                return Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tokenise_idents(s: &str) -> Vec<&str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '=' | ':' | '"'
            )
    })
    .filter(|t| !t.is_empty())
    .collect()
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("sorry") {
        hz.sorry = true;
    }
    if text.contains("admit") {
        hz.admitted = true;
    }
    // `axiom` keyword case is already handled by Postulate kind.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_def_with_body() {
        let src = "def double (n : Nat) : Nat := n + n\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "double");
        assert!(pf.decls[0].statement.contains("Nat"));
        assert!(pf.decls[0].proof.as_deref().unwrap().contains("n + n"));
    }

    #[test]
    fn parses_theorem_with_term_mode() {
        let src = "theorem t : 1 + 1 = 2 := rfl\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "t");
        assert_eq!(pf.decls[0].kind, DeclKind::Function);
        assert_eq!(pf.decls[0].proof.as_deref().unwrap(), "rfl");
    }

    #[test]
    fn parses_inductive() {
        let src = "inductive Foo where\n  | A\n  | B\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "Foo");
        assert_eq!(pf.decls[0].kind, DeclKind::Data);
    }

    #[test]
    fn parses_structure() {
        let src = "structure Pair where\n  fst : Nat\n  snd : Nat\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "Pair");
        assert_eq!(pf.decls[0].kind, DeclKind::Record);
    }

    #[test]
    fn flags_sorry() {
        let src = "theorem t : True := sorry\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert!(pf.decls[0].axiom_usage.sorry);
    }

    #[test]
    fn parses_axiom_as_postulate() {
        let src = "axiom em : forall p, p \\/ ~p\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].kind, DeclKind::Postulate);
        assert!(pf.decls[0].axiom_usage.postulate);
    }

    #[test]
    fn handles_attributes_and_modifiers() {
        let src = "@[simp] private theorem t : True := trivial\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "t");
    }

    #[test]
    fn parses_imports_and_namespace() {
        let src = "import Mathlib.Data.Nat.Basic\nnamespace MyMod\ndef x : Nat := 0\nend MyMod\n";
        let pf = parse_lean_file(src);
        assert!(pf.imports.iter().any(|m| m == "Mathlib.Data.Nat.Basic"));
        assert_eq!(pf.module_name.as_deref(), Some("MyMod"));
        assert!(pf.decls.iter().any(|d| d.name == "x"));
    }

    #[test]
    fn handles_nested_block_comment() {
        let src = "/- outer /- inner -/ still outer -/ def x : Nat := 0\n";
        let pf = parse_lean_file(src);
        assert_eq!(pf.decls.len(), 1);
        assert_eq!(pf.decls[0].name, "x");
    }
}
