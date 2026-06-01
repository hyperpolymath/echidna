// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! ProofNet adapter for the corpus indexer.
//!
//! ProofNet (Azerbayev et al., 2023, arXiv:2302.12433) pairs natural-
//! language theorem statements with Lean formalisations drawn from
//! undergraduate-textbook problem sets (Rudin, Munkres, Dummit-Foote,
//! …). The released format is JSONL: one object per line, with fields
//! roughly
//!
//! ```jsonc
//! {
//!   "id": "rudin_3_1_3",
//!   "tag": "Rudin|3.1.3",
//!   "src": "Rudin",
//!   "nl_statement":   "Prove that …",
//!   "formal_statement": "theorem rudin_3_1_3 … : … := by",
//!   "nl_proof":       "Suppose for contradiction …",
//!   "formal_proof":   "  exact …",
//!   "header":         "import Mathlib.Analysis…"
//! }
//! ```
//!
//! Field availability is shaky across forks; we treat
//! `formal_statement` (or `statement`) as the only required field and
//! tolerate everything else as `Option`. Each line becomes one
//! `CorpusEntry`; each `.jsonl` file becomes one `ModuleEntry`.
//!
//! Hazards: `sorry`, `admit`, `axiom` in either statement or proof;
//! the meta-tag `no_formal_proof` is recorded in
//! `AxiomUsage::other` when `formal_proof` is missing or empty (these
//! entries are statement-only and unsafe for SA design-search
//! consumers that expect a proven training pair).

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde_json::Value;

use super::{AxiomUsage, Corpus, CorpusEntry, DeclKind, ModuleEntry};

/// Walk `root`, parse every `*.jsonl` file, and produce a corpus.
///
/// Skips directories named `.git`, `target`, `_build`, `models`.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let mut files: Vec<PathBuf> = Vec::new();
    walk_proofnet(root, &mut files)?;
    files.sort();

    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: "proofnet".to_string(),
        ..Default::default()
    };

    for path in &files {
        let rel = path.strip_prefix(root).unwrap_or(path).to_path_buf();
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let module_name = rel
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "proofnet".to_string());

        let module_idx = corpus.modules.len();
        corpus.modules.push(ModuleEntry {
            name: module_name.clone(),
            path: rel,
            options: Vec::new(),
            imports: Vec::new(),
            entries: Vec::new(),
        });

        for (row, line) in raw.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            let value: Value = match serde_json::from_str(trimmed) {
                Ok(v) => v,
                Err(_) => continue, // tolerate truncated lines
            };

            let Some(entry) = build_entry(&value, &module_name, row, module_idx) else {
                continue;
            };
            let entry_idx = corpus.entries.len();
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(entry);
        }
    }

    corpus.reindex();
    Ok(corpus)
}

fn walk_proofnet(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let read = std::fs::read_dir(dir).with_context(|| format!("read_dir {}", dir.display()))?;
    for entry in read {
        let entry = entry?;
        let p = entry.path();
        let name_s = entry.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if matches!(name_s.as_str(), ".git" | "target" | "_build" | "models") {
                continue;
            }
            walk_proofnet(&p, out)?;
        } else if p.extension().and_then(|s| s.to_str()) == Some("jsonl") {
            out.push(p);
        }
    }
    Ok(())
}

fn str_field<'a>(v: &'a Value, key: &str) -> Option<&'a str> {
    v.get(key).and_then(|x| x.as_str()).and_then(|s| {
        let s = s.trim();
        if s.is_empty() {
            None
        } else {
            Some(s)
        }
    })
}

fn build_entry(v: &Value, module_name: &str, row: usize, module_idx: usize) -> Option<CorpusEntry> {
    // Required: a formal statement, under either canonical field name.
    let statement = str_field(v, "formal_statement")
        .or_else(|| str_field(v, "statement"))?
        .to_string();

    // Name: prefer `tag`, then `id`, then a row-stamped fallback.
    let name = str_field(v, "tag")
        .or_else(|| str_field(v, "id"))
        .map(|s| s.to_string())
        .unwrap_or_else(|| format!("proofnet-{}", row));

    // Qualified key: `proofnet.<src>.<name>` if a source textbook is
    // recorded, otherwise `proofnet.<module>.<name>` so two files
    // can't collide.
    let qualified = match str_field(v, "src") {
        Some(src) => format!("proofnet.{}.{}", src, name),
        None => format!("proofnet.{}.{}", module_name, name),
    };

    let proof = str_field(v, "formal_proof").map(|s| s.to_string());

    let mut hz = AxiomUsage::default();
    let scan = match &proof {
        Some(p) => format!("{} {}", statement, p),
        None => statement.clone(),
    };
    flag_hazards(&scan, &mut hz);
    if proof.is_none() {
        hz.other.push("no_formal_proof".to_string());
    }

    Some(CorpusEntry {
        name,
        qualified,
        module_idx,
        kind: DeclKind::Function,
        statement: normalise_ws(&statement),
        proof: proof.as_deref().map(normalise_ws),
        line: row + 1,
        dependencies: Vec::new(),
        axiom_usage: hz,
    })
}

fn normalise_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn flag_hazards(text: &str, hz: &mut AxiomUsage) {
    if text.contains("sorry") {
        hz.sorry = true;
    }
    if text.contains("admit") {
        hz.admitted = true;
    }
    if text.contains("axiom") {
        hz.postulate = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Inline JSONL fixture: two entries, one with a formal_proof,
    // one statement-only. Exercises name/statement extraction +
    // no_formal_proof hazard flagging.
    const FIXTURE: &str = concat!(
        r#"{"tag":"Rudin|3.1.3","src":"Rudin","formal_statement":"theorem rudin_3_1_3 : 1 + 1 = 2 := by","formal_proof":"  rfl"}"#,
        "\n",
        r#"{"id":"munkres_p17","src":"Munkres","formal_statement":"theorem munkres_p17 : True"}"#,
        "\n",
    );

    fn parse_fixture(name: &str) -> Corpus {
        // Use ingest() against a temp dir for a more honest integration
        // shape. Falls back to building the Corpus directly here to
        // keep the test hermetic and not depend on tempfile.
        let mut corpus = Corpus {
            adapter: "proofnet".to_string(),
            ..Default::default()
        };
        let module_idx = corpus.modules.len();
        corpus.modules.push(ModuleEntry {
            name: name.to_string(),
            path: PathBuf::from(format!("{}.jsonl", name)),
            options: Vec::new(),
            imports: Vec::new(),
            entries: Vec::new(),
        });
        for (row, line) in FIXTURE.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            let value: Value = serde_json::from_str(trimmed).unwrap();
            let entry = build_entry(&value, name, row, module_idx).unwrap();
            let idx = corpus.entries.len();
            corpus.modules[module_idx].entries.push(idx);
            corpus.entries.push(entry);
        }
        corpus.reindex();
        corpus
    }

    #[test]
    fn extracts_tag_and_statement() {
        let c = parse_fixture("mini");
        assert_eq!(c.entries.len(), 2);
        assert_eq!(c.entries[0].name, "Rudin|3.1.3");
        assert!(c.entries[0].statement.contains("rudin_3_1_3"));
        assert_eq!(c.entries[0].qualified, "proofnet.Rudin.Rudin|3.1.3");
        assert!(c.entries[0].proof.as_deref().unwrap().contains("rfl"));
    }

    #[test]
    fn flags_missing_formal_proof() {
        let c = parse_fixture("mini");
        let munkres = c.entries.iter().find(|e| e.name == "munkres_p17").unwrap();
        assert!(munkres.proof.is_none());
        assert!(munkres
            .axiom_usage
            .other
            .iter()
            .any(|t| t == "no_formal_proof"));
        // The complete pair must NOT carry that flag.
        let rudin = c.entries.iter().find(|e| e.name == "Rudin|3.1.3").unwrap();
        assert!(!rudin
            .axiom_usage
            .other
            .iter()
            .any(|t| t == "no_formal_proof"));
    }

    #[test]
    fn fallback_name_when_no_id_or_tag() {
        let v: Value =
            serde_json::from_str(r#"{"formal_statement":"theorem t : True := trivial"}"#).unwrap();
        let e = build_entry(&v, "anon", 4, 0).unwrap();
        assert_eq!(e.name, "proofnet-4");
        assert_eq!(e.qualified, "proofnet.anon.proofnet-4");
    }

    #[test]
    fn detects_sorry_in_proof() {
        let v: Value = serde_json::from_str(
            r#"{"tag":"t","src":"S","formal_statement":"theorem t : True := by","formal_proof":"  sorry"}"#,
        )
        .unwrap();
        let e = build_entry(&v, "m", 0, 0).unwrap();
        assert!(e.axiom_usage.sorry);
    }
}
