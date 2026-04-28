// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Project-corpus indexer.
//!
//! Scans a tree of proof files, extracts named declarations + a
//! lightweight dependency graph, and exposes the result for downstream
//! agent strategies (suggest, SA design search, swarm dispatcher).
//!
//! This is *not* a full Agda parser. It is a structural index — module
//! names, top-level declarations, options pragmas, imports, axiom-usage
//! flags, and a name-reference DAG over top-level identifiers within
//! the same project. It exists because the existing
//! `provers/agda.rs` parser is goal-state oriented (it parses for
//! proof-state translation, not corpus-wide dependency analysis), and
//! the `learning/` curriculum scaffolding has no concrete corpus
//! adapter wired to a real proof tree.
//!
//! First adapter: `agda` (echo-types' Buchholz / Brouwer / WF
//! programme). Future adapters: `coq`, `lean4`, `idris2`.
//!
//! ## Design
//!
//! - Two-pass extraction. Pass 1 enumerates module names and decl
//!   names; pass 2 walks each decl's text and records references to
//!   any name in pass-1's known set.
//! - Heuristic, not authoritative. Decl boundaries are detected by
//!   column-0 identifiers followed by `:`; comments (`--`, `{- … -}`)
//!   are stripped before reference scanning.
//! - JSON-serialisable. The `Corpus` value can be persisted to
//!   `data/corpus/<project>.json` and reloaded; downstream consumers
//!   read it without touching the source tree again.

#![allow(dead_code)]

pub mod agda;

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

/// What kind of top-level declaration an entry represents.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeclKind {
    /// Has a type signature and a defining equation. Most lemmas /
    /// theorems / functions land here. We don't try to distinguish
    /// theorems from non-proof functions structurally — the consumer
    /// uses the type signature for that judgement.
    Function,
    /// `data Foo : … where` block.
    Data,
    /// `record Foo : … where` block.
    Record,
    /// `postulate name : ty` (Agda) — banned-but-detected.
    Postulate,
    /// Module declaration. The corpus carries one of these per file
    /// purely so module-level options and imports have a home.
    Module,
}

/// Hazard tags computed during extraction. Any axiom-class pattern
/// detected in a decl gets recorded here so downstream consumers can
/// filter (e.g. SA design-search rejects any candidate whose proof
/// hits `believe_me` or `postulate`).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AxiomUsage {
    pub postulate: bool,
    pub believe_me: bool,
    pub assert_total: bool,
    pub admitted: bool,
    pub sorry: bool,
    pub trustme: bool,
    /// Free-form extras (e.g. `Parameter` outside Section Carrier).
    pub other: Vec<String>,
}

impl AxiomUsage {
    pub fn any(&self) -> bool {
        self.postulate
            || self.believe_me
            || self.assert_total
            || self.admitted
            || self.sorry
            || self.trustme
            || !self.other.is_empty()
    }
}

/// A module-level entry. One per source file (typically).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleEntry {
    /// Dotted name (e.g. `Ordinal.Buchholz.RecursiveSurfaceBudget`).
    pub name: String,
    /// File path relative to the corpus root.
    pub path: PathBuf,
    /// Pragma tokens from the file's leading `{-# OPTIONS … #-}`.
    pub options: Vec<String>,
    /// Imported module names (`open import …` or `import …`).
    pub imports: Vec<String>,
    /// Indices into `Corpus.entries` for declarations in this module.
    pub entries: Vec<usize>,
}

/// A single top-level declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorpusEntry {
    /// Local name (e.g. `wf-<`, `osuc-mono-≤`).
    pub name: String,
    /// Module-qualified name (e.g. `Ordinal.Brouwer.wf-<`).
    pub qualified: String,
    /// Index into `Corpus.modules`.
    pub module_idx: usize,
    pub kind: DeclKind,
    /// Raw type signature, with whitespace normalised to single spaces.
    pub statement: String,
    /// Raw proof body (defining equations), if present. None for
    /// postulates and data declarations.
    pub proof: Option<String>,
    /// 1-based line number in the source file.
    pub line: usize,
    /// Names of other corpus entries this decl references textually.
    /// Computed in pass 2 against the full set of known names.
    pub dependencies: Vec<String>,
    /// Hazard summary.
    pub axiom_usage: AxiomUsage,
}

/// The whole corpus.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Corpus {
    /// Project root absolute path (informational; consumers may
    /// re-root by replacing this).
    pub root: PathBuf,
    /// Adapter name (`"agda"`, `"coq"`, `…`).
    pub adapter: String,
    pub modules: Vec<ModuleEntry>,
    pub entries: Vec<CorpusEntry>,
    /// `entries` index by `name`. Many-to-one because a project may
    /// reuse a name across modules; the value is the list of indices
    /// in declaration order.
    pub by_name: HashMap<String, Vec<usize>>,
    /// `entries` index by `qualified`. One-to-one within a project.
    pub by_qualified: HashMap<String, usize>,
}

impl Corpus {
    /// Look up entries by short or qualified name.
    pub fn find(&self, query: &str) -> Vec<&CorpusEntry> {
        if let Some(idx) = self.by_qualified.get(query) {
            return vec![&self.entries[*idx]];
        }
        if let Some(indices) = self.by_name.get(query) {
            return indices.iter().map(|i| &self.entries[*i]).collect();
        }
        // Fallback: substring match (case-insensitive on the local
        // part). Useful for `corpus query wf` or `corpus query mono`.
        let q = query.to_lowercase();
        self.entries
            .iter()
            .filter(|e| {
                e.name.to_lowercase().contains(&q)
                    || e.qualified.to_lowercase().contains(&q)
            })
            .collect()
    }

    /// All entries that the given entry transitively depends on,
    /// computed by walking `dependencies` over `by_name`.
    pub fn closure(&self, qualified: &str) -> Vec<&CorpusEntry> {
        use std::collections::HashSet;
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack: Vec<usize> = Vec::new();
        if let Some(&start) = self.by_qualified.get(qualified) {
            stack.push(start);
        } else {
            return vec![];
        }
        while let Some(i) = stack.pop() {
            if !seen.insert(i) {
                continue;
            }
            for dep in &self.entries[i].dependencies {
                if let Some(indices) = self.by_name.get(dep) {
                    for &j in indices {
                        if !seen.contains(&j) {
                            stack.push(j);
                        }
                    }
                }
            }
        }
        seen.iter().map(|&i| &self.entries[i]).collect()
    }

    /// Persist as JSON.
    pub fn save_json(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("create_dir_all {}", parent.display()))?;
        }
        let s = serde_json::to_string_pretty(self)
            .context("serialise corpus")?;
        std::fs::write(path, s)
            .with_context(|| format!("write {}", path.display()))?;
        Ok(())
    }

    /// Load from JSON.
    pub fn load_json(path: &Path) -> Result<Self> {
        let s = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;
        let c: Corpus = serde_json::from_str(&s)
            .with_context(|| format!("parse {}", path.display()))?;
        Ok(c)
    }

    /// Re-build the by_name / by_qualified indices after mutation.
    pub fn reindex(&mut self) {
        self.by_name.clear();
        self.by_qualified.clear();
        for (i, e) in self.entries.iter().enumerate() {
            self.by_name.entry(e.name.clone()).or_default().push(i);
            self.by_qualified.insert(e.qualified.clone(), i);
        }
    }

    /// Summary counts.
    pub fn stats(&self) -> CorpusStats {
        let mut stats = CorpusStats::default();
        stats.modules = self.modules.len();
        stats.entries = self.entries.len();
        for e in &self.entries {
            match e.kind {
                DeclKind::Function => stats.functions += 1,
                DeclKind::Data => stats.data += 1,
                DeclKind::Record => stats.records += 1,
                DeclKind::Postulate => stats.postulates += 1,
                DeclKind::Module => {}
            }
            if e.axiom_usage.any() {
                stats.with_hazards += 1;
            }
            if !e.dependencies.is_empty() {
                stats.with_deps += 1;
            }
        }
        stats
    }
}

/// Aggregate counts over a corpus.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CorpusStats {
    pub modules: usize,
    pub entries: usize,
    pub functions: usize,
    pub data: usize,
    pub records: usize,
    pub postulates: usize,
    pub with_hazards: usize,
    pub with_deps: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn corpus_find_short_name() {
        let mut c = Corpus::default();
        c.entries.push(CorpusEntry {
            name: "wf-<".into(),
            qualified: "Ordinal.Brouwer.wf-<".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "WellFounded _<_".into(),
            proof: None,
            line: 130,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.modules.push(ModuleEntry {
            name: "Ordinal.Brouwer".into(),
            path: PathBuf::from("Ordinal/Brouwer.agda"),
            options: vec!["--safe".into(), "--without-K".into()],
            imports: vec![],
            entries: vec![0],
        });
        c.reindex();
        let hits = c.find("wf-<");
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].qualified, "Ordinal.Brouwer.wf-<");
    }

    #[test]
    fn corpus_find_substring_fallback() {
        let mut c = Corpus::default();
        c.entries.push(CorpusEntry {
            name: "osuc-mono-≤".into(),
            qualified: "Ordinal.Brouwer.osuc-mono-≤".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "x ≤ y → osuc x ≤ osuc y".into(),
            proof: None,
            line: 50,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.modules.push(ModuleEntry {
            name: "Ordinal.Brouwer".into(),
            path: PathBuf::from("Ordinal/Brouwer.agda"),
            options: vec![],
            imports: vec![],
            entries: vec![0],
        });
        c.reindex();
        let hits = c.find("mono");
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].name, "osuc-mono-≤");
    }
}
