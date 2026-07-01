// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Synonym table loader — reads `data/synonyms/<prover>.toml` and indexes
//! it for fast lookup of alternatives given any name in the table.

use std::collections::HashMap;
use std::path::Path;

use anyhow::{Context, Result};
use serde::Deserialize;

use crate::ProverKind;

#[derive(Debug, Clone, Deserialize)]
pub struct SynonymEntry {
    pub canonical: String,
    pub aliases: Vec<String>,
    pub tactic_class: Option<String>,
    pub notes: Option<String>,
    pub since: Option<String>,
    pub until: Option<String>,
    /// Cross-prover semantic class. Two entries (potentially from
    /// different prover synonym tables) sharing the same
    /// `semantic_class` are considered semantically equivalent. The
    /// classes are deliberately coarse (e.g. `"well-foundedness"`,
    /// `"accessibility"`, `"transitivity"`) rather than per-theorem
    /// — fine-grained equivalence belongs in the OpenTheory /
    /// Dedukti exchange layer (`src/rust/exchange/`).
    #[serde(default)]
    pub semantic_class: Option<String>,
}

/// Parsed and indexed synonym table for a single prover.
#[derive(Debug, Clone, Default)]
pub struct SynonymTable {
    pub entries: Vec<SynonymEntry>,
    /// Maps any name (canonical or alias) → indices into `entries`.
    pub by_name: HashMap<String, Vec<usize>>,
}

#[derive(Deserialize)]
struct RawTable {
    #[serde(rename = "synonym")]
    synonyms: Vec<SynonymEntry>,
}

impl SynonymTable {
    /// Load the table for `prover` from `dir/<prover-name>.toml`.
    pub fn load(prover: ProverKind, dir: &Path) -> Result<Self> {
        let filename = prover_table_filename(prover);
        let path = dir.join(&filename);
        if !path.exists() {
            return Ok(Self::default());
        }
        let raw = crate::provers::bounded_read_corpus_file(&path)?;
        let parsed: RawTable =
            toml::from_str(&raw).with_context(|| format!("Failed to parse {}", path.display()))?;
        Ok(Self::from_entries(parsed.synonyms))
    }

    pub fn from_entries(entries: Vec<SynonymEntry>) -> Self {
        let mut by_name: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, entry) in entries.iter().enumerate() {
            by_name.entry(entry.canonical.clone()).or_default().push(i);
            for alias in &entry.aliases {
                by_name.entry(alias.clone()).or_default().push(i);
            }
        }
        SynonymTable { entries, by_name }
    }

    /// All names in the same entry as `name`, excluding `name` itself.
    pub fn alternatives(&self, name: &str) -> Vec<String> {
        let indices = match self.by_name.get(name) {
            Some(v) => v,
            None => return vec![],
        };
        let mut out = Vec::new();
        for &i in indices {
            let entry = &self.entries[i];
            if entry.canonical != name {
                out.push(entry.canonical.clone());
            }
            for alias in &entry.aliases {
                if alias != name {
                    out.push(alias.clone());
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// All entries tagged with the given `semantic_class`. Used for
    /// cross-prover lookups: load tables from multiple provers and
    /// concatenate the results to find every prover's name for a
    /// shared concept.
    pub fn by_semantic_class(&self, class: &str) -> Vec<&SynonymEntry> {
        self.entries
            .iter()
            .filter(|e| e.semantic_class.as_deref() == Some(class))
            .collect()
    }
}

/// Load every prover's synonym table from `dir` and return them
/// keyed by prover. Useful for cross-prover queries:
///
/// ```ignore
/// let tables = load_all(dir)?;
/// for (prover, table) in &tables {
///     for entry in table.by_semantic_class("well-foundedness") {
///         println!("{:?}: {}", prover, entry.canonical);
///     }
/// }
/// ```
pub fn load_all(dir: &Path) -> Result<HashMap<ProverKind, SynonymTable>> {
    let mut out: HashMap<ProverKind, SynonymTable> = HashMap::new();
    // Original five + 2026-06-01 saturation campaign additions (9 more).
    // Underscore-prefix dictionaries (_msc2020, _wordnet_math,
    // _conceptnet_seed) are loaded separately by `load_cross_prover_dicts`.
    for prover in [
        ProverKind::Agda,
        ProverKind::Coq,
        ProverKind::Lean,
        ProverKind::Idris2,
        ProverKind::Isabelle,
        // Saturation campaign 2026-06-01: 9 new per-prover tables.
        ProverKind::Metamath,
        ProverKind::Mizar,
        ProverKind::HOL4,
        ProverKind::HOLLight,
        ProverKind::Dafny,
        ProverKind::Why3,
        ProverKind::FStar,
        ProverKind::ACL2,
    ] {
        let table = SynonymTable::load(prover, dir)?;
        if !table.is_empty() {
            out.insert(prover, table);
        }
    }
    Ok(out)
}

/// Cross-prover taxonomic dictionaries. Loaded from underscore-prefix
/// TOMLs that are NOT per-prover (`_msc2020.toml`, `_wordnet_math.toml`,
/// `_conceptnet_seed.toml`, `_disciplines.toml`). Consumers merge these
/// into per-prover resolution to bridge corpus items across systems by
/// `semantic_class`.
#[derive(Debug, Clone, Default)]
pub struct CrossProverDicts {
    pub msc2020: SynonymTable,
    pub wordnet_math: SynonymTable,
    pub conceptnet_seed: SynonymTable,
    /// Type-discipline vocabulary (42 TypeChecker disciplines). See
    /// `data/synonyms/_disciplines.toml` and
    /// `docs/architecture/TYPE-DISCIPLINE-EMBEDDING.md`. Added 2026-06-01
    /// as part of the saturation campaign discipline-embedding layer.
    pub disciplines: SynonymTable,
}

/// Load every cross-prover dictionary from `dir`. Missing files are
/// silently treated as empty; the campaign target is offline resilience.
pub fn load_cross_prover_dicts(dir: &Path) -> Result<CrossProverDicts> {
    Ok(CrossProverDicts {
        msc2020: load_underscore_dict(dir, "_msc2020.toml")?,
        wordnet_math: load_underscore_dict(dir, "_wordnet_math.toml")?,
        conceptnet_seed: load_underscore_dict(dir, "_conceptnet_seed.toml")?,
        disciplines: load_underscore_dict(dir, "_disciplines.toml")?,
    })
}

fn load_underscore_dict(dir: &Path, filename: &str) -> Result<SynonymTable> {
    let path = dir.join(filename);
    if !path.exists() {
        return Ok(SynonymTable::default());
    }
    let raw = crate::provers::bounded_read_corpus_file(&path)?;
    let parsed: RawTable =
        toml::from_str(&raw).with_context(|| format!("Failed to parse {}", path.display()))?;
    Ok(SynonymTable::from_entries(parsed.synonyms))
}

impl SynonymTable {
    /// Extend this per-prover table with rows from a cross-prover
    /// dictionary (MSC2020 / WordNet / ConceptNet). New entries are
    /// appended; the by_name index is rebuilt. Idempotent if called with
    /// the same `other` twice (duplicates dedup at lookup time via
    /// `alternatives()`).
    pub fn merge_external(&mut self, other: &SynonymTable) {
        let mut entries = std::mem::take(&mut self.entries);
        entries.extend(other.entries.iter().cloned());
        *self = SynonymTable::from_entries(entries);
    }
}

fn prover_table_filename(prover: ProverKind) -> String {
    match prover {
        ProverKind::Isabelle => "isabelle.toml",
        ProverKind::Coq => "coq.toml",
        ProverKind::Lean => "lean4.toml",
        ProverKind::Idris2 => "idris2.toml",
        ProverKind::Agda => "agda.toml",
        // Saturation campaign 2026-06-01 — canonical filenames for the
        // nine new per-prover synonym tables.
        ProverKind::Metamath => "metamath.toml",
        ProverKind::Mizar => "mizar.toml",
        ProverKind::HOL4 => "hol4.toml",
        ProverKind::HOLLight => "hol_light.toml",
        ProverKind::Dafny => "dafny.toml",
        ProverKind::Why3 => "why3.toml",
        ProverKind::FStar => "fstar.toml",
        ProverKind::ACL2 => "acl2.toml",
        _ => return format!("{}.toml", format!("{:?}", prover).to_lowercase()),
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_table() -> SynonymTable {
        SynonymTable::from_entries(vec![
            SynonymEntry {
                canonical: "induction".to_string(),
                aliases: vec!["induct".to_string()],
                tactic_class: Some("induction".to_string()),
                notes: None,
                since: None,
                until: None,
                semantic_class: None,
            },
            SynonymEntry {
                canonical: "linarith".to_string(),
                aliases: vec!["arith".to_string(), "presburger".to_string()],
                tactic_class: Some("arithmetic".to_string()),
                notes: None,
                since: None,
                until: None,
                semantic_class: None,
            },
        ])
    }

    #[test]
    fn test_alternatives_canonical() {
        let t = make_table();
        let alts = t.alternatives("induction");
        assert!(alts.contains(&"induct".to_string()), "expected induct");
        assert!(
            !alts.contains(&"induction".to_string()),
            "should not include self"
        );
    }

    #[test]
    fn test_alternatives_alias() {
        let t = make_table();
        let alts = t.alternatives("induct");
        assert!(
            alts.contains(&"induction".to_string()),
            "expected induction"
        );
    }

    #[test]
    fn test_alternatives_missing() {
        let t = make_table();
        assert!(t.alternatives("unknown_tactic").is_empty());
    }

    #[test]
    fn test_alternatives_multiple_aliases() {
        let t = make_table();
        let alts = t.alternatives("linarith");
        assert!(alts.contains(&"arith".to_string()));
        assert!(alts.contains(&"presburger".to_string()));
        assert!(!alts.contains(&"linarith".to_string()));
    }
}
