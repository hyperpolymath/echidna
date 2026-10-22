// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Synonym table loader — reads `data/synonyms/<prover>.toml` and indexes
//! it for fast lookup of alternatives given any name in the table.

use std::collections::HashMap;
use std::path::Path;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

use crate::exchange::ExchangeFormat;
use crate::verification::FidelityEvidence;
use crate::ProverKind;

/// How a row's `aliases` relate to its `canonical` name (lexicon v2).
///
/// The schema of record is `data/synonyms/schema.ncl`; see
/// `docs/decisions/2026-10-19-lexicon-v2-and-identity-arbitration.adoc`.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Deserialize, Serialize,
)]
#[serde(rename_all = "snake_case")]
pub enum Relation {
    /// Interchangeable names (the v1 meaning).
    #[default]
    Synonym,
    /// Each alias is a special case of `canonical`.
    Specialisation,
    /// Each alias generalises `canonical`.
    Generalisation,
    /// Each alias looks like `canonical` and is not it. Never substituted.
    FalseFriend,
    /// `canonical` is a multi-token idiom spelled out in `phrase`.
    ///
    /// Substitution runs one way today: an alias found at a tactic site
    /// can be replaced by the phrase spelling, but the extractors record
    /// single identifiers, so a canonical phrase in a proof is never a
    /// site and is not replaced by an alias. That direction needs
    /// phrase-aware site detection.
    Phrase,
}

impl Relation {
    /// Whether the variant tester may substitute an alias for the
    /// canonical name (and back). Only synonyms and phrase spellings are
    /// interchangeable; specialisations, generalisations and false friends
    /// are reported by [`SynonymTable::related`] instead.
    pub fn interchangeable(self) -> bool {
        matches!(self, Relation::Synonym | Relation::Phrase)
    }
}

/// The witness behind a lexicon row. Mirrors the ECH-05
/// [`FidelityEvidence`] shapes. It attests the row's relation, whatever
/// that is; only [`SynonymEntry::fidelity_evidence`] lifts it to the arbiter.
#[derive(Debug, Clone, PartialEq, Eq, Default, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum LexiconEvidence {
    /// No evidence (the default, and the only value a corpus-mined
    /// candidate may carry: owner decision D4).
    #[default]
    None,
    /// A person curated the row. Provenance only, not fidelity evidence.
    Curated,
    /// Consequence-tested correspondence.
    Probe { tests: u32, failures: u32 },
    /// Kernel-checked translation through the exchange layer.
    Kernel {
        format: ExchangeFormat,
        checked_by: ProverKind,
        term_hash: String,
    },
}

impl LexiconEvidence {
    /// The shape-for-shape lift, without the row's context. Private: a
    /// probe on a false friend or a lossy row must not reach the arbiter
    /// as identity evidence, so callers go through
    /// [`SynonymEntry::fidelity_evidence`].
    fn lift(&self) -> FidelityEvidence {
        match self {
            LexiconEvidence::None | LexiconEvidence::Curated => FidelityEvidence::None,
            LexiconEvidence::Probe { tests, failures } => {
                FidelityEvidence::DeclaredCorrespondence {
                    consequence_tests: *tests,
                    failures: *failures,
                }
            },
            LexiconEvidence::Kernel {
                format,
                checked_by,
                term_hash,
            } => FidelityEvidence::KernelTranslation {
                format: *format,
                checked_by: *checked_by,
                term_hash: term_hash.clone(),
            },
        }
    }
}

/// A name in another table that looks like this entry and is not it.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FalseFriend {
    pub name: String,
    /// The other table's file stem, e.g. `"lean4"` or `"metamath"`.
    pub table: String,
}

/// Whether a correspondence loses information, after echo-types'
/// loss-with-residue formalism.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Fidelity {
    Exact,
    /// Lossy: the row's `residue` says what is lost.
    Lossy,
}

/// The library (and optionally version) a relation holds in.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Scope {
    pub library: String,
    #[serde(default)]
    pub version: Option<String>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SynonymEntry {
    pub canonical: String,
    pub aliases: Vec<String>,
    #[serde(default)]
    pub tactic_class: Option<String>,
    #[serde(default)]
    pub notes: Option<String>,
    #[serde(default)]
    pub since: Option<String>,
    #[serde(default)]
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
    // ---- lexicon v2 (all optional; v1 rows load unchanged) ----
    /// How `aliases` relate to `canonical`; defaults to `synonym`.
    #[serde(default)]
    pub relation: Relation,
    /// Token spelling of a multi-token idiom (relation `phrase`).
    #[serde(default)]
    pub phrase: Option<Vec<String>>,
    /// Look-alike names in other tables that are not this entry.
    #[serde(default)]
    pub false_friends: Vec<FalseFriend>,
    #[serde(default)]
    pub evidence: LexiconEvidence,
    #[serde(default)]
    pub fidelity: Option<Fidelity>,
    /// What a lossy correspondence loses.
    #[serde(default)]
    pub residue: Option<String>,
    #[serde(default)]
    pub scope: Option<Scope>,
}

impl SynonymEntry {
    /// Whether the row claims identity: its aliases are interchangeable
    /// with `canonical` ([`Relation::interchangeable`]) and nothing is
    /// lost between them (fidelity not [`Fidelity::Lossy`]).
    pub fn claims_identity(&self) -> bool {
        self.relation.interchangeable() && self.fidelity != Some(Fidelity::Lossy)
    }

    /// The arbiter's evidence for this row.
    ///
    /// Only an identity claim ([`Self::claims_identity`]) lifts its
    /// evidence: probe to [`FidelityEvidence::DeclaredCorrespondence`],
    /// kernel to [`FidelityEvidence::KernelTranslation`]. Every other row
    /// gives [`FidelityEvidence::None`], whatever it carries: a probe on a
    /// false friend, a specialisation or a lossy row attests that
    /// relation, not identity, and must not raise an attempt's
    /// fidelity level. `none` and `curated` also give
    /// [`FidelityEvidence::None`]. Field values are carried over without
    /// validation.
    pub fn fidelity_evidence(&self) -> FidelityEvidence {
        if self.claims_identity() {
            self.evidence.lift()
        } else {
            FidelityEvidence::None
        }
    }
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
    ///
    /// Returns an empty table if the path is missing or its existence
    /// cannot be checked.
    ///
    /// # Errors
    ///
    /// If the path exists, propagates the read and parse errors from
    /// [`Self::load_path`].
    pub fn load(prover: ProverKind, dir: &Path) -> Result<Self> {
        let filename = prover_table_filename(prover);
        let path = dir.join(&filename);
        if !path.exists() {
            return Ok(Self::default());
        }
        Self::load_path(&path)
    }

    /// Load one table file, whatever its name (per-prover or an
    /// underscore-prefixed cross-prover dictionary).
    ///
    /// Indexes canonical names and aliases. The Nickel contract's
    /// cross-field rules are not checked here.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be opened or read as UTF-8,
    /// exceeds 64 MiB, cannot be deserialised as a synonym table, or has
    /// a row with an empty canonical name or alias.
    pub fn load_path(path: &Path) -> Result<Self> {
        let raw = crate::provers::bounded_read_corpus_file(path)?;
        let parsed: RawTable =
            toml::from_str(&raw).with_context(|| format!("Failed to parse {}", path.display()))?;
        // An empty name would be offered as a replacement that deletes
        // the matched tactic. The contract refuses it too; this keeps an
        // unchecked table from reaching the variant tester.
        if let Some(entry) = parsed
            .synonyms
            .iter()
            .find(|e| e.canonical.is_empty() || e.aliases.iter().any(String::is_empty))
        {
            anyhow::bail!(
                "{}: row `{}` has an empty canonical name or alias",
                path.display(),
                entry.canonical
            );
        }
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

    /// All names interchangeable with `name`, excluding `name` itself.
    ///
    /// Only rows whose [`Relation`] is interchangeable (synonym, phrase)
    /// contribute: a false friend, specialisation or generalisation is
    /// never offered as a drop-in replacement. Use [`Self::related`]
    /// for those.
    ///
    /// Matches names exactly and returns sorted, deduplicated names.
    /// Returns an empty vector if `name` is unknown.
    pub fn alternatives(&self, name: &str) -> Vec<String> {
        let indices = match self.by_name.get(name) {
            Some(v) => v,
            None => return vec![],
        };
        let mut out = Vec::new();
        for &i in indices {
            let entry = &self.entries[i];
            if !entry.relation.interchangeable() {
                continue;
            }
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

    /// Names related to `name` by a non-interchangeable [`Relation`],
    /// each with the relation read from `name`'s side: if `name` is the
    /// canonical of a `specialisation` row, every alias is a
    /// specialisation of it; if `name` is one of those aliases, the
    /// canonical is its generalisation. False friends are symmetric.
    ///
    /// Matches names exactly and returns sorted, deduplicated pairs.
    /// An alias lookup returns only the canonical name from each row,
    /// not the other aliases. The separate `false_friends` metadata is
    /// not searched. Returns an empty vector if `name` is unknown.
    pub fn related(&self, name: &str) -> Vec<(String, Relation)> {
        let mut out = Vec::new();
        for &i in self.by_name.get(name).map(Vec::as_slice).unwrap_or(&[]) {
            let entry = &self.entries[i];
            if entry.relation.interchangeable() {
                continue;
            }
            if entry.canonical == name {
                for alias in &entry.aliases {
                    out.push((alias.clone(), entry.relation));
                }
            } else {
                let inverse = match entry.relation {
                    Relation::Specialisation => Relation::Generalisation,
                    Relation::Generalisation => Relation::Specialisation,
                    other => other,
                };
                out.push((entry.canonical.clone(), inverse));
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
    // _conceptnet_seed, _disciplines, _verification_systems) are loaded
    // separately by `load_cross_prover_dicts`.
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
/// `_conceptnet_seed.toml`, `_disciplines.toml`,
/// `_verification_systems.toml`). Consumers merge these into per-prover
/// resolution to bridge corpus items across systems by `semantic_class`.
#[derive(Debug, Clone, Default)]
pub struct CrossProverDicts {
    pub msc2020: SynonymTable,
    pub wordnet_math: SynonymTable,
    pub conceptnet_seed: SynonymTable,
    /// Type-discipline vocabulary (42 TypeChecker disciplines). See
    /// `data/synonyms/_disciplines.toml` and
    /// `docs/architecture/TYPE-DISCIPLINE-EMBEDDING.adoc`. Added 2026-06-01
    /// as part of the saturation campaign discipline-embedding layer.
    pub disciplines: SynonymTable,
    /// Program-verification vocabulary: bitvectors, memory layout,
    /// separation and region framing, termination measures, resource
    /// algebras, information flow, and the estate layer boundaries
    /// (Idris2 ABI / Zig API+FFI / SNIF / Rust+Creusot / Julia / Chapel).
    /// See `data/synonyms/_verification_systems.toml`. Added 2026-10-22:
    /// the WordNet / ConceptNet seeds only carry undergraduate and
    /// competition pure mathematics, so the verification surface had no
    /// semantic classes at all.
    pub verification_systems: SynonymTable,
}

/// Load every cross-prover dictionary from `dir`. Missing files are
/// silently treated as empty; the campaign target is offline resilience.
pub fn load_cross_prover_dicts(dir: &Path) -> Result<CrossProverDicts> {
    Ok(CrossProverDicts {
        msc2020: load_underscore_dict(dir, "_msc2020.toml")?,
        wordnet_math: load_underscore_dict(dir, "_wordnet_math.toml")?,
        conceptnet_seed: load_underscore_dict(dir, "_conceptnet_seed.toml")?,
        disciplines: load_underscore_dict(dir, "_disciplines.toml")?,
        verification_systems: load_underscore_dict(dir, "_verification_systems.toml")?,
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
                ..Default::default()
            },
            SynonymEntry {
                canonical: "linarith".to_string(),
                aliases: vec!["arith".to_string(), "presburger".to_string()],
                tactic_class: Some("arithmetic".to_string()),
                notes: None,
                since: None,
                until: None,
                semantic_class: None,
                ..Default::default()
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
