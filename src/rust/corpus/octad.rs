// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! 8-modality octad emission for the corpus — Step 3 of the N-dim
//! VeriSim plan.
//!
//! Mirrors the octad shape of `verisim_bridge::OctadPayload` (which
//! is feature-gated and proof-attempt-shaped) but with corpus-
//! declaration-tailored fields. Each `CorpusEntry` becomes one
//! `DeclarationOctad`. Persist as newline-delimited JSON
//! (`*.octads.jsonl`); each line is a self-contained octad, so the
//! file is streamable and any VeriSim consumer can ingest line-by-line
//! via the existing `/api/v1/octads` endpoint.
//!
//! Six of the eight modalities populate immediately from the corpus:
//!
//! - **Semantic**: kind, statement, full proof body if present
//! - **Document**: searchable text built from name + statement +
//!   proof + axiom-usage flags
//! - **Graph**: forward `dependencies` + reverse `dependents` (Step 1
//!   payoff — both directions encoded), plus a cross-prover semantic
//!   key from `(adapter, qualified-name-tail)` for follow-up joins
//! - **Provenance**: SHA-256 hash chain over (adapter, module-path,
//!   line, ingest-timestamp) — replayable from the source files
//! - **Spatial**: module-tree coord (file path + line) + adapter
//!   namespace
//! - **Temporal**: a single Created version per entry for now;
//!   subsequent ingest rungs append additional versions
//!
//! Tensor and Vector remain reserved (Steps 4, 5).

#![allow(dead_code)]

use std::path::Path;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{Corpus, CorpusEntry, DeclKind, ModuleEntry};

// ===========================================================================
// 8-modality declaration octad
// ===========================================================================

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclarationOctad {
    /// Octad key — SHA-256 over (adapter, qualified, statement).
    pub key: String,

    pub semantic: DeclSemantic,
    pub temporal: DeclTemporal,
    pub provenance: DeclProvenance,
    pub document: DeclDocument,
    pub graph: DeclGraph,
    pub vector: DeclVector,
    pub tensor: DeclTensor,
    pub spatial: DeclSpatial,
}

/// Semantic modality — what the declaration *is*.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclSemantic {
    pub adapter: String,
    pub kind: DeclKind,
    pub name: String,
    pub qualified: String,
    pub statement: String,
    pub proof: Option<String>,
}

/// Temporal modality — version chain across rungs. We start with a
/// single Created version; future ingest rungs append new versions
/// with their content hash, enabling "what did `wf-<` look like at
/// commit X" queries.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclTemporal {
    pub versions: Vec<DeclVersion>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclVersion {
    pub version: u64,
    pub timestamp: String,
    pub content_hash: String,
    pub event: String,
}

/// Provenance modality — replayable hash chain over how the entry
/// was produced.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclProvenance {
    pub records: Vec<DeclProvenanceRecord>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclProvenanceRecord {
    pub hash: String,
    pub parent_hash: String,
    pub event: String,
    pub actor: String,
    pub timestamp: String,
    pub source_file: String,
    pub source_line: usize,
}

/// Document modality — searchable text.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclDocument {
    pub theorem_statement: String,
    pub proof_text: String,
    pub aspects: Vec<String>,
    pub searchable_text: String,
}

/// Graph modality — both forward and reverse edges in one place.
/// Cross-prover identity is the SHA-256 of just the adapter-stripped
/// qualified name; two entries from different adapters with the same
/// qualified name (e.g. `Brouwer.WellFounded` in Agda and Coq) match
/// on this hash.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclGraph {
    pub depends_on: Vec<String>,
    pub depended_on_by: Vec<String>,
    pub cross_prover_id: String,
    pub adapter_id: String,
}

/// Vector modality — reserved for Step 5 embeddings.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DeclVector {
    pub goal_embedding: Vec<f32>,
    pub model: String,
    pub dimensions: usize,
}

/// Tensor modality — currently carries axiom-hazard flags as floats
/// plus declaration-shape signals; Step 4 will expand this into a
/// proper metrics tensor.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DeclTensor {
    pub metrics: std::collections::HashMap<String, f64>,
}

/// Spatial modality — file/line + adapter namespace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclSpatial {
    pub adapter: String,
    pub module_path: String,
    pub source_line: usize,
}

// ===========================================================================
// Corpus → octad mapping
// ===========================================================================

impl DeclarationOctad {
    /// Build one octad from a `CorpusEntry` + its module + reverse-
    /// dep list (the caller is responsible for looking up the
    /// reverse-dep list from the corpus index).
    pub fn from_entry(
        entry: &CorpusEntry,
        module: &ModuleEntry,
        adapter: &str,
        reverse_deps: &[String],
        timestamp: &str,
    ) -> Self {
        let key = octad_key(adapter, &entry.qualified, &entry.statement);
        let cross_prover_id = cross_prover_key(&entry.qualified);
        let content_hash = content_hash_of(entry);

        let semantic = DeclSemantic {
            adapter: adapter.to_string(),
            kind: entry.kind,
            name: entry.name.clone(),
            qualified: entry.qualified.clone(),
            statement: entry.statement.clone(),
            proof: entry.proof.clone(),
        };

        let temporal = DeclTemporal {
            versions: vec![DeclVersion {
                version: 0,
                timestamp: timestamp.to_string(),
                content_hash: content_hash.clone(),
                event: "Created".into(),
            }],
        };

        let provenance_record = DeclProvenanceRecord {
            hash: hash_provenance(
                "",
                "Created",
                timestamp,
                &module.path.display().to_string(),
                entry.line,
            ),
            parent_hash: String::new(),
            event: "Created".into(),
            actor: format!("echidna corpus {}", adapter),
            timestamp: timestamp.to_string(),
            source_file: module.path.display().to_string(),
            source_line: entry.line,
        };
        let provenance = DeclProvenance {
            records: vec![provenance_record],
        };

        let proof_text = entry.proof.clone().unwrap_or_default();
        let aspects = aspects_for(&entry.kind, &entry.axiom_usage);
        let searchable_text = format!(
            "{} {} {} {}",
            entry.qualified, entry.statement, proof_text, aspects.join(" ")
        );
        let document = DeclDocument {
            theorem_statement: entry.statement.clone(),
            proof_text,
            aspects,
            searchable_text,
        };

        let graph = DeclGraph {
            depends_on: entry.dependencies.clone(),
            depended_on_by: reverse_deps.to_vec(),
            cross_prover_id,
            adapter_id: format!("echidna:adapter:{}", adapter),
        };

        let vector = DeclVector::default();

        let mut metrics = std::collections::HashMap::<String, f64>::new();
        metrics.insert("source_line".into(), entry.line as f64);
        metrics.insert(
            "dep_fanout".into(),
            entry.dependencies.len() as f64,
        );
        metrics.insert("dep_fanin".into(), reverse_deps.len() as f64);
        metrics.insert(
            "axiom_hazard_postulate".into(),
            if entry.axiom_usage.postulate { 1.0 } else { 0.0 },
        );
        metrics.insert(
            "axiom_hazard_admitted".into(),
            if entry.axiom_usage.admitted { 1.0 } else { 0.0 },
        );
        metrics.insert(
            "axiom_hazard_sorry".into(),
            if entry.axiom_usage.sorry { 1.0 } else { 0.0 },
        );
        metrics.insert(
            "axiom_hazard_believe_me".into(),
            if entry.axiom_usage.believe_me { 1.0 } else { 0.0 },
        );
        let tensor = DeclTensor { metrics };

        let spatial = DeclSpatial {
            adapter: adapter.to_string(),
            module_path: module.path.display().to_string(),
            source_line: entry.line,
        };

        DeclarationOctad {
            key,
            semantic,
            temporal,
            provenance,
            document,
            graph,
            vector,
            tensor,
            spatial,
        }
    }

    /// Best-effort reconstruction of a `CorpusEntry` (without
    /// `module_idx` or dependency-DAG indices, which are owned by
    /// the `Corpus` container). Caller is responsible for placing
    /// the entry into the right module and calling `Corpus::reindex`.
    pub fn to_entry(&self) -> CorpusEntry {
        CorpusEntry {
            name: self.semantic.name.clone(),
            qualified: self.semantic.qualified.clone(),
            module_idx: 0,
            kind: self.semantic.kind,
            statement: self.semantic.statement.clone(),
            proof: self.semantic.proof.clone(),
            line: self.spatial.source_line,
            dependencies: self.graph.depends_on.clone(),
            axiom_usage: axiom_usage_from_tensor(&self.tensor),
        }
    }
}

fn aspects_for(kind: &DeclKind, hz: &super::AxiomUsage) -> Vec<String> {
    let mut out: Vec<String> = match kind {
        DeclKind::Function => vec!["function".into()],
        DeclKind::Data => vec!["data".into()],
        DeclKind::Record => vec!["record".into()],
        DeclKind::Postulate => vec!["postulate".into(), "axiom".into()],
        DeclKind::Module => vec!["module".into()],
    };
    if hz.postulate {
        out.push("hazard:postulate".into());
    }
    if hz.believe_me {
        out.push("hazard:believe_me".into());
    }
    if hz.admitted {
        out.push("hazard:admitted".into());
    }
    if hz.sorry {
        out.push("hazard:sorry".into());
    }
    if hz.assert_total {
        out.push("hazard:assert_total".into());
    }
    if hz.trustme {
        out.push("hazard:trustme".into());
    }
    out
}

fn axiom_usage_from_tensor(t: &DeclTensor) -> super::AxiomUsage {
    super::AxiomUsage {
        postulate: t.metrics.get("axiom_hazard_postulate").copied().unwrap_or(0.0) > 0.5,
        believe_me: t.metrics.get("axiom_hazard_believe_me").copied().unwrap_or(0.0) > 0.5,
        admitted: t.metrics.get("axiom_hazard_admitted").copied().unwrap_or(0.0) > 0.5,
        sorry: t.metrics.get("axiom_hazard_sorry").copied().unwrap_or(0.0) > 0.5,
        assert_total: false,
        trustme: false,
        other: vec![],
    }
}

fn octad_key(adapter: &str, qualified: &str, statement: &str) -> String {
    let mut h = Sha256::new();
    h.update(adapter.as_bytes());
    h.update(b"|");
    h.update(qualified.as_bytes());
    h.update(b"|");
    h.update(statement.as_bytes());
    format!("{:x}", h.finalize())
}

fn cross_prover_key(qualified: &str) -> String {
    // Strip the leading module prefix to get the local name; this
    // gives a cross-prover-stable identity for theorems with
    // matching local names.
    let tail = qualified.rsplit('.').next().unwrap_or(qualified);
    let mut h = Sha256::new();
    h.update(tail.as_bytes());
    format!("{:x}", h.finalize())
}

fn content_hash_of(entry: &CorpusEntry) -> String {
    let mut h = Sha256::new();
    h.update(entry.qualified.as_bytes());
    h.update(b"|");
    h.update(entry.statement.as_bytes());
    h.update(b"|");
    if let Some(p) = &entry.proof {
        h.update(p.as_bytes());
    }
    format!("{:x}", h.finalize())
}

fn hash_provenance(
    parent: &str,
    event: &str,
    timestamp: &str,
    file: &str,
    line: usize,
) -> String {
    let mut h = Sha256::new();
    h.update(parent.as_bytes());
    h.update(b"|");
    h.update(event.as_bytes());
    h.update(b"|");
    h.update(timestamp.as_bytes());
    h.update(b"|");
    h.update(file.as_bytes());
    h.update(b"|");
    h.update(line.to_string().as_bytes());
    format!("{:x}", h.finalize())
}

// ===========================================================================
// Whole-corpus emit / load (JSONL)
// ===========================================================================

impl Corpus {
    /// Emit each entry as one octad and write to `path` as JSONL
    /// (one JSON object per line). The file is streamable; consumers
    /// can ingest line-by-line. Compatible with VeriSim's
    /// `/api/v1/octads` endpoint when posted one body at a time.
    ///
    /// `timestamp` is a free-form string carried in the temporal +
    /// provenance modalities (typically RFC 3339). Pass `""` to use
    /// "1970-01-01T00:00:00Z" — useful for deterministic test output.
    pub fn save_octads_jsonl(&self, path: &Path, timestamp: &str) -> Result<()> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("create_dir_all {}", parent.display()))?;
        }
        let ts = if timestamp.is_empty() {
            "1970-01-01T00:00:00Z"
        } else {
            timestamp
        };
        // Compute the rich metrics tensor + embeddings once for the
        // whole corpus (Steps 4, 5). Tensor → tensor.metrics; vectors
        // → vector.goal_embedding.
        let metrics_per_entry = self.compute_metrics();
        let embedder = super::embed::HashEmbedder;
        let info = <super::embed::HashEmbedder as super::embed::Embedder>::info(&embedder);
        let embeddings = self.compute_embeddings();
        let mut out = String::new();
        for (i, entry) in self.entries.iter().enumerate() {
            let module = &self.modules[entry.module_idx];
            let rev: Vec<String> = self
                .dependents
                .get(&entry.name)
                .map(|v| v.iter().map(|i| self.entries[*i].qualified.clone()).collect())
                .unwrap_or_default();
            let mut octad =
                DeclarationOctad::from_entry(entry, module, &self.adapter, &rev, ts);
            octad.tensor.metrics = metrics_per_entry[i].as_metric_map();
            octad.vector.goal_embedding = embeddings[i].clone();
            octad.vector.model = info.model.clone();
            octad.vector.dimensions = info.dimensions;
            let line = serde_json::to_string(&octad).context("serialise octad")?;
            out.push_str(&line);
            out.push('\n');
        }
        std::fs::write(path, out)
            .with_context(|| format!("write {}", path.display()))?;
        Ok(())
    }

    /// Load a JSONL octad stream into a fresh corpus. The
    /// reconstruction is best-effort — modules are inferred from
    /// the spatial.module_path of each entry, and entries are
    /// grouped accordingly. `dependents` is rebuilt by `reindex`.
    pub fn load_octads_jsonl(path: &Path) -> Result<Self> {
        use std::collections::HashMap as Map;

        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("read {}", path.display()))?;

        let mut corpus = Corpus::default();
        let mut adapter_set: Option<String> = None;
        let mut module_idx_by_path: Map<String, usize> = Map::new();

        for (i, line) in raw.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let octad: DeclarationOctad = serde_json::from_str(line)
                .with_context(|| format!("parse octad on line {} of {}", i + 1, path.display()))?;
            if adapter_set.is_none() {
                adapter_set = Some(octad.semantic.adapter.clone());
            }
            let module_path = octad.spatial.module_path.clone();
            let module_idx = match module_idx_by_path.get(&module_path) {
                Some(&idx) => idx,
                None => {
                    let idx = corpus.modules.len();
                    let module_name = module_name_from_qualified(&octad.semantic.qualified);
                    corpus.modules.push(ModuleEntry {
                        name: module_name,
                        path: module_path.clone().into(),
                        options: vec![],
                        imports: vec![],
                        entries: vec![],
                    });
                    module_idx_by_path.insert(module_path, idx);
                    idx
                }
            };
            let entry_idx = corpus.entries.len();
            let mut entry = octad.to_entry();
            entry.module_idx = module_idx;
            corpus.modules[module_idx].entries.push(entry_idx);
            corpus.entries.push(entry);
        }

        if let Some(a) = adapter_set {
            corpus.adapter = a;
        }
        corpus.reindex();
        Ok(corpus)
    }
}

fn module_name_from_qualified(qualified: &str) -> String {
    match qualified.rfind('.') {
        Some(i) => qualified[..i].to_string(),
        None => qualified.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::AxiomUsage;
    use std::path::PathBuf;

    fn sample_corpus() -> Corpus {
        let mut c = Corpus {
            adapter: "agda".into(),
            ..Default::default()
        };
        c.modules.push(ModuleEntry {
            name: "Ordinal.Brouwer".into(),
            path: PathBuf::from("Ordinal/Brouwer.agda"),
            options: vec!["--safe".into(), "--without-K".into()],
            imports: vec!["Data.Nat.Base".into()],
            entries: vec![0, 1],
        });
        c.entries.push(CorpusEntry {
            name: "_<_".into(),
            qualified: "Ordinal.Brouwer._<_".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "Ord -> Ord -> Set".into(),
            proof: None,
            line: 56,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "wf-<".into(),
            qualified: "Ordinal.Brouwer.wf-<".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "WellFounded _<_".into(),
            proof: Some("acc lambda".into()),
            line: 130,
            dependencies: vec!["_<_".into()],
            axiom_usage: AxiomUsage::default(),
        });
        c.reindex();
        c
    }

    #[test]
    fn from_entry_populates_six_modalities() {
        let c = sample_corpus();
        let entry = &c.entries[1]; // wf-<
        let module = &c.modules[entry.module_idx];
        let rev: Vec<String> = c
            .dependents
            .get(&entry.name)
            .map(|v| v.iter().map(|i| c.entries[*i].qualified.clone()).collect())
            .unwrap_or_default();
        let octad = DeclarationOctad::from_entry(
            entry,
            module,
            &c.adapter,
            &rev,
            "2026-04-28T00:00:00Z",
        );
        assert_eq!(octad.semantic.adapter, "agda");
        assert_eq!(octad.semantic.qualified, "Ordinal.Brouwer.wf-<");
        assert_eq!(octad.semantic.statement, "WellFounded _<_");
        assert_eq!(octad.temporal.versions.len(), 1);
        assert_eq!(octad.provenance.records.len(), 1);
        assert!(octad.document.searchable_text.contains("WellFounded"));
        assert_eq!(octad.graph.depends_on, vec!["_<_"]);
        // No reverse-deps for wf-< (it's a leaf in this sample).
        assert!(octad.graph.depended_on_by.is_empty());
        assert_eq!(octad.spatial.module_path, "Ordinal/Brouwer.agda");
        assert_eq!(octad.spatial.source_line, 130);
        // Tensor metrics include hazard flags + fan-in/out.
        assert_eq!(*octad.tensor.metrics.get("dep_fanout").unwrap(), 1.0);
        assert_eq!(*octad.tensor.metrics.get("dep_fanin").unwrap(), 0.0);
    }

    #[test]
    fn cross_prover_key_matches_on_local_name() {
        let agda_octad = DeclarationOctad::from_entry(
            &CorpusEntry {
                name: "WellFounded".into(),
                qualified: "Foo.WellFounded".into(),
                module_idx: 0,
                kind: DeclKind::Function,
                statement: "...".into(),
                proof: None,
                line: 1,
                dependencies: vec![],
                axiom_usage: AxiomUsage::default(),
            },
            &ModuleEntry {
                name: "Foo".into(),
                path: PathBuf::from("Foo.agda"),
                options: vec![],
                imports: vec![],
                entries: vec![],
            },
            "agda",
            &[],
            "T",
        );
        let coq_octad = DeclarationOctad::from_entry(
            &CorpusEntry {
                name: "WellFounded".into(),
                qualified: "Bar.WellFounded".into(),
                module_idx: 0,
                kind: DeclKind::Function,
                statement: "...".into(),
                proof: None,
                line: 1,
                dependencies: vec![],
                axiom_usage: AxiomUsage::default(),
            },
            &ModuleEntry {
                name: "Bar".into(),
                path: PathBuf::from("Bar.v"),
                options: vec![],
                imports: vec![],
                entries: vec![],
            },
            "coq",
            &[],
            "T",
        );
        assert_eq!(agda_octad.graph.cross_prover_id, coq_octad.graph.cross_prover_id);
    }

    #[test]
    fn round_trip_jsonl() {
        let tmp = tempfile::NamedTempFile::new().expect("tmpfile");
        let original = sample_corpus();
        original
            .save_octads_jsonl(tmp.path(), "2026-04-28T00:00:00Z")
            .expect("save");
        let loaded = Corpus::load_octads_jsonl(tmp.path()).expect("load");
        assert_eq!(loaded.adapter, original.adapter);
        assert_eq!(loaded.entries.len(), original.entries.len());
        for (orig, got) in original.entries.iter().zip(loaded.entries.iter()) {
            assert_eq!(orig.name, got.name);
            assert_eq!(orig.qualified, got.qualified);
            assert_eq!(orig.statement, got.statement);
            assert_eq!(orig.proof, got.proof);
            assert_eq!(orig.dependencies, got.dependencies);
            assert_eq!(orig.line, got.line);
            assert_eq!(orig.kind, got.kind);
        }
        // Dependents rebuilt on load.
        let dep_names: Vec<&str> = loaded
            .dependents
            .get("_<_")
            .unwrap()
            .iter()
            .map(|&i| loaded.entries[i].name.as_str())
            .collect();
        assert_eq!(dep_names, vec!["wf-<"]);
    }
}
