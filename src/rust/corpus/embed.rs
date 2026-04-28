// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Vector-octad embeddings for the corpus — Step 5 of the N-dim
//! VeriSim plan.
//!
//! Two backends:
//!
//! 1. **Hashing-trick** (default, offline): tokenise statement +
//!    proof on whitespace + Agda-syntax separators, hash each token
//!    into one of 32 buckets, accumulate L2-normalised counts. Free,
//!    deterministic, no network. Good enough for cosine-similarity
//!    nearest-neighbour queries over shared vocabulary, which is
//!    exactly what the SA / MCTS prior layer needs.
//!
//! 2. **GNN client** (future, online): for when the Julia server at
//!    `/gnn/embed` is primed against real proof corpora (Wave-3 ML
//!    work tracked in `docs/handover/TODO.md`). The trait `Embedder`
//!    abstracts the choice; replacing the default `HashEmbedder`
//!    with a `GnnEmbedder` is one-line.
//!
//! The corpus's `compute_embeddings` returns `Vec<Vec<f32>>` parallel
//! to `entries`; `octad.rs::save_octads_jsonl` populates each Vector
//! modality from this. Cosine-similarity helper lives here too.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

use super::{Corpus, CorpusEntry};

/// Embedding dimension used by the default hashing-trick embedder.
/// Chosen to match the 32-dim GNN local-term embeddings already
/// shipped in `src/rust/gnn/embeddings.rs` (`FEATURE_DIM = 32`), so
/// stored octads can be later re-embedded from the GNN client without
/// changing dimensions.
pub const HASH_EMBED_DIM: usize = 32;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbedderInfo {
    pub model: String,
    pub dimensions: usize,
}

pub trait Embedder {
    fn info(&self) -> EmbedderInfo;
    fn embed(&self, entry: &CorpusEntry) -> Vec<f32>;
}

/// Default offline embedder: hashing-trick over the entry's
/// statement + proof tokens, with L2 normalisation.
#[derive(Debug, Clone, Default)]
pub struct HashEmbedder;

impl Embedder for HashEmbedder {
    fn info(&self) -> EmbedderInfo {
        EmbedderInfo {
            model: "echidna-corpus-hash-v1".to_string(),
            dimensions: HASH_EMBED_DIM,
        }
    }

    fn embed(&self, entry: &CorpusEntry) -> Vec<f32> {
        let mut buckets = vec![0.0_f32; HASH_EMBED_DIM];
        let mut text = entry.statement.clone();
        if let Some(p) = &entry.proof {
            text.push(' ');
            text.push_str(p);
        }
        for tok in tokenise(&text) {
            let idx = bucket_for(tok);
            buckets[idx] += 1.0;
        }
        l2_normalise(&mut buckets);
        buckets
    }
}

fn tokenise(s: &str) -> impl Iterator<Item = &str> {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '=' | ':' | '"' | '|'
            )
    })
    .filter(|t| !t.is_empty())
}

/// FxHash-style fast hash; we only need stable bucketing, not crypto.
fn bucket_for(tok: &str) -> usize {
    let mut h: u64 = 0xcbf29ce484222325; // FNV-1a offset
    for b in tok.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    (h as usize) % HASH_EMBED_DIM
}

fn l2_normalise(v: &mut [f32]) {
    let norm: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
    if norm > 1e-9 {
        for x in v.iter_mut() {
            *x /= norm;
        }
    }
}

/// Cosine similarity between two vectors of the same dimension.
/// Returns 0.0 if either is zero.
pub fn cosine(a: &[f32], b: &[f32]) -> f32 {
    if a.len() != b.len() {
        return 0.0;
    }
    let dot: f32 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
    let na: f32 = a.iter().map(|x| x * x).sum::<f32>().sqrt();
    let nb: f32 = b.iter().map(|x| x * x).sum::<f32>().sqrt();
    if na < 1e-9 || nb < 1e-9 {
        0.0
    } else {
        dot / (na * nb)
    }
}

impl Corpus {
    /// Compute embeddings for every entry using the default
    /// `HashEmbedder`. Result is parallel to `self.entries`.
    pub fn compute_embeddings(&self) -> Vec<Vec<f32>> {
        let embedder = HashEmbedder;
        self.entries.iter().map(|e| embedder.embed(e)).collect()
    }

    /// Embed a free-form text query using the same default
    /// embedder. Used for `corpus query --near <text>`.
    pub fn embed_query(&self, query: &str) -> Vec<f32> {
        let synthetic = CorpusEntry {
            name: String::new(),
            qualified: String::new(),
            module_idx: 0,
            kind: super::DeclKind::Function,
            statement: query.to_string(),
            proof: None,
            line: 0,
            dependencies: vec![],
            axiom_usage: super::AxiomUsage::default(),
        };
        HashEmbedder.embed(&synthetic)
    }

    /// Top-k nearest entries to `query_vec` by cosine similarity.
    /// Each tuple is `(entry-index, similarity)`, sorted descending.
    pub fn nearest_neighbours(&self, query_vec: &[f32], k: usize) -> Vec<(usize, f32)> {
        let embeddings = self.compute_embeddings();
        let mut scored: Vec<(usize, f32)> = embeddings
            .iter()
            .enumerate()
            .map(|(i, v)| (i, cosine(query_vec, v)))
            .collect();
        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        scored.truncate(k);
        scored
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::{AxiomUsage, DeclKind, ModuleEntry};
    use std::path::PathBuf;

    fn sample_corpus() -> Corpus {
        let mut c = Corpus {
            adapter: "agda".into(),
            ..Default::default()
        };
        c.modules.push(ModuleEntry {
            name: "M".into(),
            path: PathBuf::from("M.agda"),
            options: vec![],
            imports: vec![],
            entries: vec![0, 1, 2],
        });
        c.entries.push(CorpusEntry {
            name: "wf-<".into(),
            qualified: "M.wf-<".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "WellFounded _<_".into(),
            proof: Some("acc lambda".into()),
            line: 1,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "Acc".into(),
            qualified: "M.Acc".into(),
            module_idx: 0,
            kind: DeclKind::Data,
            statement: "Acc R x".into(),
            proof: None,
            line: 5,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "Nat".into(),
            qualified: "M.Nat".into(),
            module_idx: 0,
            kind: DeclKind::Data,
            statement: "data Nat where zero suc".into(),
            proof: None,
            line: 10,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.reindex();
        c
    }

    #[test]
    fn hash_embedder_dimensions() {
        let c = sample_corpus();
        let embeds = c.compute_embeddings();
        assert_eq!(embeds.len(), 3);
        for v in &embeds {
            assert_eq!(v.len(), HASH_EMBED_DIM);
        }
    }

    #[test]
    fn cosine_similar_for_shared_vocab() {
        let c = sample_corpus();
        let embeds = c.compute_embeddings();
        // wf-< (mentions WellFounded + _<_) and Acc (mentions R + x)
        // should both be non-zero similar to a query about
        // well-foundedness.
        let q = c.embed_query("WellFounded _<_");
        let s_wf = cosine(&q, &embeds[0]);
        let s_acc = cosine(&q, &embeds[1]);
        let s_nat = cosine(&q, &embeds[2]);
        assert!(s_wf > 0.0, "wf-< should be similar to WellFounded query");
        assert!(s_wf >= s_nat, "wf-< should beat Nat for WF query");
        // Acc may or may not beat Nat depending on hash collisions;
        // the assertion is just that similarity is well-defined.
        assert!(s_acc.is_finite());
    }

    #[test]
    fn nearest_neighbours_top1_is_self() {
        let c = sample_corpus();
        let embeds = c.compute_embeddings();
        let nn = c.nearest_neighbours(&embeds[0], 1);
        assert_eq!(nn.len(), 1);
        assert_eq!(nn[0].0, 0);
        assert!((nn[0].1 - 1.0).abs() < 1e-5, "self-cosine should be 1.0");
    }
}
