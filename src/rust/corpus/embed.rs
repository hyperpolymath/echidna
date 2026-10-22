// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: MPL-2.0

//! Vector-octad embeddings for the corpus — Step 5 of the N-dim
//! VeriSim plan.
//!
//! Three backends:
//!
//! 1. **Structural n-gram hashing** (default, offline): normalise the
//!    statement through [`super::canonical`], then hash its 1-, 2- and
//!    3-grams of canonical atoms into 256 buckets, weighted by n-gram
//!    order and L2-normalised. Because the input is the *canonical*
//!    token stream, `x + y = y + x` in Coq and `(+ x y) = (+ y x)` in
//!    SMT-LIB land on the same buckets — the vector carries type
//!    structure, not surface spelling. Still free, deterministic and
//!    offline, and still no training run: it is the baseline the Flux
//!    GNN is measured against, not a replacement for it.
//!
//! 2. **Hashing-trick over raw text** ([`HashEmbedder`], 32-dim): the
//!    original backend, kept because `src/rust/gnn/embeddings.rs`
//!    fixes `FEATURE_DIM = 32` for node features and some deployments
//!    want the narrow, GNN-compatible vector.
//!
//! 3. **GNN client** (future, online): for when the Julia server at
//!    `/gnn/embed` is primed against real proof corpora (Wave-3 ML
//!    work tracked in `docs/handover/TODO.adoc`). The trait `Embedder`
//!    abstracts the choice; replacing the default
//!    [`StructuralEmbedder`] with a `GnnEmbedder` is one-line.
//!
//! The corpus's `compute_embeddings` returns `Vec<Vec<f32>>` parallel
//! to `entries`; `octad.rs::save_octads_jsonl` populates each Vector
//! modality from this. Cosine-similarity helper lives here too.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

use super::{Corpus, CorpusEntry};

/// Embedding dimension of the *legacy* raw-text hashing-trick
/// embedder. Chosen to match the 32-dim GNN local-term embeddings
/// already shipped in `src/rust/gnn/embeddings.rs` (`FEATURE_DIM = 32`),
/// so stored octads can be re-embedded from the GNN client without
/// changing dimensions.
pub const HASH_EMBED_DIM: usize = 32;

/// Embedding dimension of the default structural embedder (E7
/// `VectorModality`). 256 buckets is enough to keep 1–3-gram
/// collisions rare on the estate's corpora while staying trivially
/// hashable, sortable and comparable — the point is a usable
/// similarity baseline before any trained model exists.
pub const STRUCTURAL_EMBED_DIM: usize = 256;

/// Weights applied to 1-, 2- and 3-grams respectively. Unigrams carry
/// the vocabulary, longer n-grams carry the type structure.
const NGRAM_WEIGHTS: [f32; 3] = [1.0, 0.6, 0.35];

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbedderInfo {
    pub model: String,
    pub dimensions: usize,
}

pub trait Embedder {
    fn info(&self) -> EmbedderInfo;
    fn embed(&self, entry: &CorpusEntry) -> Vec<f32>;
}

/// Legacy offline embedder: hashing-trick over the entry's raw
/// statement + proof tokens, with L2 normalisation. Superseded as the
/// default by [`StructuralEmbedder`]; retained because
/// `src/rust/gnn/embeddings.rs` fixes 32-dim features and some stored
/// octads carry `echidna-corpus-hash-v1` vectors.
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

/// Default offline embedder: n-gram hashing over the *canonical* type
/// shape (see [`super::canonical`]).
///
/// Feature layout: every unigram, bigram and trigram of the canonical
/// atom stream is hashed into one of [`STRUCTURAL_EMBED_DIM`] buckets
/// and accumulated with [`NGRAM_WEIGHTS`]; the vector is L2-normalised
/// so cosine similarity is meaningful. Deterministic, dependency-free
/// and identical on every platform.
#[derive(Debug, Clone, Default)]
pub struct StructuralEmbedder;

impl Embedder for StructuralEmbedder {
    fn info(&self) -> EmbedderInfo {
        EmbedderInfo {
            model: "echidna-corpus-structural-v2".to_string(),
            dimensions: STRUCTURAL_EMBED_DIM,
        }
    }

    fn embed(&self, entry: &CorpusEntry) -> Vec<f32> {
        let atoms = super::canonical::canonical_tokens(&entry.statement);
        embed_atoms(&atoms)
    }
}

/// Hash a canonical atom stream into a [`STRUCTURAL_EMBED_DIM`] vector.
///
/// Shared by entry embedding and free-text query embedding so the two
/// always live in the same space.
pub fn embed_atoms(atoms: &[String]) -> Vec<f32> {
    let mut buckets = vec![0.0_f32; STRUCTURAL_EMBED_DIM];
    for n in 1..=3usize {
        if atoms.len() < n {
            break;
        }
        let weight = NGRAM_WEIGHTS[n - 1];
        for window in atoms.windows(n) {
            let key = window.join("\u{1f}");
            buckets[bucket_for_dim(&key, STRUCTURAL_EMBED_DIM)] += weight;
        }
    }
    l2_normalise(&mut buckets);
    buckets
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
    bucket_for_dim(tok, HASH_EMBED_DIM)
}

fn bucket_for_dim(tok: &str, dim: usize) -> usize {
    let mut h: u64 = 0xcbf29ce484222325; // FNV-1a offset
    for b in tok.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    (h as usize) % dim
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
    /// [`StructuralEmbedder`] (256-dim). Result is parallel to
    /// `self.entries`.
    pub fn compute_embeddings(&self) -> Vec<Vec<f32>> {
        let embedder = StructuralEmbedder;
        self.entries.iter().map(|e| embedder.embed(e)).collect()
    }

    /// Compute 32-dim GNN-compatible embeddings with the legacy
    /// raw-text hashing trick. Used where a consumer expects
    /// `FEATURE_DIM` vectors.
    pub fn compute_embeddings_legacy(&self) -> Vec<Vec<f32>> {
        let embedder = HashEmbedder;
        self.entries.iter().map(|e| embedder.embed(e)).collect()
    }

    /// Embed a free-form text query into the same space as
    /// [`Corpus::compute_embeddings`]. Used for `corpus near <text>`,
    /// which runs the query through the *same* canonicaliser so a
    /// query written in one prover's syntax matches statements written
    /// in another's.
    pub fn embed_query(&self, query: &str) -> Vec<f32> {
        let atoms = super::canonical::canonical_tokens(query);
        embed_atoms(&atoms)
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
    fn structural_embedder_is_256_dimensional_by_default() {
        let c = sample_corpus();
        let embeds = c.compute_embeddings();
        assert_eq!(embeds.len(), 3);
        for v in &embeds {
            assert_eq!(v.len(), STRUCTURAL_EMBED_DIM);
            assert_eq!(v.len(), 256);
        }
        let info = StructuralEmbedder.info();
        assert_eq!(info.dimensions, STRUCTURAL_EMBED_DIM);
        assert_eq!(info.model, "echidna-corpus-structural-v2");
    }

    #[test]
    fn legacy_hash_embedder_stays_32_dimensional() {
        let c = sample_corpus();
        let embeds = c.compute_embeddings_legacy();
        assert_eq!(embeds.len(), 3);
        for v in &embeds {
            assert_eq!(v.len(), HASH_EMBED_DIM);
        }
        assert_eq!(HashEmbedder.info().dimensions, 32);
    }

    #[test]
    fn queries_match_across_prover_syntaxes() {
        // An entry written the way Coq writes it, queried the way SMT-LIB
        // writes it: the canonical stream is what gets hashed, so the two
        // must land close together — and far from an unrelated statement.
        let mut c = Corpus {
            adapter: "coq".into(),
            ..Default::default()
        };
        c.entries.push(CorpusEntry {
            name: "add_comm".into(),
            qualified: "Nat.add_comm".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "forall x y : nat, x + y = y + x".into(),
            proof: None,
            line: 1,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "mul_zero".into(),
            qualified: "Nat.mul_zero".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "forall n : nat, n * 0 = 0".into(),
            proof: None,
            line: 2,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.reindex();

        let embeds = c.compute_embeddings();
        let q = c.embed_query("(assert (forall ((x Nat) (y Nat)) (= (+ x y) (+ y x))))");
        let same = cosine(&q, &embeds[0]);
        let other = cosine(&q, &embeds[1]);
        assert!(
            same > other,
            "cross-syntax query should match the same theorem: {same} vs {other}"
        );
        assert!(same > 0.8, "expected a close match, got {same}");
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
