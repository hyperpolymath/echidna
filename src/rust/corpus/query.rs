// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Multi-axis query DSL — capstone of the N-dim VeriSim plan.
//!
//! Composes filters, similarity-near, ordering, and limit into a
//! single builder over the corpus's multi-modal index. Replaces the
//! ad-hoc `find` / `closure` / `reverse_deps` / `nearest_neighbours`
//! methods with a unified surface so downstream consumers (SA energy
//! in `learning/buchholz_rank.rs`, MCTS priors, the `suggest`
//! tactic-finder) all express their lookups the same way.
//!
//! Example:
//!
//! ```ignore
//! let hits = corpus.query()
//!     .where_kind(DeclKind::Function)
//!     .where_axiom_free()
//!     .where_recursive()
//!     .near_text("WellFounded _<_")
//!     .order_by(SortKey::Similarity)
//!     .limit(10)
//!     .run();
//! ```
//!
//! All predicates short-circuit lazily: filters apply before the
//! expensive embedding cosine pass; sort happens after filtering.

#![allow(dead_code)]

use std::cmp::Ordering;

use super::{Corpus, CorpusEntry, DeclKind};
use super::embed::cosine;
use super::metrics::EntryMetrics;

/// Builder for a multi-axis corpus query. Created via `Corpus::query`.
pub struct CorpusQuery<'c> {
    corpus: &'c Corpus,
    filters: Vec<Filter>,
    near_query: Option<Vec<f32>>,
    order: SortKey,
    limit: Option<usize>,
}

#[derive(Debug, Clone)]
enum Filter {
    Kind(DeclKind),
    KindIn(Vec<DeclKind>),
    AxiomFree,
    NoHazards,
    Recursive(bool),
    StructuralInduction(bool),
    NameContains(String),
    QualifiedContains(String),
    HeadSymbol(String),
    AdapterIs(String),
    HasReverseDeps(bool),
    /// Closures over `(entry, metrics)` for ad-hoc predicates.
    Custom(fn(&CorpusEntry, &EntryMetrics) -> bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortKey {
    /// No explicit sort — entries are returned in corpus order.
    Default,
    /// Sort by cosine similarity to `near_query` (descending).
    /// Falls back to Default if no near-query is set.
    Similarity,
    /// Ascending by `EntryMetrics::statement_tokens`.
    StatementSize,
    /// Ascending by `EntryMetrics::proof_depth`.
    ProofDepth,
    /// Descending by `EntryMetrics::dep_fanin` (most-depended-on first).
    Fanin,
    /// Descending by `EntryMetrics::dep_fanout`.
    Fanout,
}

/// One row of query output: the entry plus its metrics and (if a
/// near-query was set) the cosine similarity score.
pub struct QueryHit<'c> {
    pub entry: &'c CorpusEntry,
    pub metrics: EntryMetrics,
    pub similarity: Option<f32>,
}

impl Corpus {
    /// Begin a multi-axis query.
    pub fn query(&self) -> CorpusQuery<'_> {
        CorpusQuery {
            corpus: self,
            filters: Vec::new(),
            near_query: None,
            order: SortKey::Default,
            limit: None,
        }
    }
}

impl<'c> CorpusQuery<'c> {
    pub fn where_kind(mut self, k: DeclKind) -> Self {
        self.filters.push(Filter::Kind(k));
        self
    }

    pub fn where_kind_in(mut self, kinds: &[DeclKind]) -> Self {
        self.filters.push(Filter::KindIn(kinds.to_vec()));
        self
    }

    /// Exclude entries whose axiom_usage flags any hazard
    /// (postulate, believe_me, admitted, sorry, ...).
    pub fn where_axiom_free(mut self) -> Self {
        self.filters.push(Filter::AxiomFree);
        self
    }

    /// Exclude entries with any hazard except the explicit `Postulate`
    /// declaration kind (which is intentional, not a hazard).
    pub fn where_no_hazards(mut self) -> Self {
        self.filters.push(Filter::NoHazards);
        self
    }

    pub fn where_recursive(mut self) -> Self {
        self.filters.push(Filter::Recursive(true));
        self
    }

    pub fn where_non_recursive(mut self) -> Self {
        self.filters.push(Filter::Recursive(false));
        self
    }

    pub fn where_structural(mut self) -> Self {
        self.filters.push(Filter::StructuralInduction(true));
        self
    }

    pub fn where_name_contains(mut self, s: impl Into<String>) -> Self {
        self.filters.push(Filter::NameContains(s.into()));
        self
    }

    pub fn where_qualified_contains(mut self, s: impl Into<String>) -> Self {
        self.filters.push(Filter::QualifiedContains(s.into()));
        self
    }

    pub fn where_head_symbol(mut self, s: impl Into<String>) -> Self {
        self.filters.push(Filter::HeadSymbol(s.into()));
        self
    }

    pub fn where_adapter(mut self, a: impl Into<String>) -> Self {
        self.filters.push(Filter::AdapterIs(a.into()));
        self
    }

    pub fn where_has_reverse_deps(mut self) -> Self {
        self.filters.push(Filter::HasReverseDeps(true));
        self
    }

    pub fn where_custom(
        mut self,
        f: fn(&CorpusEntry, &EntryMetrics) -> bool,
    ) -> Self {
        self.filters.push(Filter::Custom(f));
        self
    }

    /// Cosine-similarity-near a free-form text query. Implies
    /// `SortKey::Similarity` unless the caller overrides.
    pub fn near_text(mut self, q: &str) -> Self {
        self.near_query = Some(self.corpus.embed_query(q));
        if matches!(self.order, SortKey::Default) {
            self.order = SortKey::Similarity;
        }
        self
    }

    /// Cosine-similarity-near a pre-computed embedding (e.g. from a
    /// GNN backend). Same Similarity-default semantics as `near_text`.
    pub fn near_vector(mut self, v: Vec<f32>) -> Self {
        self.near_query = Some(v);
        if matches!(self.order, SortKey::Default) {
            self.order = SortKey::Similarity;
        }
        self
    }

    pub fn order_by(mut self, key: SortKey) -> Self {
        self.order = key;
        self
    }

    pub fn limit(mut self, k: usize) -> Self {
        self.limit = Some(k);
        self
    }

    /// Execute the query. Returns `QueryHit`s in the requested order.
    pub fn run(self) -> Vec<QueryHit<'c>> {
        let metrics = self.corpus.compute_metrics();
        let mut results: Vec<QueryHit<'c>> = self
            .corpus
            .entries
            .iter()
            .enumerate()
            .filter_map(|(i, entry)| {
                let m = &metrics[i];
                if self.filters.iter().all(|f| filter_match(f, entry, m, self.corpus)) {
                    Some(QueryHit {
                        entry,
                        metrics: m.clone(),
                        similarity: None,
                    })
                } else {
                    None
                }
            })
            .collect();

        // Compute similarity (post-filter is cheaper).
        if let Some(qv) = &self.near_query {
            let embedder = super::embed::HashEmbedder;
            for hit in results.iter_mut() {
                let v = <super::embed::HashEmbedder as super::embed::Embedder>::embed(
                    &embedder, hit.entry,
                );
                hit.similarity = Some(cosine(qv, &v));
            }
        }

        // Sort.
        match self.order {
            SortKey::Default => {}
            SortKey::Similarity => {
                results.sort_by(|a, b| {
                    let sa = a.similarity.unwrap_or(0.0);
                    let sb = b.similarity.unwrap_or(0.0);
                    sb.partial_cmp(&sa).unwrap_or(Ordering::Equal)
                });
            }
            SortKey::StatementSize => {
                results.sort_by_key(|h| h.metrics.statement_tokens);
            }
            SortKey::ProofDepth => {
                results.sort_by_key(|h| h.metrics.proof_depth);
            }
            SortKey::Fanin => {
                results.sort_by(|a, b| b.metrics.dep_fanin.cmp(&a.metrics.dep_fanin));
            }
            SortKey::Fanout => {
                results.sort_by(|a, b| b.metrics.dep_fanout.cmp(&a.metrics.dep_fanout));
            }
        }

        if let Some(k) = self.limit {
            results.truncate(k);
        }
        results
    }
}

fn filter_match(
    f: &Filter,
    entry: &CorpusEntry,
    metrics: &EntryMetrics,
    corpus: &Corpus,
) -> bool {
    match f {
        Filter::Kind(k) => entry.kind == *k,
        Filter::KindIn(ks) => ks.contains(&entry.kind),
        Filter::AxiomFree => !entry.axiom_usage.any(),
        Filter::NoHazards => {
            !(entry.axiom_usage.believe_me
                || entry.axiom_usage.assert_total
                || entry.axiom_usage.admitted
                || entry.axiom_usage.sorry
                || entry.axiom_usage.trustme)
        }
        Filter::Recursive(want) => metrics.recursive == *want,
        Filter::StructuralInduction(want) => metrics.structural_induction == *want,
        Filter::NameContains(needle) => entry.name.contains(needle),
        Filter::QualifiedContains(needle) => entry.qualified.contains(needle),
        Filter::HeadSymbol(s) => metrics.head_symbol == *s,
        Filter::AdapterIs(a) => corpus.adapter == *a,
        Filter::HasReverseDeps(want) => {
            let has = corpus
                .dependents
                .get(&entry.name)
                .map(|v| !v.is_empty())
                .unwrap_or(false);
            has == *want
        }
        Filter::Custom(pred) => pred(entry, metrics),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::{AxiomUsage, ModuleEntry};
    use std::path::PathBuf;

    fn test_corpus() -> Corpus {
        let mut c = Corpus {
            adapter: "agda".into(),
            ..Default::default()
        };
        c.modules.push(ModuleEntry {
            name: "M".into(),
            path: PathBuf::from("M.agda"),
            options: vec![],
            imports: vec![],
            entries: vec![0, 1, 2, 3],
        });
        c.entries.push(CorpusEntry {
            name: "Ord".into(),
            qualified: "M.Ord".into(),
            module_idx: 0,
            kind: DeclKind::Data,
            statement: "Set".into(),
            proof: None,
            line: 1,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "wf-<".into(),
            qualified: "M.wf-<".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "WellFounded _<_".into(),
            proof: Some("wf-< zero = acc lambda\nwf-< (suc n) = wf-< n".into()),
            line: 5,
            dependencies: vec!["Ord".into()],
            axiom_usage: AxiomUsage::default(),
        });
        c.entries.push(CorpusEntry {
            name: "bad".into(),
            qualified: "M.bad".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "Bot".into(),
            proof: Some("bad = believe_me".into()),
            line: 10,
            dependencies: vec![],
            axiom_usage: AxiomUsage {
                believe_me: true,
                ..Default::default()
            },
        });
        c.entries.push(CorpusEntry {
            name: "EM".into(),
            qualified: "M.EM".into(),
            module_idx: 0,
            kind: DeclKind::Postulate,
            statement: "forall p, p \\/ ~p".into(),
            proof: None,
            line: 15,
            dependencies: vec![],
            axiom_usage: AxiomUsage {
                postulate: true,
                ..Default::default()
            },
        });
        c.reindex();
        c
    }

    #[test]
    fn filter_kind_function() {
        let c = test_corpus();
        let hits = c.query().where_kind(DeclKind::Function).run();
        let names: Vec<&str> = hits.iter().map(|h| h.entry.name.as_str()).collect();
        assert!(names.contains(&"wf-<"));
        assert!(names.contains(&"bad"));
        assert!(!names.contains(&"Ord"));
        assert!(!names.contains(&"EM"));
    }

    #[test]
    fn filter_axiom_free_excludes_postulates_and_hazards() {
        let c = test_corpus();
        let hits = c.query().where_axiom_free().run();
        let names: Vec<&str> = hits.iter().map(|h| h.entry.name.as_str()).collect();
        assert!(names.contains(&"Ord"));
        assert!(names.contains(&"wf-<"));
        assert!(!names.contains(&"bad"));
        assert!(!names.contains(&"EM"));
    }

    #[test]
    fn filter_recursive() {
        let c = test_corpus();
        let hits = c.query().where_recursive().run();
        let names: Vec<&str> = hits.iter().map(|h| h.entry.name.as_str()).collect();
        assert_eq!(names, vec!["wf-<"]); // wf-< calls itself in body
    }

    #[test]
    fn near_text_orders_by_similarity() {
        let c = test_corpus();
        let hits = c
            .query()
            .where_kind(DeclKind::Function)
            .near_text("WellFounded")
            .limit(2)
            .run();
        // wf-< (statement contains WellFounded) should beat bad
        // (statement is "Bot").
        assert!(!hits.is_empty());
        assert_eq!(hits[0].entry.name, "wf-<");
        // Similarity score is set when near_text was provided.
        assert!(hits[0].similarity.is_some());
    }

    #[test]
    fn order_by_fanin() {
        let c = test_corpus();
        let hits = c.query().order_by(SortKey::Fanin).run();
        // Ord has 1 dependent (wf-<); the rest have 0.
        assert_eq!(hits[0].entry.name, "Ord");
    }

    #[test]
    fn end_to_end_compositional_query() {
        let c = test_corpus();
        // "Recursive functions, axiom-free, sorted by similarity to a
        // well-foundedness query, top 1."
        let hits = c
            .query()
            .where_kind(DeclKind::Function)
            .where_axiom_free()
            .where_recursive()
            .near_text("WellFounded _<_")
            .limit(1)
            .run();
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].entry.name, "wf-<");
    }
}
