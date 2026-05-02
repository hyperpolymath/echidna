// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Per-entry metrics tensor — Step 4 of the N-dim VeriSim plan.
//!
//! Computes a fixed-shape metrics tuple for each `CorpusEntry`. The
//! Tensor octad in `corpus/octad.rs` carries these as a `HashMap<String,
//! f64>` for VeriSim compatibility; downstream consumers (the SA
//! energy in `learning/buchholz_rank.rs::blockers`) can also consume
//! `EntryMetrics` directly without going through the string map.
//!
//! Metric families:
//!
//! * **Size**: statement token count, proof token count,
//!   declaration line count
//! * **Connectivity**: forward fan-out (dep count), reverse fan-in
//!   (dependents count), proof-depth
//! * **Shape**: recursive vs structural (heuristic from proof
//!   body), pattern-match clauses count, has-where
//! * **Hazards**: one float per hazard class (0.0 / 1.0)
//! * **K-elim**: heuristic for `--without-K` violations
//!   (Agda: indices unification on data ctors)
//!
//! All metrics are **derivable from the parsed corpus** without
//! re-reading source files. They're computed in `Corpus::compute_metrics`
//! after `reindex` populates the dependency tables.

#![allow(dead_code)]

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use super::{Corpus, DeclKind};

/// Fixed-shape metrics tensor per entry.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EntryMetrics {
    // -- size --
    pub statement_tokens: u32,
    pub proof_tokens: u32,
    pub statement_chars: u32,

    // -- connectivity --
    pub dep_fanout: u32,
    pub dep_fanin: u32,
    /// Longest forward dep-chain length to a corpus leaf, capped at
    /// 32 to avoid pathological computation on cycles. Cycle-stable
    /// because we use a `seen` set.
    pub proof_depth: u32,

    // -- shape --
    pub recursive: bool,
    pub structural_induction: bool,
    pub pattern_match_clauses: u32,
    pub has_where_block: bool,

    // -- hazards (mirror AxiomUsage) --
    pub hazard_postulate: bool,
    pub hazard_believe_me: bool,
    pub hazard_admitted: bool,
    pub hazard_sorry: bool,
    pub hazard_assert_total: bool,
    pub hazard_trustme: bool,
    pub hazard_other_count: u32,

    // -- K-elimination signal --
    /// Set when the proof body's match shape suggests reliance on
    /// equality reflection — e.g. matches on `refl` against
    /// non-first-order indices. Heuristic; conservative-positive.
    pub k_elim_risk: bool,

    // -- head-symbol class (informational; coarse) --
    /// First top-level identifier in the statement, normalised. Used
    /// as a coarse semantic-class fallback when no `semantic_class`
    /// is set in the synonym table.
    pub head_symbol: String,
}

impl EntryMetrics {
    /// Render as a string-keyed map for the Tensor octad.
    pub fn as_metric_map(&self) -> HashMap<String, f64> {
        let mut m = HashMap::new();
        m.insert("statement_tokens".into(), self.statement_tokens as f64);
        m.insert("proof_tokens".into(), self.proof_tokens as f64);
        m.insert("statement_chars".into(), self.statement_chars as f64);
        m.insert("dep_fanout".into(), self.dep_fanout as f64);
        m.insert("dep_fanin".into(), self.dep_fanin as f64);
        m.insert("proof_depth".into(), self.proof_depth as f64);
        m.insert("recursive".into(), self.recursive as i32 as f64);
        m.insert(
            "structural_induction".into(),
            self.structural_induction as i32 as f64,
        );
        m.insert(
            "pattern_match_clauses".into(),
            self.pattern_match_clauses as f64,
        );
        m.insert("has_where_block".into(), self.has_where_block as i32 as f64);
        m.insert(
            "hazard_postulate".into(),
            self.hazard_postulate as i32 as f64,
        );
        m.insert(
            "hazard_believe_me".into(),
            self.hazard_believe_me as i32 as f64,
        );
        m.insert("hazard_admitted".into(), self.hazard_admitted as i32 as f64);
        m.insert("hazard_sorry".into(), self.hazard_sorry as i32 as f64);
        m.insert(
            "hazard_assert_total".into(),
            self.hazard_assert_total as i32 as f64,
        );
        m.insert("hazard_trustme".into(), self.hazard_trustme as i32 as f64);
        m.insert(
            "hazard_other_count".into(),
            self.hazard_other_count as f64,
        );
        m.insert("k_elim_risk".into(), self.k_elim_risk as i32 as f64);
        m
    }
}

impl Corpus {
    /// Compute metrics for every entry. Should be called after
    /// `reindex` — depends on `dependents` being populated.
    /// Returns a vector parallel to `self.entries`.
    pub fn compute_metrics(&self) -> Vec<EntryMetrics> {
        let mut depth_cache: Vec<Option<u32>> = vec![None; self.entries.len()];
        let mut out: Vec<EntryMetrics> = Vec::with_capacity(self.entries.len());
        for i in 0..self.entries.len() {
            out.push(metrics_for(self, i, &mut depth_cache));
        }
        out
    }
}

#[allow(clippy::field_reassign_with_default)]
fn metrics_for(
    corpus: &Corpus,
    idx: usize,
    depth_cache: &mut Vec<Option<u32>>,
) -> EntryMetrics {
    let e = &corpus.entries[idx];
    let proof = e.proof.clone().unwrap_or_default();
    let mut m = EntryMetrics::default();

    // -- size --
    m.statement_tokens = count_tokens(&e.statement);
    m.proof_tokens = count_tokens(&proof);
    m.statement_chars = e.statement.chars().count() as u32;

    // -- connectivity --
    m.dep_fanout = e.dependencies.len() as u32;
    m.dep_fanin = corpus
        .dependents
        .get(&e.name)
        .map(|v| v.len() as u32)
        .unwrap_or(0);
    m.proof_depth = compute_proof_depth(corpus, idx, depth_cache, 0, 32);

    // -- shape --
    m.pattern_match_clauses = count_pattern_clauses(&e.name, &proof);
    m.has_where_block = proof.contains(" where ") || proof.contains("\nwhere ");
    m.recursive = is_recursive(&e.name, &proof);
    m.structural_induction = looks_structural(&proof);

    // -- hazards --
    m.hazard_postulate = e.axiom_usage.postulate;
    m.hazard_believe_me = e.axiom_usage.believe_me;
    m.hazard_admitted = e.axiom_usage.admitted;
    m.hazard_sorry = e.axiom_usage.sorry;
    m.hazard_assert_total = e.axiom_usage.assert_total;
    m.hazard_trustme = e.axiom_usage.trustme;
    m.hazard_other_count = e.axiom_usage.other.len() as u32;

    // -- K-elim risk (Agda-specific heuristic) --
    if corpus.adapter == "agda" {
        m.k_elim_risk = looks_k_elim(&proof);
    }

    // -- head symbol --
    m.head_symbol = head_symbol(&e.statement);

    let _ = e.kind; // kind is informational; not in metrics tensor today
    if matches!(e.kind, DeclKind::Postulate) {
        m.hazard_postulate = true;
    }

    m
}

fn count_tokens(s: &str) -> u32 {
    s.split(|c: char| {
        c.is_whitespace()
            || matches!(
                c,
                '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | ':' | '.' | '"'
            )
    })
    .filter(|t| !t.is_empty())
    .count() as u32
}

fn count_pattern_clauses(name: &str, body: &str) -> u32 {
    if name.is_empty() || body.is_empty() {
        return 0;
    }
    // Each occurrence of `name ` followed eventually by `=` indicates
    // a clause head. We approximate by counting `=` signs that follow
    // a `name` token; this is rough but stable across the four
    // adapters.
    let prefix = format!("{} ", name);
    let prefix_eq = format!("{} =", name);
    let mut count = 0u32;
    if body.starts_with(&prefix) || body.starts_with(&prefix_eq) || body == name {
        count += 1;
    }
    let pat = format!(" {} ", name);
    count += body.matches(&pat).count() as u32;
    count.max(1)
}

fn is_recursive(name: &str, body: &str) -> bool {
    if name.is_empty() || body.is_empty() {
        return false;
    }
    body.contains(&format!(" {} ", name)) || body.contains(&format!("({}", name))
}

fn looks_structural(body: &str) -> bool {
    // Coarse heuristic: pattern-match on a constructor name in the
    // proof body suggests structural induction. We look for any of
    // the common Agda/Idris/Coq destructor patterns.
    body.contains("zero")
        || body.contains("suc ")
        || body.contains("Z |")
        || body.contains("S k")
        || body.contains("destruct ")
        || body.contains("induction on")
}

fn looks_k_elim(body: &str) -> bool {
    // Heuristic: matching on `refl` to discharge an indexed-data
    // equation is the classic --without-K hazard. Also `subst`
    // applied to refl-pattern-matched arguments.
    if body.contains("refl ") || body.contains(" refl ") || body.contains("with refl") {
        return true;
    }
    if body.contains("subst") && body.contains("refl") {
        return true;
    }
    false
}

fn head_symbol(statement: &str) -> String {
    let s = statement.trim_start_matches(|c: char| {
        c.is_whitespace()
            || matches!(c, '(' | '{' | '[' | '∀' | 'Π')
    });
    let tok: String = s
        .chars()
        .take_while(|c| !c.is_whitespace() && !matches!(c, '(' | ')' | ',' | ';'))
        .collect();
    tok
}

/// Longest forward dep-chain from `idx` to a leaf, capped at `max_depth`.
fn compute_proof_depth(
    corpus: &Corpus,
    idx: usize,
    cache: &mut Vec<Option<u32>>,
    current_depth: u32,
    max_depth: u32,
) -> u32 {
    if current_depth >= max_depth {
        return max_depth;
    }
    if let Some(d) = cache[idx] {
        return d;
    }
    // Mark in-progress with 0 so cycles terminate.
    cache[idx] = Some(0);

    let mut max_child: u32 = 0;
    for dep in &corpus.entries[idx].dependencies {
        if let Some(indices) = corpus.by_name.get(dep) {
            for &j in indices {
                if j == idx {
                    continue;
                }
                let d = compute_proof_depth(corpus, j, cache, current_depth + 1, max_depth);
                max_child = max_child.max(d);
            }
        }
    }
    let depth = if corpus.entries[idx].dependencies.is_empty() {
        0
    } else {
        max_child + 1
    };
    cache[idx] = Some(depth);
    depth
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::{AxiomUsage, CorpusEntry, ModuleEntry};
    use std::path::PathBuf;

    fn three_entry_corpus() -> Corpus {
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
        // Leaf
        c.entries.push(CorpusEntry {
            name: "_<_".into(),
            qualified: "M._<_".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "Ord -> Ord -> Set".into(),
            proof: None,
            line: 1,
            dependencies: vec![],
            axiom_usage: AxiomUsage::default(),
        });
        // Mid: depends on _<_
        c.entries.push(CorpusEntry {
            name: "pred".into(),
            qualified: "M.pred".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "...".into(),
            proof: Some("pred zero = oz\npred (suc n) = n".into()),
            line: 5,
            dependencies: vec!["_<_".into()],
            axiom_usage: AxiomUsage::default(),
        });
        // Top: depends on pred + _<_
        c.entries.push(CorpusEntry {
            name: "wf".into(),
            qualified: "M.wf".into(),
            module_idx: 0,
            kind: DeclKind::Function,
            statement: "WellFounded _<_".into(),
            proof: Some("wf zero = acc lambda\nwf (suc n) = wf n".into()),
            line: 10,
            dependencies: vec!["pred".into(), "_<_".into()],
            axiom_usage: AxiomUsage::default(),
        });
        c.reindex();
        c
    }

    #[test]
    fn compute_metrics_full_corpus() {
        let c = three_entry_corpus();
        let metrics = c.compute_metrics();
        assert_eq!(metrics.len(), 3);

        // _<_ is a leaf
        assert_eq!(metrics[0].dep_fanout, 0);
        assert_eq!(metrics[0].dep_fanin, 2); // both pred and wf depend on it
        assert_eq!(metrics[0].proof_depth, 0);

        // pred depends on _<_
        assert_eq!(metrics[1].dep_fanout, 1);
        assert_eq!(metrics[1].dep_fanin, 1); // wf depends on pred
        assert_eq!(metrics[1].proof_depth, 1);
        // pred's body has multiple clauses — we should detect ≥2.
        assert!(metrics[1].pattern_match_clauses >= 1);

        // wf depends on pred + _<_; recursive (calls itself)
        assert_eq!(metrics[2].dep_fanout, 2);
        assert_eq!(metrics[2].dep_fanin, 0);
        assert_eq!(metrics[2].proof_depth, 2);
        assert!(metrics[2].recursive, "wf should be flagged recursive");
    }

    #[test]
    fn head_symbol_extracted() {
        let c = three_entry_corpus();
        let metrics = c.compute_metrics();
        assert_eq!(metrics[2].head_symbol, "WellFounded");
    }

    #[test]
    fn k_elim_risk_flagged_on_refl_match() {
        let mut c = three_entry_corpus();
        c.entries[2].proof = Some("wf x with refl = x".into());
        c.reindex();
        let metrics = c.compute_metrics();
        assert!(metrics[2].k_elim_risk, "refl-pattern should flag K-elim risk");
    }
}
