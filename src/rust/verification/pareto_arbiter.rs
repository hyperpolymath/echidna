// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Pareto-frontier arbiter for proof outcomes.
//!
//! When multiple provers agree on the verdict but differ in
//! (latency, axiom-cost, certificate-size, confidence), this module
//! returns the non-dominated set and a tiebreak-selected
//! recommendation. It is a thin arbitration wrapper on top of the
//! existing generic [`super::pareto`] frontier — that one operates
//! on a different objective vector and is left untouched.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

use super::bayesian_arbiter::Verdict;
use crate::provers::ProverKind;

/// A single prover attempt's measured outcome, used as a point in
/// the 4-dimensional objective space.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct AttemptOutcome {
    pub prover: ProverKind,
    pub verdict: Verdict,
    /// Self-reported (or default) confidence, 0..1. Higher is better.
    pub confidence: f64,
    /// Wall-clock latency in milliseconds. Lower is better.
    pub latency_ms: u64,
    /// Number of declared axioms relied on. Lower is better.
    pub axiom_cost: u32,
    /// Certificate size in bytes (0 if no certificate). Lower is better.
    pub certificate_size_bytes: u64,
}

/// How to pick a recommendation when multiple frontier points
/// remain after Pareto filtering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Tiebreak {
    MinAxiom,
    MinLatency,
    MaxConfidence,
    MinCertificate,
}

impl Default for Tiebreak {
    fn default() -> Self {
        Tiebreak::MinAxiom
    }
}

/// Arbitration decision: the frontier, a recommendation, and how
/// many of the inputs were dominated.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParetoDecision {
    pub frontier: Vec<AttemptOutcome>,
    pub recommended: Option<AttemptOutcome>,
    pub dominated_count: usize,
}

/// Pareto-frontier arbiter — configured with a tiebreak rule.
#[derive(Debug, Clone)]
pub struct ParetoArbiter {
    tiebreak: Tiebreak,
}

impl ParetoArbiter {
    pub fn new() -> Self {
        Self {
            tiebreak: Tiebreak::default(),
        }
    }

    /// Builder-style: replace the tiebreak rule.
    pub fn with_tiebreak(mut self, t: Tiebreak) -> Self {
        self.tiebreak = t;
        self
    }

    /// Compute the Pareto frontier and a tiebreak-selected pick.
    ///
    /// Callers should pre-filter to a single agreed verdict
    /// (e.g. via the Bayesian arbiter); mixed verdicts will still
    /// return *some* frontier but its interpretation is undefined.
    pub fn arbitrate(&self, outcomes: &[AttemptOutcome]) -> ParetoDecision {
        if outcomes.is_empty() {
            return ParetoDecision {
                frontier: vec![],
                recommended: None,
                dominated_count: 0,
            };
        }

        let mut frontier: Vec<AttemptOutcome> = Vec::with_capacity(outcomes.len());
        let mut dominated_count = 0;

        'outer: for (i, candidate) in outcomes.iter().enumerate() {
            for (j, other) in outcomes.iter().enumerate() {
                if i == j {
                    continue;
                }
                if dominates(other, candidate) {
                    dominated_count += 1;
                    continue 'outer;
                }
            }
            frontier.push(*candidate);
        }

        let recommended = self.select_recommendation(&frontier);

        ParetoDecision {
            frontier,
            recommended,
            dominated_count,
        }
    }

    fn select_recommendation(&self, frontier: &[AttemptOutcome]) -> Option<AttemptOutcome> {
        if frontier.is_empty() {
            return None;
        }
        let pick = match self.tiebreak {
            Tiebreak::MinAxiom => frontier
                .iter()
                .min_by_key(|o| (o.axiom_cost, o.latency_ms))?,
            Tiebreak::MinLatency => frontier
                .iter()
                .min_by_key(|o| (o.latency_ms, o.axiom_cost))?,
            Tiebreak::MaxConfidence => frontier.iter().max_by(|a, b| {
                a.confidence
                    .partial_cmp(&b.confidence)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })?,
            Tiebreak::MinCertificate => frontier
                .iter()
                .min_by_key(|o| (o.certificate_size_bytes, o.latency_ms))?,
        };
        Some(*pick)
    }
}

impl Default for ParetoArbiter {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns true iff `a` Pareto-dominates `b` over the 4 objectives.
///
/// `a` dominates `b` iff:
/// - a.latency_ms              <= b.latency_ms
/// - a.axiom_cost              <= b.axiom_cost
/// - a.certificate_size_bytes  <= b.certificate_size_bytes
/// - a.confidence              >= b.confidence
/// AND at least one of these is strict.
fn dominates(a: &AttemptOutcome, b: &AttemptOutcome) -> bool {
    let no_worse = a.latency_ms <= b.latency_ms
        && a.axiom_cost <= b.axiom_cost
        && a.certificate_size_bytes <= b.certificate_size_bytes
        && a.confidence >= b.confidence;
    if !no_worse {
        return false;
    }
    let strictly_better = a.latency_ms < b.latency_ms
        || a.axiom_cost < b.axiom_cost
        || a.certificate_size_bytes < b.certificate_size_bytes
        || a.confidence > b.confidence;
    strictly_better
}

#[cfg(test)]
mod tests {
    use super::*;

    fn outcome(
        prover: ProverKind,
        confidence: f64,
        latency_ms: u64,
        axiom_cost: u32,
        certificate_size_bytes: u64,
    ) -> AttemptOutcome {
        AttemptOutcome {
            prover,
            verdict: Verdict::Proven,
            confidence,
            latency_ms,
            axiom_cost,
            certificate_size_bytes,
        }
    }

    #[test]
    fn single_outcome_is_its_own_frontier() {
        let arb = ParetoArbiter::new();
        let o = outcome(ProverKind::Z3, 0.95, 100, 0, 1024);
        let d = arb.arbitrate(&[o]);
        assert_eq!(d.frontier.len(), 1);
        assert_eq!(d.dominated_count, 0);
        assert!(d.recommended.is_some());
    }

    #[test]
    fn pareto_incomparable_pair_both_on_frontier() {
        // a: faster but more axioms; b: slower but fewer axioms.
        let a = outcome(ProverKind::Z3, 0.9, 100, 5, 1024);
        let b = outcome(ProverKind::Coq, 0.9, 500, 0, 1024);
        let arb = ParetoArbiter::new(); // MinAxiom tiebreak
        let d = arb.arbitrate(&[a, b]);
        assert_eq!(d.frontier.len(), 2);
        assert_eq!(d.dominated_count, 0);
        // MinAxiom should pick b.
        assert_eq!(d.recommended.unwrap().prover, ProverKind::Coq);
    }

    #[test]
    fn clear_dominator_shrinks_frontier_to_one() {
        // a dominates b on all four axes.
        let a = outcome(ProverKind::Z3, 0.99, 50, 0, 256);
        let b = outcome(ProverKind::CVC5, 0.80, 500, 3, 4096);
        let arb = ParetoArbiter::new();
        let d = arb.arbitrate(&[a, b]);
        assert_eq!(d.frontier.len(), 1);
        assert_eq!(d.dominated_count, 1);
        assert_eq!(d.recommended.unwrap().prover, ProverKind::Z3);
    }

    #[test]
    fn tiebreak_min_latency_picks_fastest() {
        let a = outcome(ProverKind::Z3, 0.9, 100, 5, 1024);
        let b = outcome(ProverKind::Coq, 0.9, 500, 0, 1024);
        let arb = ParetoArbiter::new().with_tiebreak(Tiebreak::MinLatency);
        let d = arb.arbitrate(&[a, b]);
        assert_eq!(d.recommended.unwrap().prover, ProverKind::Z3);
    }

    #[test]
    fn tiebreak_max_confidence_picks_most_confident() {
        let a = outcome(ProverKind::Z3, 0.99, 100, 5, 1024);
        let b = outcome(ProverKind::Coq, 0.80, 500, 0, 1024);
        let arb = ParetoArbiter::new().with_tiebreak(Tiebreak::MaxConfidence);
        let d = arb.arbitrate(&[a, b]);
        // Both should be on the frontier (incomparable on the 4 axes)
        // — but tiebreak should pick Z3 for higher confidence.
        assert_eq!(d.recommended.unwrap().prover, ProverKind::Z3);
    }

    #[test]
    fn empty_input_yields_empty_decision() {
        let arb = ParetoArbiter::new();
        let d = arb.arbitrate(&[]);
        assert!(d.frontier.is_empty());
        assert!(d.recommended.is_none());
        assert_eq!(d.dominated_count, 0);
    }
}
