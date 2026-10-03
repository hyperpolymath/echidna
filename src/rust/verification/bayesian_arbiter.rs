// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Bayesian arbiter for prover-evidence fusion.
//!
//! Treats each prover as a noisy binary sensor with calibrated
//! (precision-when-true, precision-when-false) likelihoods, then
//! combines independent observations into a posterior over the
//! verdict using log-odds accumulation (numerically stable).
//!
//! This is a complement to the existing simple-majority
//! [`super::portfolio::PortfolioSolver`]: where portfolio reports
//! a categorical agreement summary, this module returns a
//! probability distribution + Shannon entropy.

#![allow(dead_code)]

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::provers::ProverKind;

/// Verdict produced by a prover for a single goal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Verdict {
    Proven,
    Refuted,
    Timeout,
    Unknown,
    Error,
}

/// A single piece of prover evidence to be combined into the posterior.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverEvidence {
    pub prover: ProverKind,
    pub verdict: Verdict,
    pub time_ms: u64,
    /// Optional prover-self-reported confidence (0..1) — currently
    /// used as a soft modulator on the configured likelihood.
    pub confidence_self_reported: Option<f64>,
}

/// Per-prover likelihood: P(verdict=true | actually-true)
/// and P(verdict=true | actually-false) — i.e. (precision, 1-FPR).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
struct Likelihood {
    /// P(prover says "Proven" | goal is actually true).
    p_correct_given_true: f64,
    /// P(prover says "Refuted" | goal is actually false).
    p_correct_given_false: f64,
}

impl Default for Likelihood {
    fn default() -> Self {
        Self {
            p_correct_given_true: 0.85,
            p_correct_given_false: 0.85,
        }
    }
}

/// Posterior over the verdict frame after Bayesian combination.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PosteriorVerdict {
    pub p_proven: f64,
    pub p_refuted: f64,
    pub p_unknown: f64,
    pub entropy_bits: f64,
    pub winning: Verdict,
}

/// Bayesian arbiter — accumulates per-prover likelihoods and
/// fuses evidence streams into a posterior.
#[derive(Debug, Clone)]
pub struct BayesianArbiter {
    /// Prior probability that the goal is true (Proven).
    prior_p_true: f64,
    /// Per-prover likelihood overrides; missing entries use defaults.
    likelihoods: HashMap<ProverKind, Likelihood>,
}

impl BayesianArbiter {
    /// Create with a uniform-ish prior (commonly 0.5 for neutrality
    /// or skewed when historical priors are known).
    pub fn new(prior_p_true: f64) -> Self {
        let clamped = prior_p_true.clamp(1e-6, 1.0 - 1e-6);
        Self {
            prior_p_true: clamped,
            likelihoods: default_likelihoods(),
        }
    }

    /// Override the likelihood for a specific prover.
    pub fn with_prover_likelihood(
        mut self,
        prover: ProverKind,
        p_correct_given_true: f64,
        p_correct_given_false: f64,
    ) -> Self {
        self.likelihoods.insert(
            prover,
            Likelihood {
                p_correct_given_true: p_correct_given_true.clamp(1e-6, 1.0 - 1e-6),
                p_correct_given_false: p_correct_given_false.clamp(1e-6, 1.0 - 1e-6),
            },
        );
        self
    }

    fn likelihood_for(&self, prover: ProverKind) -> Likelihood {
        self.likelihoods.get(&prover).copied().unwrap_or_default()
    }

    /// Combine evidence into a posterior. Timeout/Unknown/Error
    /// observations contribute a likelihood ratio of 1.0 (no update).
    pub fn combine(&self, evidence: &[ProverEvidence]) -> PosteriorVerdict {
        // Log-odds accumulation: start from prior log-odds,
        // sum log(LR) for each Proven/Refuted observation.
        let mut log_odds_true = logit(self.prior_p_true);

        for e in evidence {
            let lk = self.likelihood_for(e.prover);
            let (p_obs_given_true, p_obs_given_false) = match e.verdict {
                Verdict::Proven => (lk.p_correct_given_true, 1.0 - lk.p_correct_given_false),
                Verdict::Refuted => (1.0 - lk.p_correct_given_true, lk.p_correct_given_false),
                Verdict::Timeout | Verdict::Unknown | Verdict::Error => continue,
            };
            // Soft modulation by self-reported confidence (if present).
            let weight = e.confidence_self_reported.unwrap_or(1.0).clamp(0.0, 1.0);
            let lr = (p_obs_given_true / p_obs_given_false).max(1e-12);
            log_odds_true += weight * lr.ln();
        }

        let p_true = sigmoid(log_odds_true);
        // Reserve a small mass for "Unknown" proportional to
        // how many timeouts/unknowns we saw (heuristic — keeps
        // entropy informative even when posterior is decisive).
        let n_total = evidence.len().max(1) as f64;
        let n_no_info = evidence
            .iter()
            .filter(|e| {
                matches!(
                    e.verdict,
                    Verdict::Timeout | Verdict::Unknown | Verdict::Error
                )
            })
            .count() as f64;
        let p_unknown = (n_no_info / n_total).clamp(0.0, 0.5);
        let scale = 1.0 - p_unknown;
        let p_proven = p_true * scale;
        let p_refuted = (1.0 - p_true) * scale;

        let entropy_bits = shannon_entropy_bits(&[p_proven, p_refuted, p_unknown]);
        let winning = if p_proven >= p_refuted && p_proven >= p_unknown {
            Verdict::Proven
        } else if p_refuted >= p_unknown {
            Verdict::Refuted
        } else {
            Verdict::Unknown
        };

        PosteriorVerdict {
            p_proven,
            p_refuted,
            p_unknown,
            entropy_bits,
            winning,
        }
    }
}

impl Default for BayesianArbiter {
    fn default() -> Self {
        Self::new(0.5)
    }
}

/// Built-in calibration table for the Tier-1 backends. Numbers are
/// nominal — calibration against echidna's empirical corpus belongs
/// in a follow-up.
fn default_likelihoods() -> HashMap<ProverKind, Likelihood> {
    let mut m = HashMap::new();
    let high_smt = Likelihood {
        p_correct_given_true: 0.95,
        p_correct_given_false: 0.92,
    };
    let atp = Likelihood {
        p_correct_given_true: 0.93,
        p_correct_given_false: 0.90,
    };
    let itp = Likelihood {
        p_correct_given_true: 0.98,
        p_correct_given_false: 0.95,
    };
    let auto_active = Likelihood {
        p_correct_given_true: 0.90,
        p_correct_given_false: 0.88,
    };

    m.insert(ProverKind::Z3, high_smt);
    m.insert(ProverKind::CVC5, high_smt);
    m.insert(ProverKind::Vampire, atp);
    m.insert(ProverKind::EProver, atp);
    m.insert(ProverKind::Coq, itp);
    m.insert(ProverKind::Lean, itp);
    m.insert(ProverKind::Isabelle, itp);
    m.insert(ProverKind::Agda, itp);
    m.insert(ProverKind::Idris2, itp);
    m.insert(ProverKind::Dafny, auto_active);
    m.insert(ProverKind::Why3, auto_active);
    m
}

fn logit(p: f64) -> f64 {
    let p = p.clamp(1e-12, 1.0 - 1e-12);
    (p / (1.0 - p)).ln()
}

fn sigmoid(x: f64) -> f64 {
    if x >= 0.0 {
        let z = (-x).exp();
        1.0 / (1.0 + z)
    } else {
        let z = x.exp();
        z / (1.0 + z)
    }
}

fn shannon_entropy_bits(ps: &[f64]) -> f64 {
    let log2 = std::f64::consts::LN_2;
    let mut h = 0.0;
    for &p in ps {
        if p > 0.0 {
            h -= p * (p.ln() / log2);
        }
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(prover: ProverKind, verdict: Verdict) -> ProverEvidence {
        ProverEvidence {
            prover,
            verdict,
            time_ms: 100,
            confidence_self_reported: None,
        }
    }

    #[test]
    fn single_z3_proven_yields_high_posterior() {
        let arb = BayesianArbiter::new(0.5);
        let post = arb.combine(&[ev(ProverKind::Z3, Verdict::Proven)]);
        assert!(
            post.p_proven > 0.9,
            "expected p_proven > 0.9, got {}",
            post.p_proven
        );
        assert_eq!(post.winning, Verdict::Proven);
    }

    #[test]
    fn conflicting_z3_proven_and_coq_refuted_depends_on_priors() {
        // Coq has higher precision than Z3 in the default table —
        // so a tied 1-vs-1 should lean toward Refuted.
        let arb = BayesianArbiter::new(0.5);
        let post = arb.combine(&[
            ev(ProverKind::Z3, Verdict::Proven),
            ev(ProverKind::Coq, Verdict::Refuted),
        ]);
        assert!(
            post.p_refuted > post.p_proven,
            "Coq's higher precision should outweigh Z3: got p_proven={} p_refuted={}",
            post.p_proven,
            post.p_refuted
        );

        // With a heavily Proven-skewed prior, Z3's Proven can win.
        let arb_skewed = BayesianArbiter::new(0.99);
        let post_skewed = arb_skewed.combine(&[
            ev(ProverKind::Z3, Verdict::Proven),
            ev(ProverKind::Coq, Verdict::Refuted),
        ]);
        assert!(
            post_skewed.p_proven > post.p_proven,
            "prior skew should shift the posterior"
        );
    }

    #[test]
    fn timeouts_only_leave_entropy_at_prior_entropy() {
        let arb = BayesianArbiter::new(0.5);
        let post = arb.combine(&[
            ev(ProverKind::Z3, Verdict::Timeout),
            ev(ProverKind::Coq, Verdict::Timeout),
        ]);
        // With a uniform prior, the proven/refuted split should be balanced.
        assert!((post.p_proven - post.p_refuted).abs() < 1e-9);
        // And a chunk of mass should be on Unknown (since all evidence is timeout).
        assert!(
            post.p_unknown > 0.0,
            "expected some Unknown mass, got {}",
            post.p_unknown
        );
        assert!(
            post.entropy_bits > 0.5,
            "entropy should remain near maximal, got {}",
            post.entropy_bits
        );
    }

    #[test]
    fn empty_evidence_returns_prior() {
        let arb = BayesianArbiter::new(0.7);
        let post = arb.combine(&[]);
        // p_unknown=0 (no timeouts), so p_proven ≈ prior, p_refuted ≈ 1-prior.
        assert!((post.p_proven - 0.7).abs() < 1e-6);
        assert!((post.p_refuted - 0.3).abs() < 1e-6);
    }

    #[test]
    fn unknown_prover_uses_default_likelihood() {
        // Storm isn't in the default table; should fall back to 0.85/0.85.
        let arb = BayesianArbiter::new(0.5);
        let post = arb.combine(&[ev(ProverKind::Storm, Verdict::Proven)]);
        assert!(post.p_proven > 0.5);
        assert!(post.p_proven < 0.9); // weaker than a Z3 Proven
    }
}
