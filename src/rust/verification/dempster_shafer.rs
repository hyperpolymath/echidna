// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Dempster-Shafer evidence combination for prover arbitration.
//!
//! Each prover contributes a [`MassFunction`] over a small frame of
//! discernment {Proven, Refuted, NotApplicable}. We fuse via
//! Dempster's rule of combination (commutative + associative) and
//! report belief/plausibility intervals — the natural generalisation
//! of Bayes when sources can explicitly express ignorance.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::provers::ProverKind;

/// Errors raised during Dempster-Shafer combination.
#[derive(Debug, Error)]
pub enum ArbiterError {
    #[error("conflict mass exceeds threshold (k = {0})")]
    HighConflict(f64),
    #[error("no evidence submitted")]
    EmptyEvidence,
    #[error("invalid mass function: {0}")]
    InvalidMass(String),
}

/// Subsets of the 3-element frame {Proven, Refuted, NotApplicable}
/// that we actually use as focal elements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum VerdictSet {
    /// Singleton {Proven}.
    Proven,
    /// Singleton {Refuted}.
    Refuted,
    /// {Proven, Refuted} — definitely a verdict but unclear direction.
    ProvenOrRefuted,
    /// Whole frame Θ = {Proven, Refuted, NotApplicable} — ignorance.
    Unknown,
    /// Empty set ∅ — used internally to capture conflict mass.
    Empty,
}

impl VerdictSet {
    /// Set-theoretic intersection in the focal-element lattice we expose.
    fn intersect(self, other: VerdictSet) -> VerdictSet {
        use VerdictSet::*;
        // Whole frame ∩ X = X
        match (self, other) {
            (Unknown, x) | (x, Unknown) => x,
            (Empty, _) | (_, Empty) => Empty,
            (Proven, Proven) => Proven,
            (Refuted, Refuted) => Refuted,
            (Proven, Refuted) | (Refuted, Proven) => Empty,
            (ProvenOrRefuted, ProvenOrRefuted) => ProvenOrRefuted,
            (ProvenOrRefuted, Proven) | (Proven, ProvenOrRefuted) => Proven,
            (ProvenOrRefuted, Refuted) | (Refuted, ProvenOrRefuted) => Refuted,
        }
    }

    fn contains_proven(self) -> bool {
        matches!(self, VerdictSet::Proven | VerdictSet::ProvenOrRefuted | VerdictSet::Unknown)
    }

    fn contains_refuted(self) -> bool {
        matches!(self, VerdictSet::Refuted | VerdictSet::ProvenOrRefuted | VerdictSet::Unknown)
    }
}

/// Mass function over [`VerdictSet`]. The masses on the
/// non-empty focal elements must sum to ~1.0; we tolerate ε drift.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MassFunction {
    pub focal_elements: Vec<(VerdictSet, f64)>,
}

impl MassFunction {
    /// Validate that masses sum to ~1.0 and are non-negative.
    fn validate(&self) -> Result<(), ArbiterError> {
        let mut total = 0.0;
        for (set, m) in &self.focal_elements {
            if *m < 0.0 || !m.is_finite() {
                return Err(ArbiterError::InvalidMass(format!(
                    "negative or non-finite mass on {set:?}: {m}"
                )));
            }
            if matches!(set, VerdictSet::Empty) && *m > 1e-9 {
                return Err(ArbiterError::InvalidMass(
                    "non-zero mass on Empty in input".into(),
                ));
            }
            total += m;
        }
        if (total - 1.0).abs() > 1e-3 {
            return Err(ArbiterError::InvalidMass(format!(
                "masses sum to {total}, expected 1.0"
            )));
        }
        Ok(())
    }

    /// Pure ignorance — all mass on Θ.
    pub fn ignorance() -> Self {
        Self {
            focal_elements: vec![(VerdictSet::Unknown, 1.0)],
        }
    }

    /// Singleton commitment to Proven with given mass; remainder on Unknown.
    pub fn proven(mass: f64) -> Self {
        let m = mass.clamp(0.0, 1.0);
        Self {
            focal_elements: vec![(VerdictSet::Proven, m), (VerdictSet::Unknown, 1.0 - m)],
        }
    }

    /// Singleton commitment to Refuted with given mass; remainder on Unknown.
    pub fn refuted(mass: f64) -> Self {
        let m = mass.clamp(0.0, 1.0);
        Self {
            focal_elements: vec![(VerdictSet::Refuted, m), (VerdictSet::Unknown, 1.0 - m)],
        }
    }
}

/// Translate a "Proven" verdict + how-close-to-timeout into a mass
/// function. As the run approaches its timeout, mass shifts from
/// Proven onto Unknown (the prover may have squeezed out the result
/// near the wire — less reliable).
pub fn proven_mass(time_ms: u64, timeout_ms: u64) -> MassFunction {
    if timeout_ms == 0 {
        return MassFunction::ignorance();
    }
    let ratio = (time_ms as f64 / timeout_ms as f64).clamp(0.0, 1.0);
    // mass on Proven ramps from 0.95 (instant) down to 0.50 (at-timeout).
    let m_proven = 0.95 - 0.45 * ratio;
    MassFunction::proven(m_proven)
}

/// Symmetric helper for refutation.
pub fn refuted_mass(time_ms: u64, timeout_ms: u64) -> MassFunction {
    if timeout_ms == 0 {
        return MassFunction::ignorance();
    }
    let ratio = (time_ms as f64 / timeout_ms as f64).clamp(0.0, 1.0);
    let m_refuted = 0.95 - 0.45 * ratio;
    MassFunction::refuted(m_refuted)
}

/// Belief / plausibility intervals over the singleton verdicts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BeliefPlausibility {
    pub belief_proven: f64,
    pub plausibility_proven: f64,
    pub belief_refuted: f64,
    pub plausibility_refuted: f64,
    /// Total conflict mass (k); normalisation divisor in Dempster's rule.
    pub conflict_k: f64,
}

/// Dempster-Shafer arbiter — accumulates per-prover mass functions
/// and combines them on demand.
#[derive(Debug, Default)]
pub struct DempsterShaferArbiter {
    masses: Vec<(ProverKind, MassFunction)>,
}

impl DempsterShaferArbiter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a prover's mass function. The mass is validated on submit.
    pub fn submit(&mut self, prover: ProverKind, mass: MassFunction) {
        if mass.validate().is_ok() {
            self.masses.push((prover, mass));
        }
    }

    /// Combine all submitted masses via Dempster's rule of combination.
    pub fn combine_all(&self) -> Result<BeliefPlausibility, ArbiterError> {
        if self.masses.is_empty() {
            return Err(ArbiterError::EmptyEvidence);
        }
        let mut acc = self.masses[0].1.clone();
        let mut total_k = 0.0;
        for (_, next) in self.masses.iter().skip(1) {
            let (combined, k) = combine_two(&acc, next)?;
            total_k = 1.0 - (1.0 - total_k) * (1.0 - k);
            acc = combined;
        }
        if total_k > 0.95 {
            return Err(ArbiterError::HighConflict(total_k));
        }
        Ok(belief_plausibility(&acc, total_k))
    }
}

/// Dempster's combination of two mass functions. Returns the
/// combined (normalised) mass and the local conflict mass k.
fn combine_two(a: &MassFunction, b: &MassFunction) -> Result<(MassFunction, f64), ArbiterError> {
    use std::collections::HashMap;

    let mut joint: HashMap<VerdictSet, f64> = HashMap::new();
    let mut k = 0.0;

    for (sa, ma) in &a.focal_elements {
        for (sb, mb) in &b.focal_elements {
            let inter = sa.intersect(*sb);
            let m = ma * mb;
            if matches!(inter, VerdictSet::Empty) {
                k += m;
            } else {
                *joint.entry(inter).or_insert(0.0) += m;
            }
        }
    }

    if k >= 1.0 - 1e-9 {
        return Err(ArbiterError::HighConflict(k));
    }
    let denom = 1.0 - k;
    let normalised: Vec<(VerdictSet, f64)> =
        joint.into_iter().map(|(s, m)| (s, m / denom)).collect();
    Ok((
        MassFunction {
            focal_elements: normalised,
        },
        k,
    ))
}

fn belief_plausibility(m: &MassFunction, conflict_k: f64) -> BeliefPlausibility {
    let mut bel_p = 0.0;
    let mut bel_r = 0.0;
    let mut pl_p = 0.0;
    let mut pl_r = 0.0;
    for (set, mass) in &m.focal_elements {
        // Belief of singleton X = sum of masses on subsets of X.
        // Within our lattice, only the singleton itself is a subset of {X}.
        match set {
            VerdictSet::Proven => bel_p += mass,
            VerdictSet::Refuted => bel_r += mass,
            _ => {},
        }
        // Plausibility of {X} = sum of masses on focal sets that intersect {X}.
        if set.contains_proven() {
            pl_p += mass;
        }
        if set.contains_refuted() {
            pl_r += mass;
        }
    }
    BeliefPlausibility {
        belief_proven: bel_p,
        plausibility_proven: pl_p,
        belief_refuted: bel_r,
        plausibility_refuted: pl_r,
        conflict_k,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn two_provers_both_proven_high_mass() {
        let mut arb = DempsterShaferArbiter::new();
        arb.submit(ProverKind::Z3, MassFunction::proven(0.9));
        arb.submit(ProverKind::CVC5, MassFunction::proven(0.9));
        let bp = arb.combine_all().expect("combine ok");
        assert!(
            bp.belief_proven > 0.9,
            "expected belief_proven > 0.9, got {}",
            bp.belief_proven
        );
        assert!(bp.conflict_k < 0.1);
    }

    #[test]
    fn proven_vs_refuted_yields_conflict() {
        let mut arb = DempsterShaferArbiter::new();
        arb.submit(ProverKind::Z3, MassFunction::proven(0.9));
        arb.submit(ProverKind::Coq, MassFunction::refuted(0.9));
        // Two near-certain singletons that disagree -> very high k -> error.
        let res = arb.combine_all();
        match res {
            Err(ArbiterError::HighConflict(k)) => {
                assert!(k > 0.5, "expected conflict > 0.5, got {k}");
            },
            other => panic!("expected HighConflict, got {other:?}"),
        }
    }

    #[test]
    fn moderate_disagreement_gives_high_conflict_k() {
        // Lower-mass disagreement to land below the 0.95 trip.
        let mut arb = DempsterShaferArbiter::new();
        arb.submit(ProverKind::Z3, MassFunction::proven(0.7));
        arb.submit(ProverKind::Coq, MassFunction::refuted(0.7));
        let bp = arb.combine_all().expect("conflict below 0.95");
        assert!(
            bp.conflict_k > 0.4,
            "expected conflict_k > 0.4, got {}",
            bp.conflict_k
        );
    }

    #[test]
    fn pure_ignorance_yields_zero_belief_full_plausibility() {
        let mut arb = DempsterShaferArbiter::new();
        arb.submit(ProverKind::Z3, MassFunction::ignorance());
        arb.submit(ProverKind::CVC5, MassFunction::ignorance());
        let bp = arb.combine_all().expect("ignorance is consistent");
        assert!(bp.belief_proven.abs() < 1e-9);
        assert!((bp.plausibility_proven - 1.0).abs() < 1e-9);
    }

    #[test]
    fn proven_mass_helper_shifts_with_timeout_proximity() {
        let near_start = proven_mass(100, 10_000);
        let near_end = proven_mass(9_500, 10_000);
        let m_start = focal_mass(&near_start, VerdictSet::Proven);
        let m_end = focal_mass(&near_end, VerdictSet::Proven);
        assert!(m_start > m_end, "{m_start} should be > {m_end}");
    }

    #[test]
    fn empty_evidence_errors() {
        let arb = DempsterShaferArbiter::new();
        assert!(matches!(
            arb.combine_all(),
            Err(ArbiterError::EmptyEvidence)
        ));
    }

    fn focal_mass(m: &MassFunction, target: VerdictSet) -> f64 {
        m.focal_elements
            .iter()
            .find(|(s, _)| *s == target)
            .map(|(_, v)| *v)
            .unwrap_or(0.0)
    }
}
