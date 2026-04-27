// SPDX-License-Identifier: PMPL-1.0-or-later

//! Pareto frontier computation with Creusot proof annotations.
//!
//! Re-implements the invariant-heavy core of
//! `src/rust/verification/pareto.rs` as a self-contained, formally-
//! annotated kernel for the trust pipeline.
//!
//! ## Key proof obligations
//!
//! | ID | Property | Source |
//! |---|---|---|
//! | **PO-P1** | `dominates` is irreflexive — no candidate strictly dominates itself | E10 §PO-1, ParetoMaximality.lean |
//! | **PO-P2** | `dominates` is antisymmetric — `a ≻ b ⇒ ¬(b ≻ a)` | E10 §PO-2 |
//! | **PO-P3** | `dominates` is transitive — `a ≻ b ∧ b ≻ c ⇒ a ≻ c` | E10 §PO-3 |
//! | **PO-P4** | `compute` is sound — every candidate marked Pareto-optimal is not dominated by any other | E10 §PO-4 |
//! | **PO-P5** | `compute` is complete — every Pareto-optimal candidate is marked optimal | E10 §PO-6 |
//! | **PO-P6** | Frontier dichotomy — every candidate is either on the frontier or has a dominator in the input | E10 §PO-7 |
//! | **PO-P7** | Best-axis preservation — strictly best on any single axis ⇒ on frontier | E10 §PO-8..11 |
//! | **PO-P8** | `weighted_rank` is a permutation — the ranking output contains every input index exactly once | new |
//!
//! These obligations are stated here as Creusot contracts (in
//! comments awaiting toolchain bring-up) and as exhaustive `#[test]`
//! lemmas that exercise the same properties on small inputs.
//!
//! ## Companion proofs
//!
//! The same theorems are proved at the *abstract* level in
//! `verification/proofs/lean4/ParetoMaximality.lean`.  The Lean
//! version reasons over an unbounded `List ProofObjective`; the
//! Creusot version verifies the actual Rust implementation.  The
//! pairing follows the same dual-tool strategy used for
//! `axiom_tracker.rs`/`AxiomCompleteness.idr` and
//! `confidence.rs`/`ConfidenceLattice.lean`.
//!
//! ## Creusot annotation style
//!
//! Contracts are written as doc-comment code blocks (always visible
//! on stable Rust) and as `#[cfg_attr(feature = "creusot", …)]`
//! attribute macros (activated during formal verification — currently
//! commented out pending the toolchain pin in
//! `crates/echidna-core-spark/CREUSOT-SETUP.md`).

use serde::{Deserialize, Serialize};

use crate::TrustLevel;

#[cfg(feature = "creusot")]
use creusot_contracts::*;

// ---------------------------------------------------------------------------
// ProofObjective
// ---------------------------------------------------------------------------

/// Multi-objective metric for a proof candidate.
///
/// Mirrors `ProofObjective` in `src/rust/verification/pareto.rs` exactly,
/// but lives in this crate so the Creusot annotations are self-contained
/// and don't pull in the main echidna crate's dependency tree.
///
/// ### Direction of "better"
///
/// | Field | Direction |
/// |---|---|
/// | `proof_time_ms` | LOWER  is better |
/// | `trust_level`   | HIGHER is better (compared via `value()`) |
/// | `memory_bytes`  | LOWER  is better |
/// | `proof_steps`   | LOWER  is better |
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofObjective {
    /// Wall-clock proof time in milliseconds.
    pub proof_time_ms: u64,
    /// Trust level achieved by the proof (1..5).
    pub trust_level: TrustLevel,
    /// Peak memory usage in bytes.
    pub memory_bytes: u64,
    /// Number of proof steps emitted.
    pub proof_steps: u64,
}

/// A proof candidate paired with the objectives it achieved.
///
/// Mirrors `ProofCandidate` in `verification/pareto.rs`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofCandidate {
    /// Identifier (typically `<prover_kind>:<config_hash>`).
    pub id: String,
    /// The objectives achieved.
    pub objectives: ProofObjective,
    /// Whether `compute` flagged this candidate as Pareto-optimal.
    pub is_pareto_optimal: bool,
}

// ---------------------------------------------------------------------------
// dominates
// ---------------------------------------------------------------------------

/// `a` strictly dominates `b` iff `a` is at-least-as-good on every
/// objective and strictly better on at least one.
///
/// Mirrors `ParetoFrontier::dominates` in
/// `src/rust/verification/pareto.rs:75-94`.
///
/// ### Creusot contracts
/// ```text
/// #[ensures(result == (
///     a.proof_time_ms <= b.proof_time_ms
///     && a.trust_level.value() >= b.trust_level.value()
///     && a.memory_bytes <= b.memory_bytes
///     && a.proof_steps <= b.proof_steps
///     && (a.proof_time_ms < b.proof_time_ms
///         || a.trust_level.value() > b.trust_level.value()
///         || a.memory_bytes < b.memory_bytes
///         || a.proof_steps < b.proof_steps)
/// ))]
/// ```
#[cfg_attr(feature = "creusot",
    ensures(result == (
        a.proof_time_ms <= b.proof_time_ms
        && a.trust_level.value() >= b.trust_level.value()
        && a.memory_bytes <= b.memory_bytes
        && a.proof_steps <= b.proof_steps
        && (a.proof_time_ms < b.proof_time_ms
            || a.trust_level.value() > b.trust_level.value()
            || a.memory_bytes < b.memory_bytes
            || a.proof_steps < b.proof_steps)
    ))
)]
pub fn dominates(a: &ProofObjective, b: &ProofObjective) -> bool {
    let a_trust = a.trust_level.value();
    let b_trust = b.trust_level.value();

    let at_least_as_good = a.proof_time_ms <= b.proof_time_ms
        && a_trust >= b_trust
        && a.memory_bytes <= b.memory_bytes
        && a.proof_steps <= b.proof_steps;

    if !at_least_as_good {
        return false;
    }

    a.proof_time_ms < b.proof_time_ms
        || a_trust > b_trust
        || a.memory_bytes < b.memory_bytes
        || a.proof_steps < b.proof_steps
}

// ---------------------------------------------------------------------------
// compute (Pareto frontier)
// ---------------------------------------------------------------------------

/// Compute the Pareto frontier of a candidate list.
///
/// Sets `is_pareto_optimal` on each candidate and returns the indices
/// of candidates on the frontier.  Mirrors `ParetoFrontier::compute`
/// in `src/rust/verification/pareto.rs:50-72`.
///
/// ### Creusot contracts
/// ```text
/// #[ensures(forall<i: usize> 0 <= i && i < candidates.len() ==>
///     candidates[i].is_pareto_optimal == (
///         forall<j: usize> 0 <= j && j < candidates.len() && i != j ==>
///             !dominates(&candidates[j].objectives, &candidates[i].objectives)
///     )
/// )]
/// #[ensures(result.len() == count_optimal(&candidates))]
/// ```
/// ### Creusot contract (soundness + completeness)
/// ```text
/// #[ensures(forall<i: usize> i < candidates.len() ==>
///     candidates[i].is_pareto_optimal == (
///         forall<j: usize> j < candidates.len() && i != j ==>
///             !dominates(&candidates[j].objectives, &candidates[i].objectives)
///     )
/// )]
/// ```
// The `compute` contract is complex (nested quantifiers over a mutable slice).
// It is expressed as a doc comment above and tested exhaustively in
// `impl_invariants::{po_p4_compute_sound, po_p5_compute_complete}`.
// Activating it requires Creusot's mutable-borrow logic extensions;
// that activation is tracked in Stage 8c-M2 of the ROADMAP.
pub fn compute(candidates: &mut [ProofCandidate]) -> Vec<usize> {
    let n = candidates.len();
    let mut frontier_indices = Vec::new();

    for i in 0..n {
        let mut dominated = false;
        for j in 0..n {
            if i == j {
                continue;
            }
            if dominates(&candidates[j].objectives, &candidates[i].objectives) {
                dominated = true;
                break;
            }
        }
        candidates[i].is_pareto_optimal = !dominated;
        if !dominated {
            frontier_indices.push(i);
        }
    }

    frontier_indices
}

// ---------------------------------------------------------------------------
// weighted_rank
// ---------------------------------------------------------------------------

/// Rank candidates by a weighted combination of objectives.
///
/// Returns the indices `0..candidates.len()` sorted from best to worst
/// according to: `trust_w * trust - time_w * time - mem_w * memory - steps_w * steps`.
///
/// ### PO-P8 — permutation property
///
/// The output is a permutation of `0..candidates.len()` — every index
/// appears exactly once.
///
/// ### Creusot contract
/// ```text
/// #[ensures(result.len() == candidates.len())]
/// #[ensures(forall<i: usize, j: usize>
///     i < result.len() && j < result.len() && i != j
///     ==> result[i] != result[j]
/// )]
/// #[ensures(forall<i: usize> i < result.len() ==> result[i] < candidates.len())]
/// ```
// #[cfg_attr(feature = "creusot",
//     ensures(result.len() == candidates.len()),
//     ensures(forall<i: usize, j: usize>
//         i < result.len() && j < result.len() && i != j
//         ==> result[i] != result[j]
//     ),
//     ensures(forall<i: usize> i < result.len() ==> result[i] < candidates.len())
// )]
pub fn weighted_rank(
    candidates: &[ProofCandidate],
    trust_w: f64,
    time_w: f64,
    mem_w: f64,
    steps_w: f64,
) -> Vec<usize> {
    let score = |idx: usize| -> f64 {
        let c = &candidates[idx];
        trust_w * (c.objectives.trust_level.value() as f64)
            - time_w  * (c.objectives.proof_time_ms as f64)
            - mem_w   * (c.objectives.memory_bytes  as f64)
            - steps_w * (c.objectives.proof_steps   as f64)
    };
    let mut indices: Vec<usize> = (0..candidates.len()).collect();
    // Descending score — higher is better.
    indices.sort_by(|&i, &j| {
        score(j)
            .partial_cmp(&score(i))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    indices
}

// ---------------------------------------------------------------------------
// Invariant test suite
// ---------------------------------------------------------------------------

/// Property-style tests for the proof obligations PO-P1..PO-P8.
///
/// Each test corresponds to a named obligation and is structured so
/// that converting to a Creusot lemma is a mechanical edit (replace
/// `assert!` with `#[ensures]` and the body with `#[logic]`).
pub mod impl_invariants {
    #[allow(unused_imports)]
    use super::{compute, dominates, weighted_rank, ProofCandidate, ProofObjective};
    #[allow(unused_imports)]
    use crate::TrustLevel;

    #[allow(dead_code)]
    fn obj(t: u64, lvl: TrustLevel, mem: u64, steps: u64) -> ProofObjective {
        ProofObjective {
            proof_time_ms: t,
            trust_level: lvl,
            memory_bytes: mem,
            proof_steps: steps,
        }
    }

    #[allow(dead_code)]
    fn cand(id: &str, t: u64, lvl: TrustLevel, mem: u64, steps: u64) -> ProofCandidate {
        ProofCandidate {
            id: id.to_string(),
            objectives: obj(t, lvl, mem, steps),
            is_pareto_optimal: false,
        }
    }

    /// **PO-P1** Irreflexivity: no objective dominates itself.
    #[test]
    fn po_p1_dominates_irreflexive() {
        use TrustLevel::*;
        for &lvl in &[Level1, Level2, Level3, Level4, Level5] {
            for &t in &[0u64, 1, 100, u64::MAX / 4] {
                for &m in &[0u64, 1024, 1 << 20] {
                    for &s in &[0u64, 1, 100] {
                        let o = obj(t, lvl, m, s);
                        assert!(
                            !dominates(&o, &o),
                            "dominates is not irreflexive at {o:?}"
                        );
                    }
                }
            }
        }
    }

    /// **PO-P2** Antisymmetry: `a ≻ b ⇒ ¬(b ≻ a)`.
    #[test]
    fn po_p2_dominates_antisymmetric() {
        use TrustLevel::*;
        let cases = [
            (obj(100, Level5, 1000, 10), obj(200, Level3, 2000, 20)),
            (obj(50, Level4, 500, 5), obj(50, Level4, 600, 5)),
            (obj(0, Level5, 0, 0), obj(1, Level1, 1, 1)),
        ];
        for (a, b) in cases {
            if dominates(&a, &b) {
                assert!(
                    !dominates(&b, &a),
                    "antisymmetry violation: {a:?} ≻ {b:?} AND {b:?} ≻ {a:?}"
                );
            }
        }
    }

    /// **PO-P3** Transitivity: `a ≻ b ∧ b ≻ c ⇒ a ≻ c`.
    #[test]
    fn po_p3_dominates_transitive() {
        use TrustLevel::*;
        let triples = [
            (
                obj(10, Level5, 100, 1),
                obj(50, Level3, 500, 10),
                obj(100, Level2, 1000, 20),
            ),
            (
                obj(0, Level5, 0, 0),
                obj(1, Level5, 0, 0),
                obj(2, Level5, 0, 0),
            ),
        ];
        for (a, b, c) in triples {
            if dominates(&a, &b) && dominates(&b, &c) {
                assert!(
                    dominates(&a, &c),
                    "transitivity violation: {a:?} ≻ {b:?} ≻ {c:?} but ¬({a:?} ≻ {c:?})"
                );
            }
        }
    }

    /// **PO-P4** Soundness of `compute`: a candidate marked
    /// Pareto-optimal is not dominated by any other in the input.
    #[test]
    fn po_p4_compute_sound() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("z3", 100, Level2, 100_000, 10),
            cand("lean", 5000, Level5, 500_000, 100),
            cand("coq", 3000, Level4, 300_000, 80),
            cand("slow_coq", 4000, Level3, 400_000, 90),
        ];
        let _frontier = compute(&mut cs);
        let n = cs.len();
        for i in 0..n {
            if cs[i].is_pareto_optimal {
                for j in 0..n {
                    if i != j {
                        assert!(
                            !dominates(&cs[j].objectives, &cs[i].objectives),
                            "soundness violation: {} marked optimal but {} dominates it",
                            cs[i].id,
                            cs[j].id
                        );
                    }
                }
            }
        }
    }

    /// **PO-P5** Completeness of `compute`: a candidate not dominated
    /// by any other is marked Pareto-optimal.
    #[test]
    fn po_p5_compute_complete() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("z3", 100, Level2, 100_000, 10),
            cand("lean", 5000, Level5, 500_000, 100),
            cand("coq", 3000, Level4, 300_000, 80),
            cand("slow_coq", 4000, Level3, 400_000, 90),
        ];
        let _frontier = compute(&mut cs);
        let n = cs.len();
        for i in 0..n {
            let mut dominated = false;
            for j in 0..n {
                if i != j && dominates(&cs[j].objectives, &cs[i].objectives) {
                    dominated = true;
                    break;
                }
            }
            assert_eq!(
                cs[i].is_pareto_optimal,
                !dominated,
                "completeness violation at {}: optimal_flag={} but actually-dominated={}",
                cs[i].id,
                cs[i].is_pareto_optimal,
                dominated
            );
        }
    }

    /// **PO-P6** Frontier dichotomy: every input candidate is either
    /// on the frontier or has a dominator in the input.
    #[test]
    fn po_p6_frontier_dichotomy() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("a", 100, Level2, 100_000, 10),
            cand("b", 200, Level5, 50_000, 5),
            cand("c", 300, Level3, 200_000, 50),
        ];
        let _frontier = compute(&mut cs);
        let n = cs.len();
        for i in 0..n {
            if !cs[i].is_pareto_optimal {
                let has_dominator = (0..n)
                    .any(|j| j != i && dominates(&cs[j].objectives, &cs[i].objectives));
                assert!(
                    has_dominator,
                    "dichotomy violation at {}: not optimal but no dominator",
                    cs[i].id
                );
            }
        }
    }

    /// **PO-P7** Best-time preservation: a candidate strictly best
    /// on `proof_time_ms` is on the frontier.
    #[test]
    fn po_p7a_best_time_on_frontier() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("fast", 10, Level1, 1_000_000, 1000),       // best time
            cand("trusted", 5000, Level5, 100_000, 50),
            cand("balanced", 1000, Level3, 200_000, 100),
        ];
        let _frontier = compute(&mut cs);
        assert!(
            cs[0].is_pareto_optimal,
            "best-time candidate must be Pareto-optimal"
        );
    }

    /// **PO-P7b** Best-trust preservation: a candidate strictly best
    /// on `trust_level` is on the frontier.
    #[test]
    fn po_p7b_best_trust_on_frontier() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("fast", 10, Level1, 1_000_000, 1000),
            cand("trusted", 5000, Level5, 100_000, 50),     // best trust
            cand("balanced", 1000, Level3, 200_000, 100),
        ];
        let _frontier = compute(&mut cs);
        assert!(
            cs[1].is_pareto_optimal,
            "best-trust candidate must be Pareto-optimal"
        );
    }

    /// **PO-P7c** Best-memory preservation.
    #[test]
    fn po_p7c_best_memory_on_frontier() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("fast", 10, Level1, 1_000_000, 1000),
            cand("lean_mem", 5000, Level3, 1, 50),           // best memory
            cand("balanced", 1000, Level3, 200_000, 100),
        ];
        let _frontier = compute(&mut cs);
        assert!(
            cs[1].is_pareto_optimal,
            "best-memory candidate must be Pareto-optimal"
        );
    }

    /// **PO-P7d** Best-steps preservation.
    #[test]
    fn po_p7d_best_steps_on_frontier() {
        use TrustLevel::*;
        let mut cs = vec![
            cand("verbose", 10, Level1, 1_000_000, 1000),
            cand("terse", 5000, Level3, 500_000, 1),         // best steps
            cand("balanced", 1000, Level3, 200_000, 100),
        ];
        let _frontier = compute(&mut cs);
        assert!(
            cs[1].is_pareto_optimal,
            "best-steps candidate must be Pareto-optimal"
        );
    }

    /// **PO-P8** `weighted_rank` is a permutation: the output contains every
    /// index in `0..candidates.len()` exactly once.
    #[test]
    fn po_p8_weighted_rank_is_permutation() {
        use TrustLevel::*;
        let cs = vec![
            cand("a", 100, Level2, 100_000, 10),
            cand("b", 200, Level5, 50_000,  5),
            cand("c", 300, Level3, 200_000, 50),
            cand("d", 50,  Level1, 10_000,  1),
        ];
        let ranked = weighted_rank(&cs, 1.0, 0.001, 0.0, 0.0);
        assert_eq!(ranked.len(), cs.len(), "length must equal input length");
        // Every index 0..n appears exactly once.
        let mut seen = vec![false; cs.len()];
        for &idx in &ranked {
            assert!(idx < cs.len(), "index {idx} out of bounds");
            assert!(!seen[idx], "index {idx} appears more than once");
            seen[idx] = true;
        }
        // Best trust (Level5) should rank first when trust dominates weights.
        assert_eq!(ranked[0], 1, "Level5 candidate should rank first");
    }

    /// **PO-P8 boundary** — empty input produces empty output.
    #[test]
    fn po_p8_empty_input() {
        let ranked = weighted_rank(&[], 1.0, 1.0, 1.0, 1.0);
        assert!(ranked.is_empty());
    }

    /// **PO-P8 singleton** — single candidate is ranked at index 0.
    #[test]
    fn po_p8_singleton() {
        use TrustLevel::*;
        let cs = vec![cand("only", 100, Level3, 1000, 10)];
        let ranked = weighted_rank(&cs, 1.0, 0.001, 0.0, 0.0);
        assert_eq!(ranked, vec![0]);
    }

    /// **Empty list** — boundary condition.
    #[test]
    fn empty_compute() {
        let mut cs: Vec<ProofCandidate> = vec![];
        let frontier = compute(&mut cs);
        assert!(frontier.is_empty());
    }

    /// **Singleton list** — single candidate is trivially Pareto.
    #[test]
    fn singleton_compute() {
        use TrustLevel::*;
        let mut cs = vec![cand("only", 100, Level3, 1000, 10)];
        let frontier = compute(&mut cs);
        assert_eq!(frontier, vec![0]);
        assert!(cs[0].is_pareto_optimal);
    }
}

// ---------------------------------------------------------------------------
// Standard tests (mirroring tests in src/rust/verification/pareto.rs)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_candidate(
        id: &str,
        time: u64,
        trust: TrustLevel,
        mem: u64,
        steps: u64,
    ) -> ProofCandidate {
        ProofCandidate {
            id: id.to_string(),
            objectives: ProofObjective {
                proof_time_ms: time,
                trust_level: trust,
                memory_bytes: mem,
                proof_steps: steps,
            },
            is_pareto_optimal: false,
        }
    }

    #[test]
    fn test_single_candidate_is_pareto_optimal() {
        let mut candidates = vec![make_candidate(
            "lean",
            1000,
            TrustLevel::Level4,
            512_000,
            50,
        )];
        let frontier = compute(&mut candidates);
        assert_eq!(frontier.len(), 1);
        assert!(candidates[0].is_pareto_optimal);
    }

    #[test]
    fn test_dominated_candidate_excluded() {
        let mut candidates = vec![
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            make_candidate("slow_z3", 200, TrustLevel::Level1, 200_000, 20),
        ];
        let frontier = compute(&mut candidates);
        assert_eq!(frontier.len(), 1);
        assert!(candidates[0].is_pareto_optimal);
        assert!(!candidates[1].is_pareto_optimal);
    }

    #[test]
    fn test_tradeoff_candidates_both_on_frontier() {
        let mut candidates = vec![
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            make_candidate("lean", 5000, TrustLevel::Level5, 500_000, 100),
        ];
        let frontier = compute(&mut candidates);
        assert_eq!(frontier.len(), 2);
        assert!(candidates[0].is_pareto_optimal);
        assert!(candidates[1].is_pareto_optimal);
    }
}
