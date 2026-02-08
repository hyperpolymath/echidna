// SPDX-License-Identifier: PMPL-1.0-or-later

//! Pareto optimality for proof search
//!
//! Multi-objective optimization for proof search strategy selection:
//! - Objectives: proof time, confidence level, resource usage, proof size
//! - When portfolio solving, rank results by Pareto dominance
//! - Present Pareto frontier to user

use serde::{Deserialize, Serialize};

use super::confidence::TrustLevel;

/// Objectives for multi-objective proof search optimization
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofObjective {
    /// Proof time in milliseconds
    pub proof_time_ms: u64,
    /// Confidence level (1-5)
    pub trust_level: TrustLevel,
    /// Resource usage (memory in bytes)
    pub memory_bytes: u64,
    /// Proof size (number of steps)
    pub proof_steps: usize,
}

/// A proof candidate with its objectives
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofCandidate {
    /// Identifier for the candidate (e.g. prover name + config)
    pub id: String,
    /// The objectives achieved by this candidate
    pub objectives: ProofObjective,
    /// Whether this candidate is on the Pareto frontier
    pub is_pareto_optimal: bool,
}

/// Pareto frontier computation for proof search results
pub struct ParetoFrontier;

impl ParetoFrontier {
    /// Compute the Pareto frontier from a set of proof candidates.
    ///
    /// A candidate is Pareto-optimal if no other candidate is strictly better
    /// on ALL objectives simultaneously. "Better" means:
    /// - Lower proof_time_ms
    /// - Higher trust_level
    /// - Lower memory_bytes
    /// - Fewer proof_steps
    pub fn compute(candidates: &mut [ProofCandidate]) -> Vec<usize> {
        let n = candidates.len();
        let mut frontier_indices = Vec::new();

        for i in 0..n {
            let mut dominated = false;
            for j in 0..n {
                if i == j {
                    continue;
                }
                if Self::dominates(&candidates[j].objectives, &candidates[i].objectives) {
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

    /// Check if objective `a` dominates `b` (a is at least as good on all, strictly better on at least one)
    fn dominates(a: &ProofObjective, b: &ProofObjective) -> bool {
        let a_trust = a.trust_level.value();
        let b_trust = b.trust_level.value();

        // a must be at least as good on ALL objectives
        let at_least_as_good = a.proof_time_ms <= b.proof_time_ms
            && a_trust >= b_trust
            && a.memory_bytes <= b.memory_bytes
            && a.proof_steps <= b.proof_steps;

        if !at_least_as_good {
            return false;
        }

        // a must be strictly better on at least one
        a.proof_time_ms < b.proof_time_ms
            || a_trust > b_trust
            || a.memory_bytes < b.memory_bytes
            || a.proof_steps < b.proof_steps
    }

    /// Rank candidates by a weighted score (for when user wants a single "best")
    pub fn weighted_rank(
        candidates: &[ProofCandidate],
        weight_time: f64,
        weight_trust: f64,
        weight_memory: f64,
        weight_steps: f64,
    ) -> Vec<(usize, f64)> {
        let mut scored: Vec<(usize, f64)> = candidates
            .iter()
            .enumerate()
            .map(|(i, c)| {
                // Normalize: lower is better for time/memory/steps, higher is better for trust
                // Use inverse for "lower is better" metrics
                let time_score = if c.objectives.proof_time_ms > 0 {
                    1.0 / (c.objectives.proof_time_ms as f64)
                } else {
                    1.0
                };
                let trust_score = c.objectives.trust_level.value() as f64 / 5.0;
                let memory_score = if c.objectives.memory_bytes > 0 {
                    1.0 / (c.objectives.memory_bytes as f64 / (1024.0 * 1024.0))
                } else {
                    1.0
                };
                let steps_score = if c.objectives.proof_steps > 0 {
                    1.0 / (c.objectives.proof_steps as f64)
                } else {
                    1.0
                };

                let score = weight_time * time_score
                    + weight_trust * trust_score
                    + weight_memory * memory_score
                    + weight_steps * steps_score;

                (i, score)
            })
            .collect();

        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        scored
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_candidate(id: &str, time: u64, trust: TrustLevel, mem: u64, steps: usize) -> ProofCandidate {
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
        let mut candidates = vec![
            make_candidate("lean", 1000, TrustLevel::Level4, 512_000, 50),
        ];

        let frontier = ParetoFrontier::compute(&mut candidates);
        assert_eq!(frontier.len(), 1);
        assert!(candidates[0].is_pareto_optimal);
    }

    #[test]
    fn test_dominated_candidate_excluded() {
        let mut candidates = vec![
            // Fast but low trust
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            // Slower but dominated by z3 on all axes (worse on everything)
            make_candidate("slow_z3", 200, TrustLevel::Level1, 200_000, 20),
        ];

        let frontier = ParetoFrontier::compute(&mut candidates);
        assert_eq!(frontier.len(), 1);
        assert!(candidates[0].is_pareto_optimal);
        assert!(!candidates[1].is_pareto_optimal);
    }

    #[test]
    fn test_tradeoff_candidates_both_on_frontier() {
        let mut candidates = vec![
            // Fast but low trust
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            // Slow but high trust
            make_candidate("lean", 5000, TrustLevel::Level5, 500_000, 100),
        ];

        let frontier = ParetoFrontier::compute(&mut candidates);
        // Both should be on the frontier (neither dominates the other)
        assert_eq!(frontier.len(), 2);
        assert!(candidates[0].is_pareto_optimal);
        assert!(candidates[1].is_pareto_optimal);
    }

    #[test]
    fn test_three_way_frontier() {
        let mut candidates = vec![
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            make_candidate("lean", 5000, TrustLevel::Level5, 500_000, 100),
            make_candidate("coq", 3000, TrustLevel::Level4, 300_000, 80),
            // This one is dominated by coq (worse on all axes)
            make_candidate("slow_coq", 4000, TrustLevel::Level3, 400_000, 90),
        ];

        let frontier = ParetoFrontier::compute(&mut candidates);
        assert_eq!(frontier.len(), 3);
        assert!(candidates[0].is_pareto_optimal); // z3
        assert!(candidates[1].is_pareto_optimal); // lean
        assert!(candidates[2].is_pareto_optimal); // coq
        assert!(!candidates[3].is_pareto_optimal); // slow_coq dominated
    }

    #[test]
    fn test_weighted_rank() {
        let candidates = vec![
            make_candidate("z3", 100, TrustLevel::Level2, 100_000, 10),
            make_candidate("lean", 5000, TrustLevel::Level5, 500_000, 100),
        ];

        // Weight trust heavily
        let ranked = ParetoFrontier::weighted_rank(&candidates, 0.1, 10.0, 0.1, 0.1);
        // Lean should rank higher when trust is weighted heavily
        assert_eq!(ranked[0].0, 1); // lean index
    }

    #[test]
    fn test_empty_candidates() {
        let mut candidates: Vec<ProofCandidate> = vec![];
        let frontier = ParetoFrontier::compute(&mut candidates);
        assert!(frontier.is_empty());
    }
}
