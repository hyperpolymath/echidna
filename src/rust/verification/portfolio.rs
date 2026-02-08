// SPDX-License-Identifier: PMPL-1.0-or-later

//! SMT Solver Cross-Checking (Portfolio Solving)
//!
//! For critical proofs, submits to multiple solvers in parallel and compares
//! results. If solvers disagree, the proof is flagged for human review.

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use crate::provers::ProverKind;

/// Confidence level from portfolio solving
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PortfolioConfidence {
    /// Both/all solvers agree
    CrossChecked,
    /// Only one solver completed successfully
    SingleSolver,
    /// Solvers disagreed -- needs human review
    Inconclusive,
    /// All solvers timed out
    AllTimedOut,
}

/// Result from a single solver in the portfolio
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverResult {
    /// Which prover produced this result
    pub prover: ProverKind,
    /// Whether the proof was verified (None if timed out)
    pub verified: Option<bool>,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Whether a proof certificate was produced
    pub has_certificate: bool,
    /// Error message if the solver failed
    pub error: Option<String>,
}

/// Combined result from portfolio solving
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PortfolioResult {
    /// Overall verification result (None if inconclusive)
    pub verified: Option<bool>,
    /// Confidence level
    pub confidence: PortfolioConfidence,
    /// Individual solver results
    pub solver_results: Vec<SolverResult>,
    /// Solvers that agreed on the result
    pub agreeing_solvers: Vec<ProverKind>,
    /// Solvers that disagreed
    pub disagreeing_solvers: Vec<ProverKind>,
    /// Whether human review is needed
    pub needs_review: bool,
}

/// Configuration for portfolio solving
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PortfolioConfig {
    /// Enable cross-checking
    pub enabled: bool,
    /// Solvers to use for SMT problems
    pub smt_solvers: Vec<ProverKind>,
    /// Solvers to use for first-order ATP problems
    pub atp_solvers: Vec<ProverKind>,
    /// Solvers to use for interactive theorem prover problems
    pub itp_solvers: Vec<ProverKind>,
    /// Timeout per solver (seconds)
    pub solver_timeout: u64,
    /// Wait factor for slower solver (e.g. 2.0 means wait 2x the faster result)
    pub wait_factor: f64,
    /// Minimum complexity threshold to trigger cross-checking
    pub complexity_threshold: u32,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        Self {
            enabled: false, // Disabled by default for speed
            smt_solvers: vec![ProverKind::Z3, ProverKind::CVC5, ProverKind::AltErgo],
            atp_solvers: vec![ProverKind::Vampire, ProverKind::EProver],
            itp_solvers: vec![ProverKind::Lean, ProverKind::Coq],
            solver_timeout: 300,
            wait_factor: 2.0,
            complexity_threshold: 5,
        }
    }
}

/// Portfolio solver that runs multiple provers in parallel
pub struct PortfolioSolver {
    config: PortfolioConfig,
}

impl PortfolioSolver {
    /// Create a new portfolio solver
    pub fn new(config: PortfolioConfig) -> Self {
        Self { config }
    }

    /// Create with default configuration
    pub fn with_defaults() -> Self {
        Self::new(PortfolioConfig::default())
    }

    /// Reconcile results from multiple solvers
    pub fn reconcile(&self, results: &[SolverResult]) -> PortfolioResult {
        let completed: Vec<&SolverResult> = results.iter()
            .filter(|r| r.verified.is_some())
            .collect();

        let timed_out: Vec<&SolverResult> = results.iter()
            .filter(|r| r.verified.is_none())
            .collect();

        // All timed out
        if completed.is_empty() {
            return PortfolioResult {
                verified: None,
                confidence: PortfolioConfidence::AllTimedOut,
                solver_results: results.to_vec(),
                agreeing_solvers: vec![],
                disagreeing_solvers: vec![],
                needs_review: true,
            };
        }

        // Check agreement
        let first_result = completed[0].verified.unwrap();
        let mut agreeing = vec![completed[0].prover];
        let mut disagreeing = vec![];

        for result in &completed[1..] {
            if result.verified.unwrap() == first_result {
                agreeing.push(result.prover);
            } else {
                disagreeing.push(result.prover);
            }
        }

        // Determine confidence
        let (verified, confidence, needs_review) = if disagreeing.is_empty() {
            if completed.len() >= 2 {
                // All agree, cross-checked
                (Some(first_result), PortfolioConfidence::CrossChecked, false)
            } else {
                // Only one solver completed
                (Some(first_result), PortfolioConfidence::SingleSolver, false)
            }
        } else {
            // Disagreement -- flag for human review
            (None, PortfolioConfidence::Inconclusive, true)
        };

        PortfolioResult {
            verified,
            confidence,
            solver_results: results.to_vec(),
            agreeing_solvers: agreeing,
            disagreeing_solvers: disagreeing,
            needs_review,
        }
    }

    /// Get the appropriate solvers for a given proof type
    pub fn solvers_for_kind(&self, kind: ProverKind) -> &[ProverKind] {
        match kind {
            ProverKind::Z3 | ProverKind::CVC5 | ProverKind::AltErgo => &self.config.smt_solvers,
            ProverKind::Vampire | ProverKind::EProver | ProverKind::SPASS => &self.config.atp_solvers,
            ProverKind::Lean | ProverKind::Coq | ProverKind::Agda
            | ProverKind::Isabelle | ProverKind::Idris2 => &self.config.itp_solvers,
            _ => &self.config.smt_solvers, // Default
        }
    }

    /// Check if cross-checking is enabled
    pub fn is_enabled(&self) -> bool {
        self.config.enabled
    }

    /// Get the solver timeout
    pub fn timeout(&self) -> Duration {
        Duration::from_secs(self.config.solver_timeout)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_both_solvers_agree_sat() {
        let solver = PortfolioSolver::with_defaults();

        let results = vec![
            SolverResult {
                prover: ProverKind::Z3,
                verified: Some(true),
                time_ms: 100,
                has_certificate: false,
                error: None,
            },
            SolverResult {
                prover: ProverKind::CVC5,
                verified: Some(true),
                time_ms: 150,
                has_certificate: true,
                error: None,
            },
        ];

        let portfolio = solver.reconcile(&results);

        assert_eq!(portfolio.verified, Some(true));
        assert_eq!(portfolio.confidence, PortfolioConfidence::CrossChecked);
        assert!(!portfolio.needs_review);
        assert_eq!(portfolio.agreeing_solvers.len(), 2);
        assert!(portfolio.disagreeing_solvers.is_empty());
    }

    #[test]
    fn test_solvers_disagree() {
        let solver = PortfolioSolver::with_defaults();

        let results = vec![
            SolverResult {
                prover: ProverKind::Z3,
                verified: Some(true),
                time_ms: 100,
                has_certificate: false,
                error: None,
            },
            SolverResult {
                prover: ProverKind::CVC5,
                verified: Some(false),
                time_ms: 200,
                has_certificate: false,
                error: None,
            },
        ];

        let portfolio = solver.reconcile(&results);

        assert_eq!(portfolio.verified, None);
        assert_eq!(portfolio.confidence, PortfolioConfidence::Inconclusive);
        assert!(portfolio.needs_review);
    }

    #[test]
    fn test_one_solver_timeout() {
        let solver = PortfolioSolver::with_defaults();

        let results = vec![
            SolverResult {
                prover: ProverKind::Z3,
                verified: Some(true),
                time_ms: 100,
                has_certificate: false,
                error: None,
            },
            SolverResult {
                prover: ProverKind::CVC5,
                verified: None, // Timed out
                time_ms: 300000,
                has_certificate: false,
                error: Some("Timeout".to_string()),
            },
        ];

        let portfolio = solver.reconcile(&results);

        assert_eq!(portfolio.verified, Some(true));
        assert_eq!(portfolio.confidence, PortfolioConfidence::SingleSolver);
    }

    #[test]
    fn test_all_solvers_timeout() {
        let solver = PortfolioSolver::with_defaults();

        let results = vec![
            SolverResult {
                prover: ProverKind::Z3,
                verified: None,
                time_ms: 300000,
                has_certificate: false,
                error: Some("Timeout".to_string()),
            },
            SolverResult {
                prover: ProverKind::CVC5,
                verified: None,
                time_ms: 300000,
                has_certificate: false,
                error: Some("Timeout".to_string()),
            },
        ];

        let portfolio = solver.reconcile(&results);

        assert_eq!(portfolio.verified, None);
        assert_eq!(portfolio.confidence, PortfolioConfidence::AllTimedOut);
        assert!(portfolio.needs_review);
    }
}
