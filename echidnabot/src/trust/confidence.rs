// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Proof confidence level assessment
//!
//! Maps ECHIDNA verification results to a 5-level trust scale based on:
//! - Prover kernel size (small-kernel = higher trust)
//! - Number of independent checkers used
//! - Presence of proof certificates
//! - Prover tier within ECHIDNA

use serde::{Deserialize, Serialize};

use crate::dispatcher::{ProofStatus, ProverKind};

/// Confidence level for a proof verification result.
///
/// Higher levels indicate stronger trust in the result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ConfidenceLevel {
    /// Large-TCB system or unchecked result
    Level1 = 1,
    /// Single prover result without certificate
    Level2 = 2,
    /// Single prover with proof certificate (Alethe, DRAT/LRAT)
    Level3 = 3,
    /// Checked by small-kernel system (Lean4, Coq, Isabelle) with certificate
    Level4 = 4,
    /// Cross-checked by 2+ independent small-kernel systems
    Level5 = 5,
}

impl ConfidenceLevel {
    /// Numeric value (1-5)
    pub fn value(&self) -> u8 {
        *self as u8
    }

    /// Human-readable label
    pub fn label(&self) -> &'static str {
        match self {
            Self::Level1 => "Minimal (large-TCB / unchecked)",
            Self::Level2 => "Low (single prover, no certificate)",
            Self::Level3 => "Moderate (single prover + certificate)",
            Self::Level4 => "High (small-kernel + certificate)",
            Self::Level5 => "Maximum (cross-checked by 2+ systems)",
        }
    }

    /// Whether this confidence level is considered sufficient for production use
    pub fn is_production_ready(&self) -> bool {
        *self >= ConfidenceLevel::Level3
    }
}

impl std::fmt::Display for ConfidenceLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Level {} ({})", self.value(), self.label())
    }
}

/// Report assessing confidence in a proof result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfidenceReport {
    /// The assessed confidence level
    pub level: ConfidenceLevel,
    /// The prover that produced the result
    pub prover: ProverKind,
    /// Whether a proof certificate was present
    pub has_certificate: bool,
    /// Number of independent checkers that verified the result
    pub checker_count: usize,
    /// Whether the prover uses a small kernel
    pub small_kernel: bool,
    /// Human-readable justification for the confidence level
    pub justification: String,
}

/// Assess the confidence level of a proof verification result.
///
/// # Arguments
/// * `prover` - Which prover produced the result
/// * `status` - The verification status
/// * `has_certificate` - Whether a proof certificate (Alethe, DRAT/LRAT, etc.) was provided
/// * `checker_count` - Number of independent checkers that confirmed the result
pub fn assess_confidence(
    prover: ProverKind,
    status: ProofStatus,
    has_certificate: bool,
    checker_count: usize,
) -> ConfidenceReport {
    // Only verified proofs get meaningful confidence levels
    if status != ProofStatus::Verified {
        return ConfidenceReport {
            level: ConfidenceLevel::Level1,
            prover,
            has_certificate: false,
            checker_count: 0,
            small_kernel: is_small_kernel(prover),
            justification: format!(
                "Proof status is {:?} (not Verified) -- confidence is minimal",
                status
            ),
        };
    }

    let small_kernel = is_small_kernel(prover);

    // Level 5: Cross-checked by 2+ independent small-kernel systems
    if checker_count >= 2 && small_kernel {
        return ConfidenceReport {
            level: ConfidenceLevel::Level5,
            prover,
            has_certificate,
            checker_count,
            small_kernel,
            justification: format!(
                "Cross-checked by {} independent small-kernel systems ({})",
                checker_count,
                prover.display_name()
            ),
        };
    }

    // Level 4: Small-kernel system with certificate
    if small_kernel && has_certificate {
        return ConfidenceReport {
            level: ConfidenceLevel::Level4,
            prover,
            has_certificate,
            checker_count,
            small_kernel,
            justification: format!(
                "Verified by small-kernel system ({}) with proof certificate",
                prover.display_name()
            ),
        };
    }

    // Level 3: Single prover with proof certificate (e.g., Z3 with DRAT/LRAT)
    if has_certificate {
        return ConfidenceReport {
            level: ConfidenceLevel::Level3,
            prover,
            has_certificate,
            checker_count,
            small_kernel,
            justification: format!(
                "Verified by {} with proof certificate",
                prover.display_name()
            ),
        };
    }

    // Level 2: Single prover without certificate but with small kernel
    if small_kernel {
        return ConfidenceReport {
            level: ConfidenceLevel::Level2,
            prover,
            has_certificate,
            checker_count,
            small_kernel,
            justification: format!(
                "Verified by small-kernel system ({}) without proof certificate",
                prover.display_name()
            ),
        };
    }

    // Level 1: Large-TCB or stub prover
    ConfidenceReport {
        level: ConfidenceLevel::Level1,
        prover,
        has_certificate: false,
        checker_count,
        small_kernel: false,
        justification: format!(
            "Verified by large-TCB system ({}) -- consider cross-checking",
            prover.display_name()
        ),
    }
}

/// Determine if a prover uses a small, trusted kernel.
///
/// Small-kernel provers have a minimal trusted code base for proof checking,
/// making their results more trustworthy.
pub fn is_small_kernel(prover: ProverKind) -> bool {
    match prover {
        // Tier 1 small-kernel systems
        ProverKind::Coq => true,      // Gallina kernel
        ProverKind::Lean => true,      // Lean4 kernel
        ProverKind::Isabelle => true,  // Isabelle/Pure kernel
        ProverKind::Agda => true,      // Dependent type checker
        ProverKind::Metamath => true,  // Extremely small kernel

        // SAT/SMT solvers -- large TCB but produce certificates
        ProverKind::Z3 => false,
        ProverKind::Cvc5 => false,

        // Other provers
        ProverKind::HolLight => true,  // Small OCaml kernel
        ProverKind::Mizar => false,    // Large checker
        ProverKind::Pvs => false,      // Large TCB
        ProverKind::Acl2 => false,     // Built on Common Lisp
        ProverKind::Hol4 => true,      // Small ML kernel
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_confidence_level_ordering() {
        assert!(ConfidenceLevel::Level5 > ConfidenceLevel::Level4);
        assert!(ConfidenceLevel::Level4 > ConfidenceLevel::Level3);
        assert!(ConfidenceLevel::Level3 > ConfidenceLevel::Level2);
        assert!(ConfidenceLevel::Level2 > ConfidenceLevel::Level1);
    }

    #[test]
    fn test_confidence_level_values() {
        assert_eq!(ConfidenceLevel::Level1.value(), 1);
        assert_eq!(ConfidenceLevel::Level5.value(), 5);
    }

    #[test]
    fn test_production_readiness() {
        assert!(!ConfidenceLevel::Level1.is_production_ready());
        assert!(!ConfidenceLevel::Level2.is_production_ready());
        assert!(ConfidenceLevel::Level3.is_production_ready());
        assert!(ConfidenceLevel::Level4.is_production_ready());
        assert!(ConfidenceLevel::Level5.is_production_ready());
    }

    #[test]
    fn test_small_kernel_provers() {
        assert!(is_small_kernel(ProverKind::Coq));
        assert!(is_small_kernel(ProverKind::Lean));
        assert!(is_small_kernel(ProverKind::Isabelle));
        assert!(is_small_kernel(ProverKind::Agda));
        assert!(is_small_kernel(ProverKind::Metamath));
        assert!(is_small_kernel(ProverKind::HolLight));
        assert!(is_small_kernel(ProverKind::Hol4));

        assert!(!is_small_kernel(ProverKind::Z3));
        assert!(!is_small_kernel(ProverKind::Cvc5));
        assert!(!is_small_kernel(ProverKind::Mizar));
        assert!(!is_small_kernel(ProverKind::Pvs));
        assert!(!is_small_kernel(ProverKind::Acl2));
    }

    #[test]
    fn test_assess_level5_cross_checked() {
        let report = assess_confidence(
            ProverKind::Lean,
            ProofStatus::Verified,
            true,
            3, // 3 independent checkers
        );
        assert_eq!(report.level, ConfidenceLevel::Level5);
        assert!(report.small_kernel);
        assert_eq!(report.checker_count, 3);
    }

    #[test]
    fn test_assess_level4_small_kernel_with_cert() {
        let report = assess_confidence(
            ProverKind::Coq,
            ProofStatus::Verified,
            true,
            1,
        );
        assert_eq!(report.level, ConfidenceLevel::Level4);
    }

    #[test]
    fn test_assess_level3_cert_no_small_kernel() {
        let report = assess_confidence(
            ProverKind::Z3,
            ProofStatus::Verified,
            true, // Has DRAT/LRAT certificate
            1,
        );
        assert_eq!(report.level, ConfidenceLevel::Level3);
    }

    #[test]
    fn test_assess_level2_small_kernel_no_cert() {
        let report = assess_confidence(
            ProverKind::Lean,
            ProofStatus::Verified,
            false,
            1,
        );
        assert_eq!(report.level, ConfidenceLevel::Level2);
    }

    #[test]
    fn test_assess_level1_large_tcb() {
        let report = assess_confidence(
            ProverKind::Pvs,
            ProofStatus::Verified,
            false,
            1,
        );
        assert_eq!(report.level, ConfidenceLevel::Level1);
    }

    #[test]
    fn test_assess_failed_proof_always_level1() {
        let report = assess_confidence(
            ProverKind::Coq,
            ProofStatus::Failed,
            true,
            3,
        );
        assert_eq!(report.level, ConfidenceLevel::Level1);
    }

    #[test]
    fn test_confidence_display() {
        let level = ConfidenceLevel::Level4;
        let display = format!("{}", level);
        assert!(display.contains("Level 4"));
        assert!(display.contains("High"));
    }
}
