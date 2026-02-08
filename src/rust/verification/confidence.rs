// SPDX-License-Identifier: PMPL-1.0-or-later

//! 5-Level Trust Hierarchy for proof confidence scoring
//!
//! Assigns a trust level to each proof result based on:
//! - Number of independent provers that confirmed it
//! - Whether proof certificates were produced and verified
//! - Whether the prover has a small trusted kernel
//! - Whether dangerous axioms were used
//! - Whether solver binaries passed integrity checks

use serde::{Deserialize, Serialize};

use crate::provers::ProverKind;
use super::axiom_tracker::DangerLevel;
use super::portfolio::PortfolioConfidence;

/// Trust level for a proof result (5-level hierarchy)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TrustLevel {
    /// Large-TCB system, unchecked result, or uses dangerous axioms
    Level1 = 1,
    /// Single prover result without certificate, but no dangerous axioms
    Level2 = 2,
    /// Single prover with proof certificate (Alethe, DRAT/LRAT)
    Level3 = 3,
    /// Checked by small-kernel system (Lean4, Coq, Isabelle) with proof certificate
    Level4 = 4,
    /// Cross-checked by 2+ independent small-kernel systems with certificates
    Level5 = 5,
}

impl TrustLevel {
    /// Human-readable description
    pub fn description(&self) -> &str {
        match self {
            TrustLevel::Level1 => "Minimal trust: large-TCB, unchecked, or dangerous axioms",
            TrustLevel::Level2 => "Basic trust: single prover, no dangerous axioms",
            TrustLevel::Level3 => "Moderate trust: single prover with proof certificate",
            TrustLevel::Level4 => "High trust: small-kernel prover with certificate",
            TrustLevel::Level5 => "Maximum trust: cross-checked by 2+ small-kernel systems",
        }
    }

    /// Numeric value (1-5)
    pub fn value(&self) -> u8 {
        *self as u8
    }
}

impl std::fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Level {} ({})", self.value(), self.description())
    }
}

/// Input factors for computing trust level
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustFactors {
    /// Which prover produced the result
    pub prover: ProverKind,
    /// Number of independent provers that agree
    pub confirming_provers: u32,
    /// Whether a proof certificate was produced
    pub has_certificate: bool,
    /// Whether the certificate was independently verified
    pub certificate_verified: bool,
    /// Worst axiom danger level found
    pub worst_axiom_danger: DangerLevel,
    /// Whether the solver binary passed integrity check
    pub solver_integrity_ok: bool,
    /// Portfolio solving confidence (if used)
    pub portfolio_confidence: Option<PortfolioConfidence>,
}

/// Compute the trust level for a proof result
pub fn compute_trust_level(factors: &TrustFactors) -> TrustLevel {
    // Reject-level axioms always result in Level 1
    if factors.worst_axiom_danger == DangerLevel::Reject {
        return TrustLevel::Level1;
    }

    // Warning-level axioms cap at Level 1
    if factors.worst_axiom_danger == DangerLevel::Warning {
        return TrustLevel::Level1;
    }

    // Failed integrity check caps at Level 1
    if !factors.solver_integrity_ok {
        return TrustLevel::Level1;
    }

    let is_small_kernel = is_small_kernel_prover(factors.prover);

    // Level 5: Cross-checked by 2+ small-kernel systems with certificates
    if factors.confirming_provers >= 2
        && factors.certificate_verified
        && is_small_kernel
    {
        return TrustLevel::Level5;
    }

    // Level 4: Small-kernel prover with verified certificate
    if is_small_kernel && factors.certificate_verified {
        return TrustLevel::Level4;
    }

    // Level 3: Any prover with verified certificate
    if factors.has_certificate && factors.certificate_verified {
        return TrustLevel::Level3;
    }

    // Level 3: Cross-checked without certificate
    if factors.confirming_provers >= 2 {
        return TrustLevel::Level3;
    }

    // Level 2: Single prover, no dangerous axioms (already checked above)
    TrustLevel::Level2
}

/// Whether a prover has a small trusted computing base (kernel)
pub fn is_small_kernel_prover(prover: ProverKind) -> bool {
    matches!(
        prover,
        ProverKind::Lean
            | ProverKind::Coq
            | ProverKind::Isabelle
            | ProverKind::Agda
            | ProverKind::Metamath
            | ProverKind::HOLLight
            | ProverKind::HOL4
            | ProverKind::Idris2
            | ProverKind::FStar
            | ProverKind::Twelf
            | ProverKind::Nuprl
            | ProverKind::Minlog
    )
}

/// Get the default trust level for a given prover (without certificates)
pub fn default_trust_for_prover(prover: ProverKind) -> TrustLevel {
    if is_small_kernel_prover(prover) {
        TrustLevel::Level2
    } else {
        TrustLevel::Level2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_factors(prover: ProverKind) -> TrustFactors {
        TrustFactors {
            prover,
            confirming_provers: 1,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: None,
        }
    }

    #[test]
    fn test_cross_checked_with_certs_level5() {
        let factors = TrustFactors {
            prover: ProverKind::Lean,
            confirming_provers: 2,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: Some(PortfolioConfidence::CrossChecked),
        };

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level5);
    }

    #[test]
    fn test_lean_with_cert_level4() {
        let factors = TrustFactors {
            prover: ProverKind::Lean,
            confirming_provers: 1,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: None,
        };

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level4);
    }

    #[test]
    fn test_cvc5_with_alethe_level3() {
        let factors = TrustFactors {
            prover: ProverKind::CVC5,
            confirming_provers: 1,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: None,
        };

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level3);
    }

    #[test]
    fn test_z3_without_cert_level2() {
        let factors = make_factors(ProverKind::Z3);
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level2);
    }

    #[test]
    fn test_sorry_downgrades_to_level1() {
        let mut factors = make_factors(ProverKind::Lean);
        factors.worst_axiom_danger = DangerLevel::Warning;

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level1);
    }

    #[test]
    fn test_rejected_axiom_level1() {
        let mut factors = make_factors(ProverKind::Agda);
        factors.worst_axiom_danger = DangerLevel::Reject;
        factors.has_certificate = true;
        factors.certificate_verified = true;
        factors.confirming_provers = 3;

        // Even with certificates and cross-checking, rejected axioms cap at Level 1
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level1);
    }

    #[test]
    fn test_failed_integrity_level1() {
        let mut factors = make_factors(ProverKind::Lean);
        factors.solver_integrity_ok = false;
        factors.has_certificate = true;
        factors.certificate_verified = true;

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level1);
    }

    #[test]
    fn test_trust_level_ordering() {
        assert!(TrustLevel::Level5 > TrustLevel::Level4);
        assert!(TrustLevel::Level4 > TrustLevel::Level3);
        assert!(TrustLevel::Level3 > TrustLevel::Level2);
        assert!(TrustLevel::Level2 > TrustLevel::Level1);
    }

    #[test]
    fn test_small_kernel_detection() {
        assert!(is_small_kernel_prover(ProverKind::Lean));
        assert!(is_small_kernel_prover(ProverKind::Coq));
        assert!(is_small_kernel_prover(ProverKind::Isabelle));
        assert!(!is_small_kernel_prover(ProverKind::Z3));
        assert!(!is_small_kernel_prover(ProverKind::CVC5));
        assert!(!is_small_kernel_prover(ProverKind::Vampire));
    }
}
