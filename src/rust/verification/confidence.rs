// SPDX-License-Identifier: MPL-2.0

//! 5-Level Trust Hierarchy for proof confidence scoring
//!
//! Assigns a trust level to each proof result based on:
//! - Number of independent provers that confirmed it
//! - Whether proof certificates were produced and verified
//! - Whether the prover has a small trusted kernel
//! - Whether dangerous axioms were used
//! - Whether solver binaries passed integrity checks

use serde::{Deserialize, Serialize};

use super::axiom_tracker::DangerLevel;
use super::portfolio::PortfolioConfidence;
use crate::provers::ProverKind;

/// Trust level for a proof result (5-level hierarchy).
///
/// There is one trust kernel: this type and [`compute_trust_level`] come
/// from `echidna-core` (`echidna_core::trust`, the Creusot-annotated crate).
/// This module keeps the `ProverKind`-shaped [`TrustFactors`] that dispatch
/// builds, and maps them onto the kernel's input.
pub use echidna_core::trust::TrustLevel;

/// Input factors for computing trust level
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustFactors {
    /// Which prover produced the result
    pub prover: ProverKind,
    /// Number of independent provers that agree
    pub confirming_provers: u32,
    /// How many of the `confirming_provers` are small-kernel systems whose
    /// certificate for this result was independently verified, the producing
    /// prover included. Level 5 needs at least two. Defaults to 0, so a
    /// caller that cannot vouch for its confirmers' kernels never reaches
    /// Level 5.
    #[serde(default)]
    pub small_kernel_confirmations: u32,
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

/// Compute the trust level for a proof result.
///
/// Delegates to the single kernel, `echidna_core::trust::compute_trust_level`,
/// after mapping the prover to its kernel class and the axiom danger level
/// to the kernel's enum. The kernel's contracts (TK-4: Level 4 and above
/// need a small kernel and a produced, verified certificate; TK-5: Level 5
/// needs two or more small-kernel confirmations) hold here because there is
/// no second implementation to drift from.
pub fn compute_trust_level(factors: &TrustFactors) -> TrustLevel {
    use echidna_core::trust::{axiom_tracker::DangerLevel as KernelDanger, ProverClass};
    let prover_class = if is_small_kernel_prover(factors.prover) {
        ProverClass::SmallKernel
    } else {
        ProverClass::Other
    };
    let worst_axiom_danger = match factors.worst_axiom_danger {
        DangerLevel::Safe => KernelDanger::Safe,
        DangerLevel::Noted => KernelDanger::Noted,
        DangerLevel::Warning => KernelDanger::Warning,
        DangerLevel::Reject => KernelDanger::Reject,
    };
    echidna_core::trust::compute_trust_level(&echidna_core::trust::TrustFactors {
        prover_class,
        confirming_provers: factors.confirming_provers,
        small_kernel_confirmations: factors.small_kernel_confirmations,
        has_certificate: factors.has_certificate,
        certificate_verified: factors.certificate_verified,
        worst_axiom_danger,
        solver_integrity_ok: factors.solver_integrity_ok,
    })
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
pub fn default_trust_for_prover(_prover: ProverKind) -> TrustLevel {
    // Small-kernel provers get Level2 by default; all others also start at Level2.
    // Trust can be elevated via certificates, cross-checking, etc.
    TrustLevel::Level2
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_factors(prover: ProverKind) -> TrustFactors {
        TrustFactors {
            prover,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
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
            small_kernel_confirmations: 2,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: Some(PortfolioConfidence::CrossChecked),
        };

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level5);
    }

    /// One small-kernel prover plus a confirmer that is not a small-kernel
    /// system with a checked certificate is not Level 5 (audit 2026-11-09).
    #[test]
    fn test_one_small_kernel_confirmation_is_not_level5() {
        let factors = TrustFactors {
            prover: ProverKind::Lean,
            confirming_provers: 2,
            small_kernel_confirmations: 1,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: Some(PortfolioConfidence::CrossChecked),
        };

        assert_eq!(compute_trust_level(&factors), TrustLevel::Level4);
    }

    /// A verified flag with no certificate produced is not Level 4
    /// (audit 2026-11-09).
    #[test]
    fn test_verified_flag_without_certificate_is_not_level4() {
        let mut factors = make_factors(ProverKind::Lean);
        factors.certificate_verified = true;
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level2);
    }

    /// The kernel's notion of a small kernel is `is_small_kernel_prover`.
    #[test]
    fn test_small_kernel_class_follows_is_small_kernel_prover() {
        for prover in [
            ProverKind::Lean,
            ProverKind::Coq,
            ProverKind::Z3,
            ProverKind::CVC5,
        ] {
            let factors = TrustFactors {
                has_certificate: true,
                certificate_verified: true,
                ..make_factors(prover)
            };
            let level4 = compute_trust_level(&factors) == TrustLevel::Level4;
            assert_eq!(level4, is_small_kernel_prover(prover), "{prover:?}");
        }
    }

    #[test]
    fn test_lean_with_cert_level4() {
        let factors = TrustFactors {
            prover: ProverKind::Lean,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
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
            small_kernel_confirmations: 0,
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
