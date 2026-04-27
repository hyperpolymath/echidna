// SPDX-License-Identifier: PMPL-1.0-or-later

//! Verification subsystem for ECHIDNA
//!
//! Implements trust-hardening features:
//! - Portfolio solving (cross-checking multiple solvers)
//! - Proof certificate checking (Alethe, DRAT/LRAT)
//! - Axiom usage tracking
//! - Confidence scoring (5-level trust hierarchy)
//! - Mutation testing for specifications
//! - Pareto optimality for proof search

pub mod axiom_tracker;
pub mod certificates;
pub mod confidence;
pub mod mutation;
pub mod pareto;
pub mod portfolio;
#[cfg(feature = "verisim")]
pub mod proof;
pub mod statistics;

pub use axiom_tracker::{AxiomPolicy, AxiomTracker, AxiomUsage, DangerLevel};
pub use certificates::{CertificateFormat, CertificateVerifier, ProofCertificate};
pub use confidence::TrustLevel;
pub use mutation::{MutationKind, MutationResult, MutationTester};
pub use pareto::{ParetoFrontier, ProofCandidate, ProofObjective};
pub use portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver};
#[cfg(feature = "verisim")]
pub use proof::{
    theorem_identity, Proof, ProofStateRecord, ProofVersion, TacticApplication, TacticStatus,
};
pub use statistics::{StatsSummaryRecord, StatisticsTracker};
