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

pub mod portfolio;
pub mod certificates;
pub mod axiom_tracker;
pub mod confidence;
pub mod mutation;
pub mod pareto;
pub mod statistics;

pub use confidence::TrustLevel;
pub use portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver};
pub use certificates::{CertificateFormat, CertificateVerifier, ProofCertificate};
pub use axiom_tracker::{AxiomPolicy, AxiomTracker, AxiomUsage, DangerLevel};
pub use mutation::{MutationKind, MutationResult, MutationTester};
pub use pareto::{ParetoFrontier, ProofObjective, ProofCandidate};
pub use statistics::StatisticsTracker;
