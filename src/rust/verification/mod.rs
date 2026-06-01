// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Verification subsystem for ECHIDNA
//!
//! Implements trust-hardening features:
//! - Portfolio solving (cross-checking multiple solvers)
//! - Proof certificate checking (Alethe, DRAT/LRAT)
//! - Axiom usage tracking
//! - Confidence scoring (5-level trust hierarchy)
//! - Mutation testing for specifications
//! - Pareto optimality for proof search
//!
//! ## Arbitration stack (4 mechanisms, post-saturation 2026-06-01)
//!
//! Existing:
//! - `portfolio` — majority-vote + flagging when k provers agree
//!
//! Added in the saturation campaign (see
//! `docs/decisions/2026-06-01-saturation-campaign.md`):
//! - `bayesian_arbiter` — log-odds posterior with per-prover calibrated
//!   likelihoods; reports Shannon entropy.
//! - `dempster_shafer` — belief-mass combination via Dempster's rule;
//!   trips `HighConflict` when normalised conflict mass k > 0.95.
//! - `pareto_arbiter` — multi-objective Pareto frontier over
//!   (confidence↑, latency↓, axiom_cost↓, certificate_size↓) with
//!   pluggable tiebreak.
//!
//! Picking between them: see the "Guide: Picking an arbitration
//! mechanism" entry in `docs/wiki/Guides.md`.

pub mod axiom_tracker;
pub mod certificates;
pub mod confidence;
pub mod mutation;
pub mod pareto;
pub mod portfolio;
#[cfg(feature = "verisim")]
pub mod proof;
pub mod statistics;
pub mod bayesian_arbiter;
pub mod dempster_shafer;
pub mod pareto_arbiter;

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
pub use statistics::{StatisticsTracker, StatsSummaryRecord};
