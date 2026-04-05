// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! ECHIDNA Trust Bridge
//!
//! Connects echidnabot to ECHIDNA's trust verification mechanisms:
//!
//! 1. **Proof Confidence Levels** (1-5): quantify trust in verification results
//! 2. **Solver Integrity Verification**: check that solver binaries are untampered
//! 3. **Axiom Usage Tracking**: detect sorry, Admitted, postulate, etc.
//!
//! Confidence levels:
//! - Level 5: Cross-checked by 2+ independent small-kernel systems
//! - Level 4: Small-kernel system (Lean4, Coq, Isabelle) with proof certificate
//! - Level 3: Single prover with proof certificate (Alethe, DRAT/LRAT)
//! - Level 2: Single prover result without certificate
//! - Level 1: Large-TCB system or unchecked result

pub mod axiom_tracker;
pub mod confidence;
pub mod migration_scanner;
pub mod solver_integrity;

pub use axiom_tracker::{AxiomFlag, AxiomReport, AxiomTracker};
pub use confidence::{ConfidenceLevel, ConfidenceReport};
pub use migration_scanner::{MigrationScanReport, MigrationScanner, MigrationSeverity};
pub use solver_integrity::{IntegrityReport, IntegrityStatus, SolverIntegrity};
