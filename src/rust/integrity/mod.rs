// SPDX-License-Identifier: PMPL-1.0-or-later

//! Solver binary integrity verification module
//!
//! Provides SHAKE3-512 and BLAKE3 hash-based integrity verification for solver
//! binaries. On startup, each solver binary is hashed and compared against a
//! known-good manifest. If a mismatch is detected, the solver is marked as
//! untrusted and will not be used.

pub mod solver_integrity;

pub use solver_integrity::{
    IntegrityChecker, IntegrityStatus, SolverIntegrityReport, SolverManifest,
    SolverManifestEntry,
};
