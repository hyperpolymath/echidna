// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! echidnabot - Proof-aware CI bot for theorem prover repositories
//!
//! This crate provides the core functionality for monitoring code repositories
//! containing formal proofs and delegating verification to ECHIDNA Core.
//!
//! # Architecture
//!
//! ```text
//! GitHub/GitLab → Webhooks → echidnabot → ECHIDNA Core → Results → Check Runs
//! ```
//!
//! See `docs/ARCHITECTURE.adoc` for the full design document.

pub mod api;
pub mod adapters;
pub mod config;
pub mod dispatcher;
pub mod error;
pub mod executor; // Container isolation for secure prover execution
pub mod fleet; // gitbot-fleet coordination layer
pub mod modes; // Bot operating modes (Verifier/Advisor/Consultant/Regulator)
pub mod result_formatter; // Bridge between dispatcher results and bot modes
pub mod scheduler;
pub mod store;
pub mod trust; // ECHIDNA Trust Bridge (confidence, integrity, axiom tracking)

pub use config::Config;
pub use error::{Error, Result};

/// Re-export commonly used types
pub mod prelude {
    pub use crate::config::Config;
    pub use crate::error::{Error, Result};
    pub use crate::scheduler::JobScheduler;
    pub use crate::store::Store;
}
