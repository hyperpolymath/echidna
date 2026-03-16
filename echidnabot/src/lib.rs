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

#![forbid(unsafe_code)]
pub mod api;
pub mod adapters;
pub mod config;
pub mod dispatcher;
pub mod error;
pub mod fleet;
pub mod scheduler;
pub mod store;

pub use config::Config;
pub use error::{Error, Result};

/// Re-export commonly used types
pub mod prelude {
    pub use crate::config::Config;
    pub use crate::error::{Error, Result};
    pub use crate::scheduler::JobScheduler;
    pub use crate::store::Store;
}
