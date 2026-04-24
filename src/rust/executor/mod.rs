// SPDX-License-Identifier: PMPL-1.0-or-later

//! Solver execution and sandboxing module
//!
//! Runs solver binaries in sandboxed environments using Podman (preferred)
//! or bubblewrap (fallback) to prevent untrusted solver code from accessing
//! the host system.

pub mod bounded;
pub mod sandbox;

pub use bounded::{bounded_command_output, BoundedOutput, MAX_PROVER_OUTPUT_BYTES};
pub use sandbox::{SandboxConfig, SandboxKind, SandboxedExecutor};
