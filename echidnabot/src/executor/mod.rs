// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Secure execution environment for prover verification

pub mod container;

pub use container::{ExecutionResult, IsolationBackend, PodmanExecutor};
