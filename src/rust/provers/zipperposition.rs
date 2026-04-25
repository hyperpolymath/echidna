// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Zipperposition Backend
//!
//! Zipperposition is a higher-order and first-order automated theorem prover
//! for the TPTP/TSTP format. Supports full TPTP syntax with superposition,
//! resolution, and unification.
//!
//! Input format: TPTP `.p` files (problem statements with FOL + HOL).
//! Executable: `zipperposition` with `--input tptp` flag.

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// Zipperposition ATP backend
pub struct ZipperpositionBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl ZipperpositionBackend {
    /// Create a new Zipperposition backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        ZipperpositionBackend { config }
    }

    /// Parse Zipperposition output to determine success or failure
    ///
    /// "SZS status Theorem" → success; "CounterSatisfiable", "Satisfiable", or "Unknown" → failure.
    fn parse_result(&self, output: &str) -> Result<bool> {
        for line in output.lines() {
            let trimmed = line.trim();

            // Success
            if trimmed.contains("SZS status Theorem") {
                return Ok(true);
            }

            // Failure
            if trimmed.contains("SZS status CounterSatisfiable")
                || trimmed.contains("SZS status Satisfiable")
                || trimmed.contains("SZS status Unknown")
            {
                return Ok(false);
            }
        }

        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for ZipperpositionBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Zipperposition
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Zipperposition version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_zipperposition.p";
        tokio::fs::write(temp_path, content).await?;
        Ok(ProofState {
            goals: vec![],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        })
    }

    async fn apply_tactic(
        &self,
        _state: &ProofState,
        _tactic: &Tactic,
    ) -> Result<TacticResult> {
        Ok(TacticResult::Error(
            "Tactic application not supported for Zipperposition".to_string(),
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.proof_script.is_empty() {
            return Ok(false);
        }
        let content = state
            .proof_script
            .iter()
            .map(|t| format!("{:?}", t))
            .collect::<Vec<_>>()
            .join("\n");
        let temp_path = "/tmp/echidna_zipperposition.p";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("--input")
            .arg("tptp")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run Zipperposition")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let combined = format!("{}\n{}", stdout, stderr);

        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .goals
            .iter()
            .map(|g| format!("{}", g.target))
            .collect::<Vec<_>>()
            .join("\n"))
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zipperposition_backend_creation() {
        let config = ProverConfig::default();
        let backend = ZipperpositionBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Zipperposition);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = ZipperpositionBackend::new(config);
        let output = "% SZS status Theorem\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_unknown() {
        let config = ProverConfig::default();
        let backend = ZipperpositionBackend::new(config);
        let output = "% SZS status Unknown\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
