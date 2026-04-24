// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! SMT-RAT Backend
//!
//! SMT-RAT is a nonlinear arithmetic SMT solver from RWTH Aachen.
//! Supports QF_NIA, QF_NRA, QF_LRA, and hybrid logics with
//! cylindrical algebraic decomposition.
//!
//! Input format: SMT-LIB2 `.smt2` files (nonlinear arithmetic).
//! Executable: `smtrat` with SMT-LIB2 input.

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// SMT-RAT nonlinear arithmetic SMT solver backend
pub struct SmtRatBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl SmtRatBackend {
    /// Create a new SMT-RAT backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        SmtRatBackend { config }
    }

    /// Parse SMT-RAT output to determine success or failure
    ///
    /// Same as OpenSMT: "unsat" → success; "sat" or "unknown" → failure.
    fn parse_result(&self, output: &str) -> Result<bool> {
        for line in output.lines() {
            let trimmed = line.trim().to_lowercase();

            // Success
            if trimmed == "unsat" {
                return Ok(true);
            }

            // Failure
            if trimmed == "sat" || trimmed == "unknown" {
                return Ok(false);
            }
        }

        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for SmtRatBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::SmtRat
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get SMT-RAT version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_smtrat.smt2";
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
            "Tactic application not supported for SMT-RAT".to_string(),
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
        let temp_path = "/tmp/echidna_smtrat.smt2";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run SMT-RAT")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
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
    fn test_smtrat_backend_creation() {
        let config = ProverConfig::default();
        let backend = SmtRatBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::SmtRat);
    }

    #[test]
    fn test_parse_result_unsat() {
        let config = ProverConfig::default();
        let backend = SmtRatBackend::new(config);
        let output = "unsat\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_sat() {
        let config = ProverConfig::default();
        let backend = SmtRatBackend::new(config);
        let output = "sat\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
