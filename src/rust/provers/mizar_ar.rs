// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! MizAR Backend
//!
//! MizAR is Mizar integrated with automated theorem proving assistance.
//! Combines the Mizar system's formal article checker with ATP backend
//! solvers (E prover, Vampire) for automated lemma discharge.
//!
//! Input format: Mizar `.miz` article files.
//! Executable: `mizar-atp` (Mizar ATP bridge) with `-atp` flag.

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// MizAR automated reasoning backend
pub struct MizARBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl MizARBackend {
    /// Create a new MizAR backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        MizARBackend { config }
    }

    /// Parse MizAR output to determine success or failure
    ///
    /// Success: "Verified Successfully" or "The proof structure is correct".
    /// Failure: "Error" or "failed" (case-insensitive) in output.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let output_lower = output.to_lowercase();

        // Check for success markers first
        if output.contains("Verified Successfully")
            || output.contains("The proof structure is correct")
        {
            return Ok(true);
        }

        // Check for failure markers
        if output_lower.contains("error") || output_lower.contains("failed") {
            return Ok(false);
        }

        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for MizARBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::MizAR
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get MizAR version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_mizar_ar.miz";
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
        state: &ProofState,
        _tactic: &Tactic,
    ) -> Result<TacticResult> {
        Ok(TacticResult::Error(
            "Tactic application not supported for MizAR".to_string(),
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
        let temp_path = "/tmp/echidna_mizar_ar.miz";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("-atp")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run MizAR")?;

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
    fn test_mizar_ar_backend_creation() {
        let config = ProverConfig::default();
        let backend = MizARBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::MizAR);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = MizARBackend::new(config);
        let output = "Verified Successfully\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_error() {
        let config = ProverConfig::default();
        let backend = MizARBackend::new(config);
        let output = "Error: type mismatch\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
