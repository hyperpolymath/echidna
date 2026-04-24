// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Cubical Agda Backend
//!
//! Cubical Agda extends Agda with cubical HoTT features: path types,
//! univalence, higher inductive types, and interval-based computations.
//! Complements classical Agda with synthetic homotopy theory and univalence.
//!
//! Input format: `.agda` files with cubical HoTT content (--cubical mode).
//! Executable: `agda` with `--cubical` flag.

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// Cubical Agda proof assistant backend
pub struct CubicalAgdaBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl CubicalAgdaBackend {
    /// Create a new Cubical Agda backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        CubicalAgdaBackend { config }
    }

    /// Parse Cubical Agda output to determine success or failure
    ///
    /// Agda outputs "Finished" on successful compilation; any line containing "error"
    /// (case-insensitive) indicates failure.
    fn parse_result(&self, output: &str) -> Result<bool> {
        for line in output.lines() {
            let trimmed = line.trim();

            // Success marker
            if trimmed.contains("Finished") {
                return Ok(true);
            }

            // Error markers
            if trimmed.to_lowercase().contains("error") {
                return Ok(false);
            }
        }

        // No explicit success/failure found — assume failure
        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for CubicalAgdaBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::CubicalAgda
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Cubical Agda version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_cubical_agda.agda";
        tokio::fs::write(temp_path, content).await?;
        self.check(&ProofState {
            goals: vec![],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        })
        .await?;
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
            "Tactic application not supported for Cubical Agda".to_string(),
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
        let temp_path = "/tmp/echidna_cubical_agda.agda";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("--cubical")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run Cubical Agda")?;

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
    fn test_cubical_agda_backend_creation() {
        let config = ProverConfig::default();
        let backend = CubicalAgdaBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::CubicalAgda);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = CubicalAgdaBackend::new(config);
        let output = "Compiling...\nFinished\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_error() {
        let config = ProverConfig::default();
        let backend = CubicalAgdaBackend::new(config);
        let output = "error: type mismatch\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
