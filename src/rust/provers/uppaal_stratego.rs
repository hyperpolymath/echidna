// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! UPPAAL Stratego Backend
//!
//! UPPAAL Stratego extends UPPAAL with strategy synthesis and stochastic
//! model checking. Synthesises controllers satisfying safety and optimality
//! properties on timed automata with randomness.
//!
//! Input format: UPPAAL XML `.xml` files with strategy queries.
//! Executable: `stratego` (from UPPAAL package).

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// UPPAAL Stratego strategy synthesis backend
pub struct UppaalStrategoBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl UppaalStrategoBackend {
    /// Create a new UPPAAL Stratego backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        UppaalStrategoBackend { config }
    }

    /// Parse UPPAAL Stratego output to determine success or failure
    ///
    /// Success: "Strategy found", "Property is satisfied", or "-- Formula is satisfied".
    /// Failure: "Unrealizable" or "Property is NOT satisfied".
    fn parse_result(&self, output: &str) -> Result<bool> {
        for line in output.lines() {
            let trimmed = line.trim();

            // Success markers
            if trimmed.contains("Strategy found")
                || trimmed.contains("Property is satisfied")
                || trimmed.contains("-- Formula is satisfied")
            {
                return Ok(true);
            }

            // Failure markers
            if trimmed.contains("Unrealizable") || trimmed.contains("Property is NOT satisfied") {
                return Ok(false);
            }
        }

        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for UppaalStrategoBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::UppaalStratego
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get UPPAAL Stratego version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_stratego.xml";
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
            "Tactic application not supported for UPPAAL Stratego".to_string(),
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
        let temp_path = "/tmp/echidna_stratego.xml";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("-q")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run UPPAAL Stratego")?;

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
    fn test_uppaal_stratego_backend_creation() {
        let config = ProverConfig::default();
        let backend = UppaalStrategoBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::UppaalStratego);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = UppaalStrategoBackend::new(config);
        let output = "Strategy found\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_unrealizable() {
        let config = ProverConfig::default();
        let backend = UppaalStrategoBackend::new(config);
        let output = "Unrealizable\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
