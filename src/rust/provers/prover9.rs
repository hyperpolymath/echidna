// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Prover9 Backend
//!
//! Prover9 is an automated theorem prover for first-order and equational
//! logic. It uses superposition, resolution, and paramodulation.
//! Pairs with Mace4 for counter-example generation.
//!
//! Input format: Prover9 `.p9` clause notation files.
//! Executable: `prover9` with `-f` flag.

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// Prover9 ATP backend
pub struct Prover9Backend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl Prover9Backend {
    /// Create a new Prover9 backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        Prover9Backend { config }
    }

    /// Parse Prover9 output to determine success or failure
    ///
    /// "THEOREM PROVED" → success; "SEARCH FAILED" or "Fatal error" → failure.
    fn parse_result(&self, output: &str) -> Result<bool> {
        for line in output.lines() {
            let trimmed = line.trim();

            // Success marker
            if trimmed.contains("THEOREM PROVED") {
                return Ok(true);
            }

            // Failure markers
            if trimmed.contains("SEARCH FAILED") || trimmed.contains("Fatal error") {
                return Ok(false);
            }
        }

        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for Prover9Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Prover9
    }

    async fn version(&self) -> Result<String> {
        // Prover9 does not have a standard --version flag; extract from help
        let output = Command::new(&self.config.executable)
            .arg("--help")
            .output()
            .await;

        match output {
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                if !stderr.is_empty() {
                    let first_line = stderr.lines().next().unwrap_or("unknown");
                    Ok(first_line.to_string())
                } else {
                    Ok("Prover9 (version unknown)".to_string())
                }
            }
            Err(_) => Ok("Prover9 (version unknown)".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_prover9.p9";
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
            "Tactic application not supported for Prover9".to_string(),
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
        let temp_path = "/tmp/echidna_prover9.p9";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("-f")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run Prover9")?;

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

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Prover9 is a first-order ATP (resolution + paramodulation).
        // Suggestions are weight-function and strategy flags passed to the binary.
        let tactics = vec![
            Tactic::Custom {
                prover: "prover9".to_string(),
                command: "set".to_string(),
                args: vec!["auto".to_string()],
            },
            Tactic::Custom {
                prover: "prover9".to_string(),
                command: "set".to_string(),
                args: vec!["paramodulation".to_string()],
            },
            Tactic::Custom {
                prover: "prover9".to_string(),
                command: "set".to_string(),
                args: vec!["back_subsumption".to_string()],
            },
            Tactic::Custom {
                prover: "prover9".to_string(),
                command: "assign".to_string(),
                args: vec!["max_seconds 60".to_string()],
            },
            Tactic::Simplify,
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // ATP solvers do not maintain searchable theorem libraries.
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
    fn test_prover9_backend_creation() {
        let config = ProverConfig::default();
        let backend = Prover9Backend::new(config);
        assert_eq!(backend.kind(), ProverKind::Prover9);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = Prover9Backend::new(config);
        let output = "THEOREM PROVED\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_failure() {
        let config = ProverConfig::default();
        let backend = Prover9Backend::new(config);
        let output = "SEARCH FAILED\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
