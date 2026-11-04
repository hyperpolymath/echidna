// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! OpenSMT Backend
//!
//! OpenSMT is an SMT solver with support for QF_UF, QF_EUF, QF_LRA, and other
//! logics. Generates Craig interpolants for abstraction refinement.
//!
//! Input format: SMT-LIB2 `.smt2` files.
//! Executable: `opensmt` with SMT-LIB2 piped to stdin or file argument.

#![allow(dead_code)]

use anyhow::{bail, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// OpenSMT SMT solver backend
pub struct OpenSmtBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl OpenSmtBackend {
    /// Create a new OpenSMT backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        OpenSmtBackend { config }
    }

    /// Parse OpenSMT output to determine success or failure
    ///
    /// "unsat" (on any line) → success; "sat" or "unknown" → failure.
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
impl ProverBackend for OpenSmtBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::OpenSmt
    }

    async fn version(&self) -> Result<String> {
        let output = tokio::time::timeout(
            std::time::Duration::from_secs(self.config.timeout.clamp(1, 30)),
            Command::new(&self.config.executable)
                .arg("--version")
                .stdin(Stdio::null())
                .kill_on_drop(true)
                .output(),
        )
        .await
        .context("OpenSMT version probe timed out")?
        .with_context(|| {
            format!(
                "Failed to execute OpenSMT at {}",
                self.config.executable.display()
            )
        })?;
        if !output.status.success() {
            bail!("OpenSMT version probe failed: {}", output.status);
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if stdout.trim().is_empty() {
            stderr.trim()
        } else {
            stdout.trim()
        };
        if version.is_empty() {
            bail!("OpenSMT version probe returned no version information");
        }
        Ok(version.to_owned())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_opensmt.smt2";
        tokio::fs::write(temp_path, content).await?;
        Ok(ProofState {
            goals: vec![],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        })
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Ok(TacticResult::Error(
            "Tactic application not supported for OpenSMT".to_string(),
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
        let temp_path = "/tmp/echidna_opensmt.smt2";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run OpenSMT")?;

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

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // OpenSMT is an SMT solver focused on interpolation-based verification.
        // Suggestions are option-level strategy hints (similar to Z3 and CVC5).
        let tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "opensmt".to_string(),
                command: "set-option".to_string(),
                args: vec![":produce-interpolants true".to_string()],
            },
            Tactic::Custom {
                prover: "opensmt".to_string(),
                command: "set-logic".to_string(),
                args: vec!["QF_LRA".to_string()],
            },
            Tactic::Custom {
                prover: "opensmt".to_string(),
                command: "set-logic".to_string(),
                args: vec!["QF_UF".to_string()],
            },
            Tactic::Custom {
                prover: "opensmt".to_string(),
                command: "set-option".to_string(),
                args: vec![":interpolation-algorithm 1".to_string()],
            },
        ];
        Ok(
            crate::provers::gnn_augment_tactics(&self.config, state, "opensmt", tactics, limit)
                .await,
        )
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // SMT solvers do not maintain searchable theorem libraries.
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
    fn test_opensmt_backend_creation() {
        let config = ProverConfig::default();
        let backend = OpenSmtBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::OpenSmt);
    }

    #[tokio::test]
    async fn test_version_rejects_a_missing_executable() {
        let directory = tempfile::tempdir().unwrap();
        let backend = OpenSmtBackend::new(ProverConfig {
            executable: directory.path().join("missing-opensmt"),
            ..ProverConfig::default()
        });
        assert!(backend.version().await.is_err());
    }

    #[test]
    fn test_parse_result_unsat() {
        let config = ProverConfig::default();
        let backend = OpenSmtBackend::new(config);
        let output = "unsat\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_parse_result_sat() {
        let config = ProverConfig::default();
        let backend = OpenSmtBackend::new(config);
        let output = "sat\n";
        assert!(!backend.parse_result(output).unwrap());
    }
}
