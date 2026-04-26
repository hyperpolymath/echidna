// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Rocq Backend
//!
//! Rocq is the 2024 community-renamed version of Coq. It provides dependent
//! type theory with inductive families, tactics, and the Rocq Standard Library.
//! Fully compatible with Coq 8.19+ syntax and libraries.
//!
//! Input format: `.v` files (same as Coq).
//! Executable: `rocq` with `compile` subcommand.

#![allow(dead_code)]

use anyhow::Context;
use anyhow::Result;
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult, Term};

/// Rocq proof assistant backend
pub struct RocqBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl RocqBackend {
    /// Create a new Rocq backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        RocqBackend { config }
    }

    /// Parse Rocq output to determine success or failure
    ///
    /// Success: exit status is success (0).
    /// Failure: exit status non-zero or "Error:" in output.
    fn parse_result(&self, exit_ok: bool, output: &str) -> Result<bool> {
        if !exit_ok {
            return Ok(false);
        }

        // Scan for error messages
        for line in output.lines() {
            if line.contains("Error:") {
                return Ok(false);
            }
        }

        Ok(true)
    }
}

#[async_trait]
impl ProverBackend for RocqBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Rocq
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Rocq version")?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let temp_path = "/tmp/echidna_rocq.v";
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
            "Tactic application not supported for Rocq".to_string(),
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
        let temp_path = "/tmp/echidna_rocq.v";
        tokio::fs::write(temp_path, &content).await?;

        let output = Command::new(&self.config.executable)
            .arg("compile")
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run Rocq")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let combined = format!("{}\n{}", stdout, stderr);
        let success = output.status.success();

        self.parse_result(success, &combined)
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
        // Rocq (the Coq proof assistant, renamed) uses the same tactic
        // language as Coq 8.x. Suggestions mirror the Coq backend's
        // heuristics so that callers receive consistent advice regardless
        // of which spelling they use for the prover.
        let mut suggestions = Vec::new();

        if state.goals.is_empty() {
            return Ok(suggestions);
        }

        let goal = &state.goals[0];

        // Shape-based heuristics matching the Coq backend
        match &goal.target {
            Term::Pi { .. } => {
                suggestions.push(Tactic::Intro(None));
            },
            Term::App { func, .. } => {
                if let Term::Const(name) = func.as_ref() {
                    match name.as_str() {
                        "and" => suggestions.push(Tactic::Custom {
                            prover: "rocq".to_string(),
                            command: "split".to_string(),
                            args: vec![],
                        }),
                        "or" => {
                            suggestions.push(Tactic::Custom {
                                prover: "rocq".to_string(),
                                command: "left".to_string(),
                                args: vec![],
                            });
                            suggestions.push(Tactic::Custom {
                                prover: "rocq".to_string(),
                                command: "right".to_string(),
                                args: vec![],
                            });
                        },
                        "eq" => suggestions.push(Tactic::Reflexivity),
                        _ => {},
                    }
                }
            },
            _ => {},
        }

        // Canonical general tactics
        suggestions.push(Tactic::Simplify);
        suggestions.push(Tactic::Assumption);
        suggestions.push(Tactic::Custom {
            prover: "rocq".to_string(),
            command: "auto".to_string(),
            args: vec![],
        });
        suggestions.push(Tactic::Custom {
            prover: "rocq".to_string(),
            command: "tauto".to_string(),
            args: vec![],
        });

        Ok(crate::provers::gnn_augment_tactics(
            &self.config, state, "rocq", suggestions, limit,
        )
        .await)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Rocq (formerly Coq) exposes a Search command that queries the loaded
        // environment. We wrap it in a minimal .v file and parse the output.
        let search_script = format!(
            "From Coq Require Import Prelude.\nSearch {pattern}.\n"
        );
        let temp_path = "/tmp/echidna_rocq_search.v";
        if tokio::fs::write(temp_path, search_script.as_bytes())
            .await
            .is_err()
        {
            return Ok(vec![]);
        }

        let output = Command::new(&self.config.executable)
            .arg(temp_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await;

        match output {
            Ok(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout);
                let theorems: Vec<String> = stdout
                    .lines()
                    .filter(|line| !line.is_empty() && !line.starts_with("Error"))
                    .map(|s| s.to_string())
                    .collect();
                Ok(theorems)
            },
            Err(_) => Ok(vec![]),
        }
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
    fn test_rocq_backend_creation() {
        let config = ProverConfig::default();
        let backend = RocqBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Rocq);
    }

    #[test]
    fn test_parse_result_success() {
        let config = ProverConfig::default();
        let backend = RocqBackend::new(config);
        let output = "Compiled successfully.\n";
        assert!(backend.parse_result(true, output).unwrap());
    }

    #[test]
    fn test_parse_result_error() {
        let config = ProverConfig::default();
        let backend = RocqBackend::new(config);
        let output = "Error: type mismatch\n";
        assert!(!backend.parse_result(true, output).unwrap());
    }
}
