// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Leo-III higher-order automated theorem prover backend
//!
//! Leo-III is a lean, higher-order prover for THF (Typed Higher-Order Form)
//! problems in TPTP format. It combines term rewriting with a saturation-based
//! architecture.
//!
//! Features:
//! - Higher-order logic (THF)
//! - TPTP format input/output
//! - Full first-order and higher-order reasoning
//! - Produces SZS status lines

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Leo-III theorem prover backend
pub struct Leo3Backend {
    config: ProverConfig,
}

impl Leo3Backend {
    pub fn new(config: ProverConfig) -> Self {
        Leo3Backend { config }
    }

    fn to_tptp(&self, state: &ProofState) -> Result<String> {
        let mut tptp = String::new();

        for (i, axiom) in state.context.axioms.iter().enumerate() {
            tptp.push_str(&format!("thf(axiom_{}, axiom, {}).\n", i, axiom));
        }

        for (i, def) in state.context.definitions.iter().enumerate() {
            tptp.push_str(&format!("thf(definition_{}, axiom, {}).\n", i, def));
        }

        if let Some(goal) = state.goals.first() {
            tptp.push_str(&format!("thf(conjecture, conjecture, {}).\n", goal.target));
        }

        Ok(tptp)
    }

    fn parse_result(&self, output: &str) -> Result<bool> {
        super::tptp_output::parse_szs_status(output)
    }
}

#[async_trait]
impl ProverBackend for Leo3Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Leo3
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run leo3 --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("unknown").to_string()
        } else {
            stderr.lines().next().unwrap_or("unknown").to_string()
        };

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read proof file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "leo3_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') {
                continue;
            }

            if line.starts_with("thf(") {
                if let Some(formula) = line.split(',').nth(2) {
                    let formula = formula.trim_end_matches(").").trim();
                    if line.contains("axiom") {
                        state.context.axioms.push(formula.to_string());
                    } else if line.contains("conjecture") {
                        state.goals.push(Goal {
                            id: format!("goal_{}", state.goals.len()),
                            target: Term::Const(formula.to_string()),
                            hypotheses: vec![],
                        });
                    }
                }
            }
        }

        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Leo-III is a fully automated prover - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp_code = if let Some(src) = state
            .metadata
            .get("leo3_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_tptp(state)?
        };

        let mut child = Command::new(&self.config.executable)
            .arg("--input")
            .arg("tptp")
            .arg("--output")
            .arg("tptp")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Leo-III process")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(tptp_code.as_bytes())
                .await
                .context("Failed to write to Leo-III stdin")?;
            stdin.flush().await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("Leo-III timed out")??;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        self.parse_result(&stdout)
            .or_else(|_| self.parse_result(&stderr))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tptp(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let tactics = vec![
            Tactic::Custom {
                prover: "leo3".to_string(),
                command: "timeout".to_string(),
                args: vec![format!("{}", self.config.timeout)],
            },
            Tactic::Custom {
                prover: "leo3".to_string(),
                command: "mode".to_string(),
                args: vec!["tptp".to_string()],
            },
        ];
        Ok(tactics.into_iter().take(limit).collect())
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
    fn test_leo3_backend_creation() {
        let config = ProverConfig::default();
        let backend = Leo3Backend::new(config);
        assert_eq!(backend.kind(), ProverKind::Leo3);
    }

    #[test]
    fn test_leo3_parse_result_theorem() {
        let config = ProverConfig::default();
        let backend = Leo3Backend::new(config);
        let output = "% SZS status Theorem\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_leo3_parse_result_unknown() {
        let config = ProverConfig::default();
        let backend = Leo3Backend::new(config);
        let output = "% SZS status Unknown\n";
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_leo3_to_tptp() {
        let config = ProverConfig::default();
        let backend = Leo3Backend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("p => q".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("q".to_string()),
            hypotheses: vec![],
        });

        let tptp = backend.to_tptp(&state).unwrap();

        assert!(tptp.contains("thf(axiom_0, axiom, p => q)."));
        assert!(tptp.contains("thf(conjecture, conjecture, q)."));
    }
}
