// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! E Prover backend
//!
//! E is a highly optimized first-order theorem prover for clausal logic.
//! Multiple CASC winner with excellent performance on large problems.
//!
//! Features:
//! - First-order logic with equality
//! - TPTP format input/output
//! - Superposition calculus
//! - Auto mode with sophisticated strategy selection

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// E Prover theorem prover backend
pub struct EProverBackend {
    config: ProverConfig,
}

impl EProverBackend {
    pub fn new(config: ProverConfig) -> Self {
        EProverBackend { config }
    }

    /// Convert proof state to TPTP format (same as Vampire)
    fn to_tptp(&self, state: &ProofState) -> Result<String> {
        let mut tptp = String::new();

        for (i, axiom) in state.context.axioms.iter().enumerate() {
            tptp.push_str(&format!("fof(axiom_{}, axiom, {}).\n", i, axiom));
        }

        for (i, def) in state.context.definitions.iter().enumerate() {
            tptp.push_str(&format!("fof(definition_{}, axiom, {}).\n", i, def));
        }

        if let Some(goal) = state.goals.first() {
            tptp.push_str(&format!("fof(conjecture, conjecture, {}).\n", goal.target));
        }

        Ok(tptp)
    }

    /// Parse E output to determine proof success
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("# Proof found!")
            || output.contains("# SZS status Theorem")
            || output.contains("# SZS status Unsatisfiable")
        {
            Ok(true)
        } else if output.contains("# SZS status CounterSatisfiable")
            || output.contains("# SZS status Satisfiable")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "E Prover inconclusive: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for EProverBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::EProver
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run eprover --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout
            .lines()
            .next()
            .unwrap_or("unknown")
            .trim()
            .to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
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
            "eprover_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') || line.starts_with('#') {
                continue;
            }

            if line.starts_with("fof(") {
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
            "E Prover is fully automated - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Prefer the original TPTP source when parse_file / parse_string
        // stashed it.  `to_tptp(state)` round-trips through the generic
        // Term IR and silently mangles anything beyond toy axioms.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg("--auto")
                    .arg("--tptp3-format")
                    .arg("--cpu-limit")
                    .arg(format!("{}", self.config.timeout))
                    .arg("--proof-object=0")
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("E Prover timed out")??;
            let stdout = String::from_utf8_lossy(&output.stdout);
            return self.parse_result(&stdout);
        }
        let tptp_code = if let Some(src) = state
            .metadata
            .get("eprover_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_tptp(state)?
        };

        let mut child = Command::new(&self.config.executable)
            .arg("--auto")
            .arg("--tptp3-format")
            .arg("--cpu-limit")
            .arg(format!("{}", self.config.timeout))
            .arg("--proof-object=0")
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn E Prover process")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(tptp_code.as_bytes()).await?;
            stdin.flush().await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("E Prover timed out")??;

        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tptp(state)
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

    #[tokio::test]
    async fn test_eprover_tptp_export() {
        let config = ProverConfig {
            executable: PathBuf::from("eprover"),
            timeout: 10,
            ..Default::default()
        };

        let backend = EProverBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("p => q".to_string());
        state.context.axioms.push("p".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("q".to_string()),
            hypotheses: vec![],
        });

        let tptp = backend.to_tptp(&state).unwrap();

        assert!(tptp.contains("fof(axiom_0, axiom, p => q)."));
        assert!(tptp.contains("fof(axiom_1, axiom, p)."));
        assert!(tptp.contains("fof(conjecture, conjecture, q)."));
    }

    #[test]
    fn test_eprover_kind() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::EProver);
    }

    #[test]
    fn test_eprover_parse_result_theorem() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        assert!(backend
            .parse_result("# Proof found!\n# SZS status Theorem\n")
            .unwrap());
        assert!(backend
            .parse_result("# SZS status Unsatisfiable\n")
            .unwrap());
    }

    #[test]
    fn test_eprover_parse_result_counter_satisfiable() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        assert!(!backend
            .parse_result("# SZS status CounterSatisfiable\n")
            .unwrap());
        assert!(!backend.parse_result("# SZS status Satisfiable\n").unwrap());
    }

    #[test]
    fn test_eprover_parse_result_inconclusive() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        assert!(backend.parse_result("# SZS status ResourceOut\n").is_err());
    }

    #[tokio::test]
    async fn test_eprover_parse_string_tptp() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        let tptp = "fof(ax1, axiom, p(a)).\nfof(conj, conjecture, p(a)).\n";
        let state = backend.parse_string(tptp).await.unwrap();

        assert_eq!(state.context.axioms.len(), 1);
        assert_eq!(state.goals.len(), 1);
    }

    #[tokio::test]
    async fn test_eprover_parse_string_empty() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        let state = backend.parse_string("").await.unwrap();
        assert!(state.goals.is_empty());
        assert!(state.context.axioms.is_empty());
    }

    #[tokio::test]
    async fn test_eprover_parse_string_with_comments() {
        let config = ProverConfig::default();
        let backend = EProverBackend::new(config);

        let tptp = "% This is a comment\nfof(ax1, axiom, p(a)).\n# Another comment\n";
        let state = backend.parse_string(tptp).await.unwrap();

        assert_eq!(state.context.axioms.len(), 1);
    }
}
