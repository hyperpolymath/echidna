// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Twee equational theorem prover backend
//!
//! Twee is a fully automated pure equational theorem prover based on the
//! Knuth-Bendix completion procedure. It is deterministic and has been
//! formally audited, making it trust-tier 3.
//!
//! Features:
//! - Pure equational reasoning (FOL without predicates)
//! - Knuth-Bendix completion algorithm
//! - Deterministic output (fully auditable)
//! - TPTP equality-only input

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Twee equational theorem prover backend
pub struct TweeBackend {
    config: ProverConfig,
}

impl TweeBackend {
    pub fn new(config: ProverConfig) -> Self {
        TweeBackend { config }
    }

    /// Convert proof state to TPTP equational format
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

    /// Parse Twee output to determine proof success
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("THEOREM")
            || output.contains("YES")
            || output.contains("Proof found")
        {
            Ok(true)
        } else if output.contains("COUNTER-SATISFIABLE")
            || output.contains("NO")
            || output.contains("No proof")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "Twee inconclusive or error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for TweeBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Twee
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run twee --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let version = if !stderr.is_empty() {
            stderr.lines().next().unwrap_or("unknown").to_string()
        } else {
            stdout.lines().next().unwrap_or("unknown").to_string()
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
            "twee_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') {
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
            "Twee is a fully automated equational prover - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp = self.to_tptp(state)?;
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn twee")?;

        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open twee stdin"))?;
            stdin
                .write_all(tptp.as_bytes())
                .await
                .context("Failed to write to twee stdin")?;
        }

        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for twee")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tptp(state)
    }

    async fn suggest_tactics(
        &self,
        _state: &ProofState,
        _limit: usize,
    ) -> Result<Vec<Tactic>> {
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
    fn test_twee_kind() {
        let config = ProverConfig::default();
        let backend = TweeBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Twee);
    }

    #[test]
    fn test_twee_to_tptp() {
        let config = ProverConfig::default();
        let backend = TweeBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("f(x) = g(x)".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("f(a) = g(a)".to_string()),
            hypotheses: vec![],
        });
        let tptp = backend.to_tptp(&state).expect("to_tptp failed");
        assert!(tptp.contains("fof(axiom_0, axiom, f(x) = g(x))."));
        assert!(tptp.contains("fof(conjecture, conjecture, f(a) = g(a))."));
    }

    #[test]
    fn test_twee_parse_result_theorem() {
        let config = ProverConfig::default();
        let backend = TweeBackend::new(config);

        let output = "THEOREM";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(result);
    }

    #[test]
    fn test_twee_parse_result_counter_satisfiable() {
        let config = ProverConfig::default();
        let backend = TweeBackend::new(config);

        let output = "COUNTER-SATISFIABLE";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(!result);
    }

}
