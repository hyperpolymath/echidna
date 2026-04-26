// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! MetiTarski ATP backend
//!
//! MetiTarski is a first-order automated theorem prover extended with
//! support for transcendental functions (sin, cos, exp, log, etc.) via
//! real-closed field decision procedures.
//!
//! Features:
//! - First-order logic with transcendental arithmetic
//! - TPTP format input with real-arithmetic extensions
//! - Polynomial/exponential/trigonometric function reasoning
//! - RCF integration for decision procedures

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// MetiTarski theorem prover backend
pub struct MetiTarskiBackend {
    config: ProverConfig,
}

impl MetiTarskiBackend {
    pub fn new(config: ProverConfig) -> Self {
        MetiTarskiBackend { config }
    }

    /// Convert proof state to TPTP format
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

    /// Parse MetiTarski output to determine proof success
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("% SZS status Theorem")
            || output.contains("Success")
            || output.contains("proved")
        {
            Ok(true)
        } else if output.contains("% SZS status Satisfiable")
            || output.contains("Failed")
            || output.contains("not proved")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "MetiTarski inconclusive or error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for MetiTarskiBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::MetiTarski
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run metit --version")?;

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
            "metitarski_source".to_string(),
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
            "MetiTarski is a fully automated prover - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp = self.to_tptp(state)?;
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn metit")?;

        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open metit stdin"))?;
            stdin
                .write_all(tptp.as_bytes())
                .await
                .context("Failed to write to metit stdin")?;
        }

        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for metit")?;

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
    fn test_metitarski_kind() {
        let config = ProverConfig::default();
        let backend = MetiTarskiBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::MetiTarski);
    }

    #[test]
    fn test_metitarski_to_tptp() {
        let config = ProverConfig::default();
        let backend = MetiTarskiBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("sin(x) < 1".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("cos(x) >= 0".to_string()),
            hypotheses: vec![],
        });
        let tptp = backend.to_tptp(&state).expect("to_tptp failed");
        assert!(tptp.contains("fof(axiom_0, axiom, sin(x) < 1)."));
        assert!(tptp.contains("fof(conjecture, conjecture, cos(x) >= 0)."));
    }

    #[test]
    fn test_metitarski_parse_result_theorem() {
        let config = ProverConfig::default();
        let backend = MetiTarskiBackend::new(config);

        let output = "% SZS status Theorem\nproof found";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(result);
    }

    #[test]
    fn test_metitarski_parse_result_satisfiable() {
        let config = ProverConfig::default();
        let backend = MetiTarskiBackend::new(config);

        let output = "% SZS status Satisfiable\nmodel not found";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(!result);
    }

}
