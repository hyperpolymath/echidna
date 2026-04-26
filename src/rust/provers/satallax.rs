// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Satallax higher-order automated theorem prover backend

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

pub struct SatallaxBackend {
    config: ProverConfig,
}

impl SatallaxBackend {
    pub fn new(config: ProverConfig) -> Self {
        SatallaxBackend { config }
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
impl ProverBackend for SatallaxBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Satallax
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-v")
            .output()
            .await
            .context("Failed to run satallax -v")?;
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
        let content = super::bounded_read_proof_file(&path).await.context("Failed to read proof file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert("source_path".to_string(), serde_json::Value::String(path.to_string_lossy().into_owned()));
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert("satallax_source".to_string(), serde_json::Value::String(content.to_string()));
        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') { continue; }
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
        Err(anyhow::anyhow!("Satallax is a fully automated prover - interactive tactics not supported"))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp_code = if let Some(src) = state.metadata.get("satallax_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_tptp(state)?
        };

        let mut child = Command::new(&self.config.executable)
            .arg("-t").arg(format!("{}", self.config.timeout))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Satallax process")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(tptp_code.as_bytes()).await.context("Failed to write to Satallax stdin")?;
            stdin.flush().await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(tokio::time::Duration::from_secs(self.config.timeout + 5), child.wait_with_output())
            .await.context("Satallax timed out")??;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        self.parse_result(&stdout).or_else(|_| self.parse_result(&stderr))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tptp(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let tactics = vec![
            Tactic::Custom { prover: "satallax".to_string(), command: "timeout".to_string(), args: vec![format!("{}", self.config.timeout)] },
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
    fn test_satallax_backend_creation() {
        let config = ProverConfig::default();
        let backend = SatallaxBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Satallax);
    }

    #[test]
    fn test_satallax_parse_result_theorem() {
        let config = ProverConfig::default();
        let backend = SatallaxBackend::new(config);
        assert!(backend.parse_result("% SZS status Theorem\n").unwrap());
    }

    #[test]
    fn test_satallax_parse_result_satisfiable() {
        let config = ProverConfig::default();
        let backend = SatallaxBackend::new(config);
        assert!(!backend.parse_result("% SZS status Satisfiable\n").unwrap());
    }
}
