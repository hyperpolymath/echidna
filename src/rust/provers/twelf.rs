// SPDX-License-Identifier: PMPL-1.0-or-later
//! Twelf logical framework (LF) backend for metatheory verification
#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
pub struct TwelfBackend {
    config: ProverConfig,
}
impl TwelfBackend {
    pub fn new(config: ProverConfig) -> Self {
        TwelfBackend { config }
    }
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        if let Some(g) = state.goals.first() {
            s.push_str(&format!("%% goal: {}\n", g.target));
        }
        Ok(s)
    }
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("ok") || l.contains("type-checked") {
            Ok(true)
        } else if l.contains("error") {
            Ok(false)
        } else {
            Err(anyhow::anyhow!("Twelf inconclusive"))
        }
    }
}
#[async_trait]
impl ProverBackend for TwelfBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Twelf
    }
    async fn version(&self) -> Result<String> {
        Ok("twelf".to_string())
    }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
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
            "twelf_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let l = line.trim();
            if !l.is_empty() && !l.starts_with("%") {
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(l.to_string()),
                    hypotheses: vec![],
                });
            }
        }
        if state.goals.is_empty() {
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const("type".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!("Twelf: use LF declarations"))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("Twelf timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let input = if let Some(src) = state.metadata.get("twelf_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Twelf")?;
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("Twelf timed out")??;
        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> {
        Ok(vec![])
    }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> {
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
    async fn test_twelf_export() {
        let b = TwelfBackend::new(ProverConfig {
            executable: PathBuf::from("twelf-server"),
            timeout: 10,
            ..Default::default()
        });
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("type".to_string()),
            hypotheses: vec![],
        });
        assert!(b.to_input_format(&s).unwrap().contains("goal"));
    }
    #[tokio::test]
    async fn test_twelf_parse() {
        let b = TwelfBackend::new(ProverConfig {
            executable: PathBuf::from("twelf-server"),
            timeout: 10,
            ..Default::default()
        });
        let s = b.parse_string("nat : type.").await.unwrap();
        assert!(!s.goals.is_empty());
    }
    #[test]
    fn test_twelf_result() {
        let b = TwelfBackend::new(ProverConfig {
            executable: PathBuf::from("twelf-server"),
            timeout: 10,
            ..Default::default()
        });
        assert!(b.parse_result("OK").unwrap());
    }
}
