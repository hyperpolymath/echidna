// SPDX-License-Identifier: PMPL-1.0-or-later
//! TLAPS (TLA+ Proof System) backend for distributed system verification
#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

pub struct TLAPSBackend {
    config: ProverConfig,
}
impl TLAPSBackend {
    pub fn new(config: ProverConfig) -> Self {
        TLAPSBackend { config }
    }
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::from("---- MODULE Export ----\n");
        if let Some(g) = state.goals.first() {
            s.push_str(&format!("THEOREM {}\nPROOF OBVIOUS\n", g.target));
        }
        s.push_str("====\n");
        Ok(s)
    }
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("proved") || l.contains("qed") {
            Ok(true)
        } else if l.contains("error") || l.contains("failed") {
            Ok(false)
        } else {
            Err(anyhow::anyhow!("TLAPS inconclusive"))
        }
    }
}
#[async_trait]
impl ProverBackend for TLAPSBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::TLAPS
    }
    async fn version(&self) -> Result<String> {
        let o = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await?;
        Ok(String::from_utf8_lossy(&o.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .to_string())
    }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await?;
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
            "tlaps_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let l = line.trim();
            if l.is_empty()
                || l.starts_with("\\*")
                || l.starts_with("----")
                || l.starts_with("====")
            {
                continue;
            }
            if l.starts_with("THEOREM") {
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
                target: Term::Const("TRUE".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!("TLAPS: use OBVIOUS/BY/QED"))
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
            .context("TLAPS timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let input = if let Some(src) = state.metadata.get("tlaps_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn TLAPS")?;
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("TLAPS timed out")??;
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
    async fn test_tlaps_export() {
        let b = TLAPSBackend::new(ProverConfig {
            executable: PathBuf::from("tlapm"),
            timeout: 10,
            ..Default::default()
        });
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("TRUE".to_string()),
            hypotheses: vec![],
        });
        assert!(b.to_input_format(&s).unwrap().contains("MODULE"));
    }
    #[tokio::test]
    async fn test_tlaps_parse() {
        let b = TLAPSBackend::new(ProverConfig {
            executable: PathBuf::from("tlapm"),
            timeout: 10,
            ..Default::default()
        });
        let s = b
            .parse_string("---- MODULE T ----\nTHEOREM TRUE\n====")
            .await
            .unwrap();
        assert!(!s.goals.is_empty());
    }
    #[test]
    fn test_tlaps_result() {
        let b = TLAPSBackend::new(ProverConfig {
            executable: PathBuf::from("tlapm"),
            timeout: 10,
            ..Default::default()
        });
        assert!(b.parse_result("proved").unwrap());
    }
}
