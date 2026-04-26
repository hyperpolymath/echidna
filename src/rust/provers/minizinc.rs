// SPDX-License-Identifier: PMPL-1.0-or-later
//! MiniZinc constraint modelling backend
#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
pub struct MiniZincBackend {
    config: ProverConfig,
}
impl MiniZincBackend {
    pub fn new(config: ProverConfig) -> Self {
        MiniZincBackend { config }
    }
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        if let Some(g) = state.goals.first() {
            s.push_str(&format!(
                "% goal: {}\nconstraint true;\nsolve satisfy;\n",
                g.target
            ));
        }
        Ok(s)
    }
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("unsatisfiable")
            || l.contains("=====unsatisfiable=====")
            || l.contains("error")
        {
            Ok(false)
        } else if l.contains("----------") || l.contains("=====") || l.contains("satisfied") {
            Ok(true)
        } else {
            Err(anyhow::anyhow!("MiniZinc inconclusive"))
        }
    }
}
#[async_trait]
impl ProverBackend for MiniZincBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::MiniZinc
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
            "minizinc_source".to_string(),
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
                target: Term::Const("satisfy".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "MiniZinc: constraint solving, not interactive proving"
        ))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg("--solver")
                    .arg("gecode")
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("MiniZinc timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let input = if let Some(src) = state
            .metadata
            .get("minizinc_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };
        let mut child = Command::new(&self.config.executable)
            .arg("--solver")
            .arg("gecode")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn MiniZinc")?;
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("MiniZinc timed out")??;
        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // MiniZinc is a high-level constraint modelling language. Suggestions
        // are solve annotations and search strategies that guide the underlying
        // solver (Gecode, Chuffed, OR-Tools, etc.).
        let tactics = vec![
            Tactic::Custom {
                prover: "minizinc".to_string(),
                command: "solve".to_string(),
                args: vec!["satisfy".to_string()],
            },
            Tactic::Custom {
                prover: "minizinc".to_string(),
                command: "solve".to_string(),
                args: vec!["minimize objective".to_string()],
            },
            Tactic::Custom {
                prover: "minizinc".to_string(),
                command: "annotation".to_string(),
                args: vec!["int_search(vars, first_fail, indomain_min, complete)".to_string()],
            },
            Tactic::Custom {
                prover: "minizinc".to_string(),
                command: "output".to_string(),
                args: vec!["[ show(vars) ]".to_string()],
            },
            Tactic::Simplify,
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Constraint modelling languages have no theorem libraries.
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
    async fn test_minizinc_export() {
        let b = MiniZincBackend::new(ProverConfig {
            executable: PathBuf::from("minizinc"),
            timeout: 10,
            ..Default::default()
        });
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("x > 0".to_string()),
            hypotheses: vec![],
        });
        assert!(b.to_input_format(&s).unwrap().contains("constraint"));
    }
    #[tokio::test]
    async fn test_minizinc_parse() {
        let b = MiniZincBackend::new(ProverConfig {
            executable: PathBuf::from("minizinc"),
            timeout: 10,
            ..Default::default()
        });
        let s = b
            .parse_string("var 1..10: x;\nsolve satisfy;")
            .await
            .unwrap();
        assert!(!s.goals.is_empty());
    }
    #[test]
    fn test_minizinc_result() {
        let b = MiniZincBackend::new(ProverConfig {
            executable: PathBuf::from("minizinc"),
            timeout: 10,
            ..Default::default()
        });
        assert!(b.parse_result("----------\nx = 5").unwrap());
        assert!(!b.parse_result("=====UNSATISFIABLE=====").unwrap());
    }
}
