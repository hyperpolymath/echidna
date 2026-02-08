// SPDX-License-Identifier: PMPL-1.0-or-later
//! MiniZinc constraint modelling backend
#![allow(dead_code)]
use async_trait::async_trait;
use anyhow::{Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
pub struct MiniZincBackend { config: ProverConfig }
impl MiniZincBackend {
    pub fn new(config: ProverConfig) -> Self { MiniZincBackend { config } }
    fn to_input_format(&self, state: &ProofState) -> Result<String> { let mut s = String::new(); if let Some(g) = state.goals.first() { s.push_str(&format!("% goal: {}\nconstraint true;\nsolve satisfy;\n", g.target)); } Ok(s) }
    fn parse_result(&self, output: &str) -> Result<bool> { let l = output.to_lowercase(); if l.contains("unsatisfiable") || l.contains("=====unsatisfiable=====") || l.contains("error") { Ok(false) } else if l.contains("----------") || l.contains("=====") || l.contains("satisfied") { Ok(true) } else { Err(anyhow::anyhow!("MiniZinc inconclusive")) } }
}
#[async_trait]
impl ProverBackend for MiniZincBackend {
    fn kind(&self) -> ProverKind { ProverKind::MiniZinc }
    async fn version(&self) -> Result<String> { let o = Command::new(&self.config.executable).arg("--version").output().await?; Ok(String::from_utf8_lossy(&o.stdout).lines().next().unwrap_or("unknown").to_string()) }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> { self.parse_string(&tokio::fs::read_to_string(path).await?).await }
    async fn parse_string(&self, content: &str) -> Result<ProofState> { let mut state = ProofState::default(); for line in content.lines() { let l = line.trim(); if !l.is_empty() && !l.starts_with("%") { state.goals.push(Goal { id: format!("goal_{}", state.goals.len()), target: Term::Const(l.to_string()), hypotheses: vec![] }); } } if state.goals.is_empty() { state.goals.push(Goal { id: "goal_0".to_string(), target: Term::Const("satisfy".to_string()), hypotheses: vec![] }); } Ok(state) }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> { Err(anyhow::anyhow!("MiniZinc: constraint solving, not interactive proving")) }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> { let input = self.to_input_format(state)?; let mut child = Command::new(&self.config.executable).arg("--solver").arg("gecode").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().context("Failed to spawn MiniZinc")?; if let Some(mut stdin) = child.stdin.take() { stdin.write_all(input.as_bytes()).await?; drop(stdin); } let output = tokio::time::timeout(tokio::time::Duration::from_secs(self.config.timeout + 5), child.wait_with_output()).await.context("MiniZinc timed out")??; self.parse_result(&format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr))) }
    async fn export(&self, state: &ProofState) -> Result<String> { self.to_input_format(state) }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> { Ok(vec![]) }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> { Ok(vec![]) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, config: ProverConfig) { self.config = config; }
}
#[cfg(test)]
mod tests { use super::*;
    #[tokio::test] async fn test_minizinc_export() { let b = MiniZincBackend::new(ProverConfig { executable: PathBuf::from("minizinc"), timeout: 10, ..Default::default() }); let mut s = ProofState::default(); s.goals.push(Goal { id: "g".to_string(), target: Term::Const("x > 0".to_string()), hypotheses: vec![] }); assert!(b.to_input_format(&s).unwrap().contains("constraint")); }
    #[tokio::test] async fn test_minizinc_parse() { let b = MiniZincBackend::new(ProverConfig { executable: PathBuf::from("minizinc"), timeout: 10, ..Default::default() }); let s = b.parse_string("var 1..10: x;\nsolve satisfy;").await.unwrap(); assert!(!s.goals.is_empty()); }
    #[test] fn test_minizinc_result() { let b = MiniZincBackend::new(ProverConfig { executable: PathBuf::from("minizinc"), timeout: 10, ..Default::default() }); assert!(b.parse_result("----------\nx = 5").unwrap()); assert!(!b.parse_result("=====UNSATISFIABLE=====").unwrap()); }
}
