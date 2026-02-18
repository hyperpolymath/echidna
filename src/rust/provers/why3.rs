// SPDX-License-Identifier: PMPL-1.0-or-later
//! Why3 multi-prover orchestration backend
#![allow(dead_code)]
use async_trait::async_trait;
use anyhow::{Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

pub struct Why3Backend { config: ProverConfig }
impl Why3Backend {
    pub fn new(config: ProverConfig) -> Self { Why3Backend { config } }
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::from("module Export\n");
        for (i, ax) in state.context.axioms.iter().enumerate() { s.push_str(&format!("  axiom ax_{} : {}\n", i, ax)); }
        if let Some(g) = state.goals.first() { s.push_str(&format!("  goal g : {}\n", g.target)); }
        s.push_str("end\n");
        Ok(s)
    }
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("valid") || l.contains("proved") { Ok(true) } else if l.contains("unknown") || l.contains("timeout") || l.contains("error") { Ok(false) }
        else { Err(anyhow::anyhow!("Why3 inconclusive")) }
    }
}
#[async_trait]
impl ProverBackend for Why3Backend {
    fn kind(&self) -> ProverKind { ProverKind::Why3 }
    async fn version(&self) -> Result<String> { let o = Command::new(&self.config.executable).arg("--version").output().await?; Ok(String::from_utf8_lossy(&o.stdout).lines().next().unwrap_or("unknown").to_string()) }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> { self.parse_string(&tokio::fs::read_to_string(path).await?).await }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        for line in content.lines() { let l = line.trim(); if l.is_empty() || l.starts_with("(*") { continue; }
            if l.starts_with("goal ") { state.goals.push(Goal { id: format!("goal_{}", state.goals.len()), target: Term::Const(l.to_string()), hypotheses: vec![] }); }
            else if l.starts_with("axiom ") { state.context.axioms.push(l.to_string()); }
        }
        if state.goals.is_empty() { state.goals.push(Goal { id: "goal_0".to_string(), target: Term::Const("true".to_string()), hypotheses: vec![] }); }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> { Err(anyhow::anyhow!("Why3: use built-in transformations")) }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let input = self.to_input_format(state)?;
        let mut child = Command::new(&self.config.executable).arg("prove").arg("-P").arg("z3").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().context("Failed to spawn Why3")?;
        if let Some(mut stdin) = child.stdin.take() { stdin.write_all(input.as_bytes()).await?; drop(stdin); }
        let output = tokio::time::timeout(tokio::time::Duration::from_secs(self.config.timeout + 5), child.wait_with_output()).await.context("Why3 timed out")??;
        self.parse_result(&format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr)))
    }
    async fn export(&self, state: &ProofState) -> Result<String> { self.to_input_format(state) }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> { Ok(vec![]) }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> { Ok(vec![]) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, config: ProverConfig) { self.config = config; }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[tokio::test] async fn test_why3_export() { let b = Why3Backend::new(ProverConfig { executable: PathBuf::from("why3"), timeout: 10, ..Default::default() }); let mut s = ProofState::default(); s.goals.push(Goal { id: "g".to_string(), target: Term::Const("true".to_string()), hypotheses: vec![] }); assert!(b.to_input_format(&s).unwrap().contains("module Export")); }
    #[tokio::test] async fn test_why3_parse() { let b = Why3Backend::new(ProverConfig { executable: PathBuf::from("why3"), timeout: 10, ..Default::default() }); let s = b.parse_string("goal g : true").await.unwrap(); assert!(!s.goals.is_empty()); }
    #[test] fn test_why3_result() { let b = Why3Backend::new(ProverConfig { executable: PathBuf::from("why3"), timeout: 10, ..Default::default() }); assert!(b.parse_result("Valid").unwrap()); assert!(!b.parse_result("Unknown").unwrap()); }
}
