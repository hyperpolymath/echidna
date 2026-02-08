// SPDX-License-Identifier: PMPL-1.0-or-later
//! Chuffed lazy clause generation CP solver backend
#![allow(dead_code)]
use async_trait::async_trait;
use anyhow::{Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
pub struct ChuffedBackend { config: ProverConfig }
impl ChuffedBackend {
    pub fn new(config: ProverConfig) -> Self { ChuffedBackend { config } }
    fn to_input_format(&self, state: &ProofState) -> Result<String> { let mut s = String::new(); if let Some(g) = state.goals.first() { s.push_str(&format!("% goal: {}\n", g.target)); } Ok(s) }
    fn parse_result(&self, output: &str) -> Result<bool> { let l = output.to_lowercase(); if l.contains("----------") || l.contains("==========") { Ok(true) } else if l.contains("unsatisfiable") || l.contains("=====unsatisfiable=====") || l.contains("error") { Ok(false) } else { Err(anyhow::anyhow!("Chuffed inconclusive")) } }
}
#[async_trait]
impl ProverBackend for ChuffedBackend {
    fn kind(&self) -> ProverKind { ProverKind::Chuffed }
    async fn version(&self) -> Result<String> { Ok("chuffed".to_string()) }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> { self.parse_string(&tokio::fs::read_to_string(path).await?).await }
    async fn parse_string(&self, content: &str) -> Result<ProofState> { let mut state = ProofState::default(); for line in content.lines() { let l = line.trim(); if !l.is_empty() && !l.starts_with("%") { state.goals.push(Goal { id: format!("goal_{}", state.goals.len()), target: Term::Const(l.to_string()), hypotheses: vec![] }); } } if state.goals.is_empty() { state.goals.push(Goal { id: "goal_0".to_string(), target: Term::Const("satisfy".to_string()), hypotheses: vec![] }); } Ok(state) }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> { Err(anyhow::anyhow!("Chuffed: CP solver, not interactive")) }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> { let input = self.to_input_format(state)?; let mut child = Command::new(&self.config.executable).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().context("Failed to spawn Chuffed")?; if let Some(mut stdin) = child.stdin.take() { stdin.write_all(input.as_bytes()).await?; drop(stdin); } let output = tokio::time::timeout(tokio::time::Duration::from_secs(self.config.timeout + 5), child.wait_with_output()).await.context("Chuffed timed out")??; self.parse_result(&format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr))) }
    async fn export(&self, state: &ProofState) -> Result<String> { self.to_input_format(state) }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> { Ok(vec![]) }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> { Ok(vec![]) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, config: ProverConfig) { self.config = config; }
}
#[cfg(test)]
mod tests { use super::*;
    #[tokio::test] async fn test_chuffed_export() { let b = ChuffedBackend::new(ProverConfig { executable: PathBuf::from("fzn-chuffed"), timeout: 10, ..Default::default() }); let mut s = ProofState::default(); s.goals.push(Goal { id: "g".to_string(), target: Term::Const("satisfy".to_string()), hypotheses: vec![] }); assert!(b.to_input_format(&s).unwrap().contains("goal")); }
    #[tokio::test] async fn test_chuffed_parse() { let b = ChuffedBackend::new(ProverConfig { executable: PathBuf::from("fzn-chuffed"), timeout: 10, ..Default::default() }); let s = b.parse_string("var int: x :: output_var;").await.unwrap(); assert!(!s.goals.is_empty()); }
    #[test] fn test_chuffed_result() { let b = ChuffedBackend::new(ProverConfig { executable: PathBuf::from("fzn-chuffed"), timeout: 10, ..Default::default() }); assert!(b.parse_result("----------").unwrap()); }
}
