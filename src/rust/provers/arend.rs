// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Arend — cubical HoTT prover (JetBrains). Distinct from Agda's
//! cubical mode in having path primitives as first-class syntax and
//! IntelliJ-integrated IDE tooling. Co-lives with Agda/Lean as a
//! classical server of the `TypeDiscipline::Cubical` discipline.
//! Vendor: github.com/JetBrains/Arend

#![allow(dead_code)]
use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

pub struct ArendBackend { config: ProverConfig }
impl ArendBackend { pub fn new(c: ProverConfig) -> Self { Self { config: c } }
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() { PathBuf::from("arend") }
        else { self.config.executable.clone() } } }

#[async_trait]
impl ProverBackend for ArendBackend {
    fn kind(&self) -> ProverKind { ProverKind::Arend }
    async fn version(&self) -> Result<String> {
        match Command::new(self.binary()).arg("--version").output().await {
            Ok(o) if o.status.success() => Ok(String::from_utf8_lossy(&o.stdout).trim().to_string()),
            Ok(_) => Ok("arend@unavailable".into()),
            Err(_) => Ok("arend@not-installed".into()) } }
    async fn parse_file(&self, p: PathBuf) -> Result<ProofState> {
        let c = tokio::fs::read_to_string(&p).await.with_context(|| format!("Arend: reading {}", p.display()))?;
        self.parse_string(&c).await }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut s = ProofState {
            goals: vec![Goal { id: "arend-file".into(), target: Term::Const(content.into()), hypotheses: vec![] }],
            context: ProofContext::default(), proof_script: vec![], metadata: Default::default() };
        s.metadata.insert("arend_source".into(), serde_json::Value::String(content.into())); Ok(s) }
    async fn apply_tactic(&self, s: &ProofState, t: &Tactic) -> Result<TacticResult> {
        let mut n = s.clone(); n.proof_script.push(t.clone()); Ok(TacticResult::Success(n)) }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let src: String = state.metadata.get("arend_source").and_then(|v| v.as_str()).map(String::from).unwrap_or_default();
        let dir = tempfile::Builder::new().prefix("echidna-arend-").tempdir().context("Arend: tempdir")?;
        let input = dir.path().join("Check.ard");
        tokio::fs::write(&input, src.as_bytes()).await.context("Arend: writing")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg(&input).stdout(Stdio::piped()).stderr(Stdio::piped());
        for a in &self.config.args { cmd.arg(a); }
        match cmd.output().await {
            Ok(o) if o.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("Arend: binary not runnable: {}", e)) } }
    async fn export(&self, s: &ProofState) -> Result<String> {
        Ok(s.metadata.get("arend_source").and_then(|v| v.as_str()).map(String::from).unwrap_or_default()) }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> { Ok(vec![]) }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> { Ok(vec![]) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, c: ProverConfig) { self.config = c; } }

#[cfg(test)]
mod tests { use super::*;
    #[test] fn kind_is_arend() { assert_eq!(ArendBackend::new(ProverConfig::default()).kind(), ProverKind::Arend); } }
