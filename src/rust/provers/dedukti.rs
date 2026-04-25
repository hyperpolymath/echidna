// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Dedukti — classical prover backend for the universal λΠ-modulo logical
//! framework.
//!
//! Dedukti is already present in echidna as a **proof-exchange format**
//! (`src/rust/exchange/dedukti.rs`). This module adds the sibling
//! **prover-as-solver** role: invoking `dkcheck` / `lambdapi` on a `.dk`
//! or `.lp` source to typecheck it end-to-end, treating Dedukti's
//! rewrite-rule machinery as the reasoning kernel. The exchange module
//! and this prover module are complementary — one translates proofs
//! into the format, the other checks proofs written in the format.
//!
//! Highest marginal value in the Phase 4 backlog because Dedukti is the
//! universal translation target: proofs from Coq, HOL Light, HOL4, Matita,
//! Agda, and others can be encoded in λΠ-modulo and then re-checked here.
//! When triangulation-rate hits the Phase 3 threshold this is the channel
//! through which cross-prover port mills will flow.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Dedukti backend.
pub struct DeduktiBackend {
    config: ProverConfig,
}

impl DeduktiBackend {
    pub fn new(config: ProverConfig) -> Self {
        DeduktiBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("dkcheck")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for DeduktiBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Dedukti
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("--version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            },
            Ok(out) => Ok(format!(
                "dedukti@unavailable (status {:?})",
                out.status.code()
            )),
            Err(_) => Ok("dedukti@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Dedukti: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "dedukti-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "dedukti_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let source: String = state
            .metadata
            .get("dedukti_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-dedukti-")
            .tempdir()
            .context("Dedukti: tempdir")?;
        let input = tmp_dir.path().join("check.dk");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Dedukti: writing input")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg("-q")
            .arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("Dedukti: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("dedukti_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default())
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
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

    #[tokio::test]
    async fn parse_string_stores_source_in_metadata() {
        let backend = DeduktiBackend::new(ProverConfig::default());
        let src = "#NAME nat.\nNat : Type.\nz : Nat.\n";
        let state = backend.parse_string(src).await.unwrap();
        assert_eq!(
            state
                .metadata
                .get("dedukti_source")
                .and_then(|v| v.as_str())
                .unwrap(),
            src
        );
    }

    #[test]
    fn kind_is_dedukti() {
        let backend = DeduktiBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Dedukti);
    }
}
