// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Cameleer — OCaml front-end for Why3.
//!
//! Cameleer lets OCaml programs be annotated with GOSPEL (Generic
//! OCaml Specification Language) contracts and transpiled to WhyML
//! for verification via Why3. Conceptually it is a thin pipeline
//! wrapper: the real proof obligations land in Why3's solver fleet.
//! Worth exposing as its own `ProverKind` because:
//!   - the source format (.ml with GOSPEL comments) is distinct
//!     from every other prover's input
//!   - the OCaml-proofs niche is a domain none of the other backends
//!     cover directly
//!   - port-pairs between Cameleer-verified OCaml and F* or Dafny
//!     proofs of the same property give the Phase 5 Arbiter more
//!     cross-language evidence

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

pub struct CameleerBackend {
    config: ProverConfig,
}

impl CameleerBackend {
    pub fn new(config: ProverConfig) -> Self {
        CameleerBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("cameleer")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for CameleerBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Cameleer
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("--version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            },
            Ok(_) => Ok("cameleer@unavailable".to_string()),
            Err(_) => Ok("cameleer@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Cameleer: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "cameleer-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "cameleer_source".to_string(),
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
            .get("cameleer_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-cameleer-")
            .tempdir()
            .context("Cameleer: tempdir")?;
        let input = tmp_dir.path().join("check.ml");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Cameleer: writing input")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("Cameleer: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("cameleer_source")
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

    #[test]
    fn kind_is_cameleer() {
        let backend = CameleerBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Cameleer);
    }

    #[tokio::test]
    async fn parse_string_stashes_source() {
        let backend = CameleerBackend::new(ProverConfig::default());
        let src = "let id x = x\n(*@ ensures result = x *)\n";
        let state = backend.parse_string(src).await.unwrap();
        assert_eq!(
            state
                .metadata
                .get("cameleer_source")
                .and_then(|v| v.as_str())
                .unwrap(),
            src
        );
    }
}
