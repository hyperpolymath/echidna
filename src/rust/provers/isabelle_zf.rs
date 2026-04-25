// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Isabelle/ZF — Isabelle with the Zermelo-Fraenkel set theory object
//! logic, as distinct from the default Isabelle/HOL.
//!
//! Same binary (`isabelle`) as the Isabelle/HOL backend, but a
//! different session name (`ZF` or `ZFC`) and a different object logic.
//! Separate `ProverKind` because the proof style, stdlib, and theorem
//! namespace are distinct enough that the ML policy should train on
//! them separately. Isabelle/ZF is used for set-theoretic work that
//! does not sit naturally in HOL's typed discipline — a useful foil
//! to the arbiter's polymorphism-heavy default expectations.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

pub struct IsabelleZfBackend {
    config: ProverConfig,
}

impl IsabelleZfBackend {
    pub fn new(config: ProverConfig) -> Self {
        IsabelleZfBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("isabelle")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for IsabelleZfBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::IsabelleZF
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("version").output().await;
        match output {
            Ok(out) if out.status.success() => Ok(format!(
                "{}-ZF",
                String::from_utf8_lossy(&out.stdout).trim()
            )),
            Ok(_) => Ok("isabelle-zf@unavailable".to_string()),
            Err(_) => Ok("isabelle-zf@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Isabelle/ZF: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "isabelle-zf-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "isabelle_zf_source".to_string(),
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
            .get("isabelle_zf_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-isabelle-zf-")
            .tempdir()
            .context("Isabelle/ZF: tempdir")?;
        let input = tmp_dir.path().join("Check.thy");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Isabelle/ZF: writing input")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg("build")
            .arg("-d")
            .arg(tmp_dir.path())
            .arg("-l")
            .arg("ZF") // ZF object logic
            .arg("Check")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("Isabelle/ZF: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("isabelle_zf_source")
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
    fn kind_is_isabelle_zf() {
        let backend = IsabelleZfBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::IsabelleZF);
    }
}
