// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! ACL2s — sibling dialect to ACL2 with richer type annotations and
//! "session" extensions (Northeastern). Same Common-Lisp foundation
//! and same proof theory, but different binary, different default
//! libraries, and different user base. Kept as its own `ProverKind`
//! because the corpus grows separately and the default tactic
//! distributions diverge enough that an ML policy trained on ACL2
//! proofs alone won't be optimal for ACL2s and vice versa.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

pub struct Acl2sBackend {
    config: ProverConfig,
}

impl Acl2sBackend {
    pub fn new(config: ProverConfig) -> Self {
        Acl2sBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("acl2s")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for Acl2sBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::ACL2s
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("--version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            }
            Ok(_) => Ok("acl2s@unavailable".to_string()),
            Err(_) => Ok("acl2s@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .with_context(|| format!("ACL2s: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "acl2s-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "acl2s_source".to_string(),
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
            .get("acl2s_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-acl2s-")
            .tempdir()
            .context("ACL2s: tempdir")?;
        let input = tmp_dir.path().join("check.lisp");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("ACL2s: writing input")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg("-f").arg(&input).stdout(Stdio::piped()).stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("ACL2s: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("acl2s_source")
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
    fn kind_is_acl2s() {
        let backend = Acl2sBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::ACL2s);
    }
}
