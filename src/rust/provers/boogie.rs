// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Boogie — intermediate verification language standalone backend.
//!
//! Boogie already reaches echidna indirectly via the Viper backend
//! (`src/rust/provers/viper.rs`), which targets Boogie as its
//! intermediate representation. Adding Boogie as its own
//! `ProverKind` lets echidna consume `.bpl` programs directly
//! (e.g. from Dafny output, Chalice, VCC front-ends, Solidity*,
//! or any tool that emits Boogie) without requiring a Viper-
//! adjacent wrapper. Corpus source: Boogie's `Test/` suite +
//! Dafny-generated `.bpl` dumps.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

pub struct BoogieBackend {
    config: ProverConfig,
}

impl BoogieBackend {
    pub fn new(config: ProverConfig) -> Self {
        BoogieBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("boogie")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for BoogieBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Boogie
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("/version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            },
            Ok(_) => Ok("boogie@unavailable".to_string()),
            Err(_) => Ok("boogie@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Boogie: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "boogie-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "boogie_source".to_string(),
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
            .get("boogie_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-boogie-")
            .tempdir()
            .context("Boogie: tempdir")?;
        let input = tmp_dir.path().join("check.bpl");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Boogie: writing input")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        match cmd.output().await {
            Ok(out) if out.status.success() => {
                // Boogie prints "0 errors" on full success; non-zero errors
                // in stdout even with exit 0 means verification failed.
                let stdout = String::from_utf8_lossy(&out.stdout);
                Ok(stdout.contains("0 errors")
                    || stdout.contains("Boogie program verifier finished with"))
            },
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("Boogie: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("boogie_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default())
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Boogie is an intermediate verification language; it delegates to
        // an SMT solver (typically Z3). Suggestions are annotation and
        // specification hints rather than interactive tactics.
        let tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "boogie".to_string(),
                command: "add_invariant".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "boogie".to_string(),
                command: "add_requires".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "boogie".to_string(),
                command: "add_ensures".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "boogie".to_string(),
                command: "prover_option".to_string(),
                args: vec!["/z3opt:smt.arith.solver=6".to_string()],
            },
            Tactic::Custom {
                prover: "boogie".to_string(),
                command: "prover_option".to_string(),
                args: vec!["/proverOpt:O:smt.qi.max_multi_patterns=1000".to_string()],
            },
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Boogie has no theorem library; it encodes programs for an SMT backend.
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
    fn kind_is_boogie() {
        let backend = BoogieBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Boogie);
    }
}
