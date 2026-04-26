// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! λProlog — higher-order logic programming with HOAS. Teyjus and Elpi
//! are the main implementations; this backend invokes whichever is on
//! PATH via the config. Complementary to Abella — both do HOAS but
//! λProlog emphasises the *specification* side where Abella adds the
//! *reasoning* side. Serves `TypeDiscipline::Nominal` alongside Abella.
//! Vendor: github.com/teyjus/teyjus or github.com/LPCIC/elpi

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct LambdaPrologBackend {
    config: ProverConfig,
}
impl LambdaPrologBackend {
    pub fn new(c: ProverConfig) -> Self {
        Self { config: c }
    }
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("tjsim")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for LambdaPrologBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::LambdaProlog
    }
    async fn version(&self) -> Result<String> {
        match Command::new(self.binary()).arg("--version").output().await {
            Ok(o) if o.status.success() => {
                Ok(String::from_utf8_lossy(&o.stdout).trim().to_string())
            },
            Ok(_) => Ok("lambda-prolog@unavailable".into()),
            Err(_) => Ok("lambda-prolog@not-installed".into()),
        }
    }
    async fn parse_file(&self, p: PathBuf) -> Result<ProofState> {
        let c = super::bounded_read_proof_file(&p)
            .await
            .with_context(|| format!("λProlog: reading {}", p.display()))?;
        self.parse_string(&c).await
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut s = ProofState {
            goals: vec![Goal {
                id: "lambdaprolog-file".into(),
                target: Term::Const(content.into()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        s.metadata.insert(
            "lambda_prolog_source".into(),
            serde_json::Value::String(content.into()),
        );
        Ok(s)
    }
    async fn apply_tactic(&self, s: &ProofState, t: &Tactic) -> Result<TacticResult> {
        let mut n = s.clone();
        n.proof_script.push(t.clone());
        Ok(TacticResult::Success(n))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let src: String = state
            .metadata
            .get("lambda_prolog_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default();
        let dir = tempfile::Builder::new()
            .prefix("echidna-lambda-prolog-")
            .tempdir()
            .context("λProlog: tempdir")?;
        let input = dir.path().join("check.mod");
        tokio::fs::write(&input, src.as_bytes())
            .await
            .context("λProlog: writing")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for a in &self.config.args {
            cmd.arg(a);
        }
        match cmd.output().await {
            Ok(o) if o.status.success() => Ok(true),
            Ok(_) => Ok(false),
            Err(e) => Err(anyhow!("λProlog: binary not runnable: {}", e)),
        }
    }
    async fn export(&self, s: &ProofState) -> Result<String> {
        Ok(s.metadata
            .get("lambda_prolog_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default())
    }
    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // λProlog (e.g. Teyjus, ELPI) is a higher-order logic programming
        // language; proofs are goal-directed search programs. Canonical
        // Prolog-style proof steps follow.
        let tactics = vec![
            Tactic::Custom {
                prover: "lambda_prolog".to_string(),
                command: "apply".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lambda_prolog".to_string(),
                command: "backchain".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lambda_prolog".to_string(),
                command: "cases".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lambda_prolog".to_string(),
                command: "intros".to_string(),
                args: vec![],
            },
            Tactic::Assumption,
            Tactic::Simplify,
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // λProlog has no built-in theorem-search mechanism.
        Ok(vec![])
    }
    fn config(&self) -> &ProverConfig {
        &self.config
    }
    fn set_config(&mut self, c: ProverConfig) {
        self.config = c;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn kind_is_lambda_prolog() {
        assert_eq!(
            LambdaPrologBackend::new(ProverConfig::default()).kind(),
            ProverKind::LambdaProlog
        );
    }
}
