// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Nunchaku — model / counter-example finder for higher-order logic.
//! Sibling to Nitpick but standalone (not Isabelle-integrated) and
//! supports a wider input format range (TPTP, Kodkod-style). Same
//! negative-class data story: corpus records are refutations, which
//! balance the otherwise positive-only proof corpus during ML training.
//! Vendor: github.com/nunchaku-inria/nunchaku

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct NunchakuBackend {
    config: ProverConfig,
}
impl NunchakuBackend {
    pub fn new(c: ProverConfig) -> Self {
        Self { config: c }
    }
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("nunchaku")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for NunchakuBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Nunchaku
    }
    async fn version(&self) -> Result<String> {
        match Command::new(self.binary()).arg("--version").output().await {
            Ok(o) if o.status.success() => {
                Ok(String::from_utf8_lossy(&o.stdout).trim().to_string())
            },
            Ok(_) => Ok("nunchaku@unavailable".into()),
            Err(_) => Ok("nunchaku@not-installed".into()),
        }
    }
    async fn parse_file(&self, p: PathBuf) -> Result<ProofState> {
        let c = super::bounded_read_proof_file(&p)
            .await
            .with_context(|| format!("Nunchaku: reading {}", p.display()))?;
        self.parse_string(&c).await
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut s = ProofState {
            goals: vec![Goal {
                id: "nunchaku-goal".into(),
                target: Term::Const(content.into()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        s.metadata.insert(
            "nunchaku_source".into(),
            serde_json::Value::String(content.into()),
        );
        Ok(s)
    }
    async fn apply_tactic(&self, s: &ProofState, t: &Tactic) -> Result<TacticResult> {
        let mut n = s.clone();
        n.proof_script.push(t.clone());
        Ok(TacticResult::Success(n))
    }
    // Same inverted semantics as Nitpick: verify_proof returns true if
    // Nunchaku found a counter-example (the input goal is shown false).
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let src: String = state
            .metadata
            .get("nunchaku_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default();
        let dir = tempfile::Builder::new()
            .prefix("echidna-nunchaku-")
            .tempdir()
            .context("Nunchaku: tempdir")?;
        let input = dir.path().join("check.nun");
        tokio::fs::write(&input, src.as_bytes())
            .await
            .context("Nunchaku: writing")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for a in &self.config.args {
            cmd.arg(a);
        }
        match cmd.output().await {
            Ok(o) => {
                let out = String::from_utf8_lossy(&o.stdout);
                Ok(
                    out.contains("SAT")
                        || out.contains("counterexample")
                        || out.contains("UNKNOWN"),
                )
            },
            Err(e) => Err(anyhow!("Nunchaku: binary not runnable: {}", e)),
        }
    }
    async fn export(&self, s: &ProofState) -> Result<String> {
        Ok(s.metadata
            .get("nunchaku_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default())
    }
    async fn suggest_tactics(&self, _: &ProofState, _: usize) -> Result<Vec<Tactic>> {
        Ok(vec![])
    }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> {
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
    fn kind_is_nunchaku() {
        assert_eq!(
            NunchakuBackend::new(ProverConfig::default()).kind(),
            ProverKind::Nunchaku
        );
    }
}
