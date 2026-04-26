// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Nitpick — Isabelle-integrated counter-example finder.
//!
//! Produces **refutations** rather than proofs — the distinct corpus
//! contribution is negative-class data that balances the otherwise
//! positive-class proof corpus. The value-head training signal benefits
//! from seeing both what succeeds and what's been shown to fail.
//! Invoked via `isabelle process -e "nitpick"` on a Isabelle/HOL
//! theorem that the caller wants refuted.

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct NitpickBackend {
    config: ProverConfig,
}
impl NitpickBackend {
    pub fn new(c: ProverConfig) -> Self {
        Self { config: c }
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
impl ProverBackend for NitpickBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Nitpick
    }
    async fn version(&self) -> Result<String> {
        match Command::new(self.binary()).arg("version").output().await {
            Ok(o) if o.status.success() => Ok(format!(
                "{}+nitpick",
                String::from_utf8_lossy(&o.stdout).trim()
            )),
            Ok(_) => Ok("nitpick@unavailable".into()),
            Err(_) => Ok("nitpick@not-installed".into()),
        }
    }
    async fn parse_file(&self, p: PathBuf) -> Result<ProofState> {
        let c = super::bounded_read_proof_file(&p)
            .await
            .with_context(|| format!("Nitpick: reading {}", p.display()))?;
        self.parse_string(&c).await
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut s = ProofState {
            goals: vec![Goal {
                id: "nitpick-theorem".into(),
                target: Term::Const(content.into()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        s.metadata.insert(
            "nitpick_source".into(),
            serde_json::Value::String(content.into()),
        );
        Ok(s)
    }
    async fn apply_tactic(&self, s: &ProofState, t: &Tactic) -> Result<TacticResult> {
        let mut n = s.clone();
        n.proof_script.push(t.clone());
        Ok(TacticResult::Success(n))
    }
    // verify_proof semantics inverted: returns true if Nitpick FOUND a
    // counter-example (i.e. the input theorem was successfully refuted);
    // returns false otherwise. Consumers treat Nitpick as a negative-class
    // signal — success here means the candidate theorem is known-false.
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let src: String = state
            .metadata
            .get("nitpick_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default();
        let dir = tempfile::Builder::new()
            .prefix("echidna-nitpick-")
            .tempdir()
            .context("Nitpick: tempdir")?;
        let input = dir.path().join("Check.thy");
        tokio::fs::write(&input, src.as_bytes())
            .await
            .context("Nitpick: writing")?;
        let mut cmd = Command::new(self.binary());
        cmd.arg("process")
            .arg("-e")
            .arg("nitpick")
            .arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for a in &self.config.args {
            cmd.arg(a);
        }
        match cmd.output().await {
            Ok(o) => {
                let out = String::from_utf8_lossy(&o.stdout);
                Ok(out.contains("Nitpick found a counterexample") || out.contains("Nitpicking"))
            },
            Err(e) => Err(anyhow!("Nitpick: binary not runnable: {}", e)),
        }
    }
    async fn export(&self, s: &ProofState) -> Result<String> {
        Ok(s.metadata
            .get("nitpick_source")
            .and_then(|v| v.as_str())
            .map(String::from)
            .unwrap_or_default())
    }
    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Nitpick is Isabelle's counterexample finder (based on Kodkod/SAT).
        // Its primary role is falsification, so "tactics" are configuration
        // knobs that shape the finite-model search space.
        let tactics = vec![
            Tactic::Custom {
                prover: "nitpick".to_string(),
                command: "nitpick".to_string(),
                args: vec!["[expect = genuine]".to_string()],
            },
            Tactic::Custom {
                prover: "nitpick".to_string(),
                command: "nitpick".to_string(),
                args: vec!["[card = 1-8]".to_string()],
            },
            Tactic::Custom {
                prover: "nitpick".to_string(),
                command: "nitpick".to_string(),
                args: vec!["[verbose, show_all]".to_string()],
            },
            Tactic::Custom {
                prover: "nitpick".to_string(),
                command: "nitpick".to_string(),
                args: vec!["[timeout = 120]".to_string()],
            },
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Nitpick is a counterexample finder; it does not search theorem libraries.
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
    fn kind_is_nitpick() {
        assert_eq!(
            NitpickBackend::new(ProverConfig::default()).kind(),
            ProverKind::Nitpick
        );
    }
}
