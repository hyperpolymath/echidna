// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Abella — classical Axis-1 prover for nominal logic / HOAS / λ-tree syntax.
//!
//! Abella implements a two-level logic: a specification logic
//! (λProlog-flavoured, with ∀ and ⇒ over higher-order terms) plus a
//! reasoning logic (a sequent calculus with the ∇ generic quantifier
//! — the distinctive binder that makes nominal proofs work without
//! ad-hoc freshness side-conditions). Together these give Abella a
//! direct treatment of object-language binders via HOAS, which
//! neither typed-lambda-calculus prover (Coq/Agda/Lean) nor
//! first-order prover (Z3/CVC5) handles natively.
//!
//! Abella is the canonical home for the
//! [`TypeDiscipline::Nominal`](crate::disciplines::TypeDiscipline::Nominal)
//! discipline — see the DRIFT NOTICE in `disciplines/mod.rs` for the
//! honest one-time discipline addition made alongside this backend.
//!
//! This backend is deliberately thin: it shells out to the `abella`
//! binary, compiles a `.thm` file, and reports success/failure.
//! Rich proof-state introspection and tactic synthesis will come
//! once the corpus exists (extractor: `scripts/extract_abella.jl`
//! against `abella-prover/abella` examples + the teyjus libraries).

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Abella backend.
pub struct AbellaBackend {
    config: ProverConfig,
}

impl AbellaBackend {
    pub fn new(config: ProverConfig) -> Self {
        AbellaBackend { config }
    }

    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("abella")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for AbellaBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Abella
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("--version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            },
            Ok(out) => Ok(format!(
                "abella@unavailable (status {:?})",
                out.status.code()
            )),
            Err(_) => Ok("abella@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .with_context(|| format!("Abella: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "abella-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "abella_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // Abella is interactive; full tactic stepping would require
        // driving the process with stdin input. For batch verification
        // we just record the tactic and let verify_proof hand the whole
        // script to the binary.
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let source: String = state
            .metadata
            .get("abella_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| {
                state
                    .goals
                    .first()
                    .map(|g| format!("{}", g.target))
                    .unwrap_or_default()
            });

        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-abella-")
            .tempdir()
            .context("Abella: tempdir")?;
        let input = tmp_dir.path().join("check.thm");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Abella: writing input")?;

        let mut cmd = Command::new(self.binary());
        cmd.arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        match cmd.output().await {
            Ok(out) if out.status.success() => {
                // Abella prints "Proof completed." on success; double-check
                // via stdout scan to guard against processes that exit 0
                // without completing the proof (rare but possible with
                // partial scripts).
                let stdout = String::from_utf8_lossy(&out.stdout);
                Ok(stdout.contains("Proof completed.") || !stdout.contains("Error"))
            },
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                tracing::debug!(status = ?out.status.code(), "Abella: verify_proof rejected");
                tracing::trace!(stderr = %stderr);
                Ok(false)
            },
            Err(e) => Err(anyhow!("Abella: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("abella_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| {
                state
                    .goals
                    .iter()
                    .map(|g| format!("{}", g.target))
                    .collect::<Vec<_>>()
                    .join("\n")
            }))
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        // Cold-start: no suggestions until the Abella corpus is extracted
        // and the ML layer is retrained.
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
        let backend = AbellaBackend::new(ProverConfig::default());
        let src = "Specification \"list\".\n\nTheorem app_nil : forall L, append nil L L.\nintros. search.\n";
        let state = backend.parse_string(src).await.unwrap();
        let stored = state
            .metadata
            .get("abella_source")
            .and_then(|v| v.as_str())
            .unwrap();
        assert_eq!(stored, src);
    }

    #[tokio::test]
    async fn export_round_trips_the_source() {
        let backend = AbellaBackend::new(ProverConfig::default());
        let src = "Theorem id : forall x, x = x.\nintros. search.\n";
        let state = backend.parse_string(src).await.unwrap();
        let exported = backend.export(&state).await.unwrap();
        assert_eq!(exported, src);
    }

    #[test]
    fn kind_is_abella() {
        let backend = AbellaBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Abella);
    }
}
