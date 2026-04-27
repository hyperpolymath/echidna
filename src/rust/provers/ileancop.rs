// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ileanCoP backend — connection-method prover for intuitionistic
//! first-order logic.
//!
//! ileanCoP is the intuitionistic-logic member of the leanCoP family.
//! It uses the *intuitionistic* connection method (with
//! prefix-checking to enforce constructive validity) rather than the
//! classical version used by MleanCoP.
//!
//! ## Why this backend exists
//!
//! Constructive provers (Coq, Agda, Lean, Idris2) live in
//! intuitionistic logic.  ileanCoP gives ECHIDNA a *fully automated*
//! intuitionistic ATP that complements those interactive provers —
//! useful for offloading the trivial-but-tedious lemmas that arise
//! during constructive proof development.
//!
//! ## Input format
//!
//! TPTP fof, same as MleanCoP.  The "intuitionistic" interpretation
//! is enforced by the prover — the input syntax is unchanged.
//!
//! ## CLI invocation
//!
//! `swipl -g "ileancop:prove(...)"` or via stdin like MleanCoP.
//!
//! ## Output parsing
//!
//! Same SZS / native markers as MleanCoP — see
//! `connection_method::parse_szs_or_native`.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 3 (intuitionistic kernel is *small*
//! and well-studied — connection-method gives a checkable matrix
//! proof object with a 30-line core).  Complexity 3.

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::connection_method;
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// ileanCoP backend.
pub struct IleanCopBackend {
    config: ProverConfig,
}

impl IleanCopBackend {
    pub fn new(config: ProverConfig) -> Self {
        IleanCopBackend { config }
    }
}

#[async_trait]
impl ProverBackend for IleanCopBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::IleanCoP
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run ileancop --version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.lines().next().unwrap_or("ileancop").trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read TPTP input")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "tptp_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') {
                continue;
            }
            if line.starts_with("fof(") {
                if let Some(formula) = line.split(',').nth(2) {
                    let formula = formula.trim_end_matches(").").trim();
                    if line.contains(", axiom,") {
                        state.context.axioms.push(formula.to_string());
                    } else if line.contains(", conjecture,") {
                        state.goals.push(Goal {
                            id: format!("goal_{}", state.goals.len()),
                            target: Term::Const(formula.to_string()),
                            hypotheses: vec![],
                        });
                    }
                }
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "ileanCoP is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp = connection_method::to_tptp(state);
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn ileancop")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open ileancop stdin"))?;
            stdin
                .write_all(tptp.as_bytes())
                .await
                .context("Failed to write to ileancop stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for ileancop")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        connection_method::parse_szs_or_native(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(connection_method::to_tptp(state))
    }

    async fn suggest_tactics(
        &self,
        _state: &ProofState,
        _limit: usize,
    ) -> Result<Vec<Tactic>> {
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
    fn test_ileancop_kind() {
        let config = ProverConfig::default();
        let backend = IleanCopBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::IleanCoP);
    }

    #[tokio::test]
    async fn test_ileancop_parse_string_extracts_axioms_and_goal() {
        let config = ProverConfig::default();
        let backend = IleanCopBackend::new(config);
        let tptp = "fof(a1, axiom, p => p).\nfof(conj, conjecture, p => p).\n";
        let state = backend.parse_string(tptp).await.expect("parse_string failed");
        assert_eq!(state.context.axioms.len(), 1);
        assert_eq!(state.goals.len(), 1);
    }

    #[test]
    fn test_ileancop_export_emits_conjecture() {
        let config = ProverConfig::default();
        let _backend = IleanCopBackend::new(config);
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("p => p".to_string()),
            hypotheses: vec![],
        });
        let tptp = connection_method::to_tptp(&state);
        assert!(tptp.contains("fof(conjecture, conjecture, p => p)."));
    }
}
