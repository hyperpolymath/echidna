// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! MleanCoP backend — connection-method prover for classical
//! first-order logic with equality.
//!
//! MleanCoP extends leanCoP with native equality handling via term
//! rewriting and lemma management.  It is the classical-FOL member
//! of the leanCoP family that ECHIDNA carries (alongside ileanCoP
//! for intuitionistic logic and nanoCoP for the lean-kernel
//! variant).
//!
//! ## Why this backend exists
//!
//! Connection-method provers explore the matrix-character of a
//! formula directly rather than going through resolution.  On
//! intuitionistic and modal logics the connection-method tractably
//! produces small kernels that resolution-based ATPs cannot match.
//! Even on classical FOL, MleanCoP is competitive on certain CASC
//! benchmark classes — and it produces a *connection proof* (a
//! matrix proof object) that resolution provers do not.
//!
//! ## Input format
//!
//! TPTP CNF or FOF.  Same as MetiTarski / iProver.
//!
//! ## CLI invocation
//!
//! `swipl -g "leancop:prove('<input>.p', 'auto')" -t halt -- -input <file>`
//! or, with stdin:
//! `swipl -s mleancop.pl -g "prove_input" -t halt`
//!
//! For maximum portability we go through stdin: write TPTP to the
//! Prolog process's stdin and let it read via `see/1` / `read/1`.
//!
//! ## Output parsing
//!
//! See `connection_method::parse_szs_or_native` — handles both the
//! TPTP SZS markers and leanCoP's native `matrix proof found` /
//! `no proof` lines.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 2 (classical leanCoP kernel is
//! small but unverified).  Complexity 3.

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

/// MleanCoP backend.
pub struct MleanCopBackend {
    config: ProverConfig,
}

impl MleanCopBackend {
    pub fn new(config: ProverConfig) -> Self {
        MleanCopBackend { config }
    }
}

#[async_trait]
impl ProverBackend for MleanCopBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::MleanCoP
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run mleancop --version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.lines().next().unwrap_or("mleancop").trim().to_string())
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
            "MleanCoP is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tptp = connection_method::to_tptp(state);
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn mleancop")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open mleancop stdin"))?;
            stdin
                .write_all(tptp.as_bytes())
                .await
                .context("Failed to write to mleancop stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for mleancop")?;
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
    fn test_mleancop_kind() {
        let config = ProverConfig::default();
        let backend = MleanCopBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::MleanCoP);
    }

    #[tokio::test]
    async fn test_mleancop_parse_string_extracts_axioms_and_goal() {
        let config = ProverConfig::default();
        let backend = MleanCopBackend::new(config);
        let tptp = "fof(a1, axiom, p | ~ p).\nfof(conj, conjecture, p).\n";
        let state = backend.parse_string(tptp).await.expect("parse_string failed");
        assert_eq!(state.context.axioms.len(), 1);
        assert_eq!(state.goals.len(), 1);
    }

    #[test]
    fn test_mleancop_export_produces_tptp() {
        let config = ProverConfig::default();
        let _backend = MleanCopBackend::new(config);
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("p".to_string()),
            hypotheses: vec![],
        });
        let tptp = connection_method::to_tptp(&state);
        assert!(tptp.contains("fof(conjecture, conjecture, p)."));
    }
}
