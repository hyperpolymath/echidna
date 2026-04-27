// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! CryptoVerif backend — automatic prover for cryptographic protocols
//! in the computational model.
//!
//! CryptoVerif is the **automatic** counterpart to EasyCrypt's
//! interactive proof assistant: it produces concrete-security proofs
//! by automated game-hopping using a built-in indistinguishability
//! library.  It was used to prove the formal security of TLS 1.3,
//! Signal, WireGuard, and Kerberos.
//!
//! ## Why this backend exists
//!
//! EasyCrypt produces interactive proofs with concrete-security
//! bounds.  CryptoVerif produces *automated* proofs in the same model.
//! Together they cover the computational-crypto verification space.
//! ECHIDNA already has Tamarin and ProVerif (symbolic) — adding both
//! computational tools gives us the four-corner crypto-verification
//! matrix: symbolic-automatic (ProVerif), symbolic-interactive
//! (Tamarin), computational-interactive (EasyCrypt),
//! computational-automatic (CryptoVerif).
//!
//! ## Input format
//!
//! `.ocv` — CryptoVerif source (recommended modern syntax).
//! `.cv`  — legacy format (still supported by upstream).
//!
//! ## CLI invocation
//!
//! `cryptoverif -in <ocv-file> -out <result-dir>` for full automation.
//! `cryptoverif -interactive` for hand-driven game-hopping.
//!
//! ## Output parsing
//!
//! CryptoVerif emits per-game status with a final verdict line:
//!
//! - `RESULT Proved <event-or-property>`
//! - `RESULT Could not prove ...`
//! - `Cannot prove ...` (failure mid-script)
//!
//! ## Integration tier
//!
//! Tier-5l / Phase-4.  Trust tier 3 (small game-hopping engine,
//! peer-reviewed, used for TLS 1.3 / Signal proofs).  Complexity 4
//! (probabilistic process calculi + indistinguishability library +
//! cryptographic-game search).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// CryptoVerif backend for automated computational crypto proofs.
pub struct CryptoVerifBackend {
    config: ProverConfig,
}

impl CryptoVerifBackend {
    pub fn new(config: ProverConfig) -> Self {
        CryptoVerifBackend { config }
    }

    /// Render a `ProofState` into a minimal CryptoVerif `.ocv` file.
    ///
    /// Each axiom is emitted as a `def` declaration; the goal is
    /// emitted as the `query` line that drives the prover.
    fn to_ocv(state: &ProofState) -> String {
        let mut ocv = String::new();
        ocv.push_str("(* SPDX-License-Identifier: PMPL-1.0-or-later *)\n");
        ocv.push_str("(* CryptoVerif input synthesised by ECHIDNA *)\n\n");
        for axiom in &state.context.axioms {
            ocv.push_str(&format!("def {}.\n", axiom));
        }
        if let Some(goal) = state.goals.first() {
            ocv.push_str(&format!("\nquery {}.\n", goal.target));
        }
        ocv.push_str("\nprocess 0\n");
        ocv
    }

    /// Parse CryptoVerif's stdout to a boolean verdict.
    fn parse_result(output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        let positive = [
            "result proved",
            "all queries proved",
            "successfully proved",
            "[ok] proof complete",
        ];
        let negative = [
            "could not prove",
            "cannot prove",
            "result not proved",
            "result rand_failure",
            "[error]",
        ];
        if positive.iter().any(|m| lower.contains(m)) {
            return Ok(true);
        }
        if negative.iter().any(|m| lower.contains(m)) {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "CryptoVerif output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for CryptoVerifBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::CryptoVerif
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run cryptoverif -version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("cryptoverif").to_string()
        } else {
            stderr.lines().next().unwrap_or("cryptoverif").to_string()
        };
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read .ocv file")?;
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
            "ocv_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("(*") {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("def ") {
                let body = rest.trim_end_matches('.').trim();
                if !body.is_empty() {
                    state.context.axioms.push(body.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("query ") {
                let body = rest.trim_end_matches('.').trim();
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(body.to_string()),
                    hypotheses: vec![],
                });
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "CryptoVerif is automation-first; interactive game-hopping is out of band"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let ocv = Self::to_ocv(state);
        let mut child = Command::new(&self.config.executable)
            .arg("-in")
            .arg("/dev/stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn cryptoverif")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open cryptoverif stdin"))?;
            stdin
                .write_all(ocv.as_bytes())
                .await
                .context("Failed to write to cryptoverif stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for cryptoverif")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Self::parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(Self::to_ocv(state))
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
    fn test_cryptoverif_kind() {
        let config = ProverConfig::default();
        let backend = CryptoVerifBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::CryptoVerif);
    }

    #[test]
    fn test_cryptoverif_to_ocv_emits_query() {
        let mut state = ProofState::default();
        state.context.axioms.push("MAC_secure".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("event(authenticated(m)) ==> exists s. signed(s, m)".to_string()),
            hypotheses: vec![],
        });
        let ocv = CryptoVerifBackend::to_ocv(&state);
        assert!(ocv.contains("def MAC_secure"));
        assert!(ocv.contains("query event(authenticated(m))"));
        assert!(ocv.contains("process 0"));
    }

    #[test]
    fn test_cryptoverif_parse_result_proved() {
        assert!(CryptoVerifBackend::parse_result("RESULT Proved authentication").expect("parse"));
    }

    #[test]
    fn test_cryptoverif_parse_result_could_not_prove() {
        assert!(!CryptoVerifBackend::parse_result("RESULT Could not prove confidentiality")
            .expect("parse"));
    }

    #[test]
    fn test_cryptoverif_parse_result_silence_errors() {
        assert!(CryptoVerifBackend::parse_result("warning: nothing").is_err());
    }

    #[tokio::test]
    async fn test_cryptoverif_parse_string_extracts_def_and_query() {
        let config = ProverConfig::default();
        let backend = CryptoVerifBackend::new(config);
        let ocv = "def MAC_secure.\nquery event(auth(m)) ==> sender(m).\n";
        let state = backend.parse_string(ocv).await.expect("parse_string");
        assert_eq!(state.context.axioms.len(), 1);
        assert_eq!(state.goals.len(), 1);
    }
}
