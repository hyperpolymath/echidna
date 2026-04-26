// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! AProVE (Automated Program Verification Engine) backend
//!
//! AProVE is a leading automated termination prover for term rewriting systems
//! and logic programs. It handles both TRS and XTC (XML Termination Competition)
//! formats and is regularly competitive in TERMCOMP.
//!
//! Features:
//! - Termination analysis for TRS/CTRS/Logic programs
//! - XTC and native TRS input formats
//! - Complexity analysis and certification
//! - Integration with dependency pair techniques

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{ProofState, Tactic, TacticResult};

/// AProVE termination verifier backend
pub struct AProVEBackend {
    config: ProverConfig,
}

impl AProVEBackend {
    pub fn new(config: ProverConfig) -> Self {
        AProVEBackend { config }
    }

    /// Convert proof state to TRS format
    fn to_trs(&self, state: &ProofState) -> Result<String> {
        let mut trs = String::new();
        trs.push_str("(TRS\n");

        for (i, rule) in state.context.axioms.iter().enumerate() {
            trs.push_str(&format!("  (rule {} \"{}\")\n", i, rule));
        }

        trs.push_str(")\n");
        Ok(trs)
    }

    /// Parse AProVE output to determine termination result
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("YES")
            || output.contains("Terminating")
            || output.contains("Proven")
            || output.contains("TERMINATING")
        {
            Ok(true)
        } else if output.contains("NO")
            || output.contains("Not terminating")
            || output.contains("Failed")
            || output.contains("NON-TERMINATING")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "AProVE inconclusive or error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for AProVEBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::AProVE
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run aprove --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let version = if !stderr.is_empty() {
            stderr.lines().next().unwrap_or("unknown").to_string()
        } else {
            stdout.lines().next().unwrap_or("unknown").to_string()
        };

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read proof file")?;
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
            "aprove_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') || line.starts_with(';') {
                continue;
            }

            if line.starts_with("(rule") {
                state.context.axioms.push(line.to_string());
            }
        }

        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "AProVE is a fully automated termination prover - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let trs = self.to_trs(state)?;
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn aprove")?;

        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open aprove stdin"))?;
            stdin
                .write_all(trs.as_bytes())
                .await
                .context("Failed to write to aprove stdin")?;
        }

        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for aprove")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_trs(state)
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
    fn test_aprove_kind() {
        let config = ProverConfig::default();
        let backend = AProVEBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::AProVE);
    }

    #[test]
    fn test_aprove_to_trs() {
        let config = ProverConfig::default();
        let backend = AProVEBackend::new(config);

        let state = ProofState::default();
        let trs = backend.to_trs(&state).expect("to_trs failed");
        assert!(trs.contains("(TRS"));
        assert!(trs.contains(")"));
    }

    #[test]
    fn test_aprove_parse_result_yes() {
        let config = ProverConfig::default();
        let backend = AProVEBackend::new(config);

        let output = "YES\nTerminating";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(result);
    }

    #[test]
    fn test_aprove_parse_result_no() {
        let config = ProverConfig::default();
        let backend = AProVEBackend::new(config);

        let output = "NO\nNot terminating";
        let result = backend.parse_result(output).expect("parse_result failed");
        assert!(!result);
    }

}
