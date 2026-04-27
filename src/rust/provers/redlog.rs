// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Redlog backend — REDUCE-CAS frontend for real algebra
//!
//! Redlog is a logical extension of REDUCE that provides quantifier
//! elimination, optimisation, and decision procedures over real
//! and integer arithmetic, using CAD and virtual substitution.
//!
//! ## Why this backend exists
//!
//! Redlog is the second CAD-class backend (alongside QEPCAD-B).  It
//! has different strengths: virtual substitution beats CAD on
//! formulae with low-degree polynomials, and Redlog supports the
//! `ofsf` (ordered field standard form) and `dvfsf` (discretely
//! valued field) contexts that QEPCAD-B does not.  The pair gives
//! ECHIDNA a cross-checkable real-algebra portfolio.
//!
//! ## Input format
//!
//! Redlog runs inside REDUCE.  A typical session:
//!
//! ```text
//! load_package redlog;
//! rlset reals;
//! formula := all(x, x^2 + 1 > 0);
//! rlqe formula;
//! ;end;
//! ```
//!
//! Statements are terminated with `;` (echo) or `$` (silent).  We
//! always use `;` so the result lands on stdout.
//!
//! ## Output parsing
//!
//! `rlqe` returns either a boolean (`true` / `false`) or a
//! quantifier-free residual formula.  The Redlog/REDUCE printer
//! puts the result on its own line with a leading number:
//!
//! ```text
//! 4: true
//! ```
//!
//! We strip the "N: " prefix and classify the remainder.
//!
//! ## CLI invocation
//!
//! Either `redcsl` (CSL build) or `redpsl` (PSL build) accepts the
//! Redlog input on stdin.  Default config assumes `redcsl` is on
//! the path; override via `ProverConfig::executable`.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 2 (parallel to QEPCAD).  Complexity
//! 3 (Redlog's virtual substitution is faster than CAD on many
//! inputs, but worst-case still doubly-exponential).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Redlog backend (REDUCE-CAS frontend for real algebra).
pub struct RedlogBackend {
    config: ProverConfig,
}

impl RedlogBackend {
    pub fn new(config: ProverConfig) -> Self {
        RedlogBackend { config }
    }

    /// Convert a `ProofState` into a Redlog session script.
    fn to_redlog(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        s.push_str("load_package redlog;\n");

        // Default to the reals context; override via metadata.
        let context = state
            .metadata
            .get("redlog_context")
            .and_then(|v| v.as_str())
            .unwrap_or("reals");
        s.push_str(&format!("rlset {};\n", context));

        // Build the formula: each axiom implies the goal.
        let mut formula = String::new();
        for axiom in &state.context.axioms {
            formula.push_str(&format!("({}) impl ", axiom));
        }
        if let Some(goal) = state.goals.first() {
            formula.push_str(&goal.target.to_string());
        } else {
            formula.push_str("true");
        }
        s.push_str(&format!("formula := {};\n", formula));

        // Apply quantifier elimination.
        s.push_str("rlqe formula;\n");
        s.push_str(";end;\n");
        Ok(s)
    }

    /// Parse Redlog output to determine proof success.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Redlog prints lines like "4: true" or "5: false" or
        // "5: x > 0 and y > 0" (residual formula).
        for raw_line in output.lines() {
            let line = raw_line.trim();
            // Strip a leading "N:" if present.
            let payload = if let Some(idx) = line.find(':') {
                line[idx + 1..].trim()
            } else {
                line
            };
            if payload.eq_ignore_ascii_case("true") {
                return Ok(true);
            }
            if payload.eq_ignore_ascii_case("false") {
                return Ok(false);
            }
        }

        let lower = output.to_ascii_lowercase();
        if lower.contains("error") || lower.contains("***") {
            return Err(anyhow::anyhow!(
                "Redlog error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }
        // No clean true/false means residual formula or inconclusive →
        // treat as not-closed.
        Ok(false)
    }
}

#[async_trait]
impl ProverBackend for RedlogBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Redlog
    }

    async fn version(&self) -> Result<String> {
        // REDUCE prints its banner on startup; capture the first
        // non-empty stdout line.
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn redcsl/redpsl")?;
        if let Some(stdin) = child.stdin.as_mut() {
            let _ = stdin.write_all(b";end;\n").await;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for redcsl/redpsl")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let first = stdout
            .lines()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("redlog")
            .trim()
            .to_string();
        Ok(first)
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read Redlog file")?;
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
            "redlog_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        // Heuristic: pull the right-hand side of `formula := <expr>;`.
        for line in content.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("formula") {
                let rest = rest.trim_start_matches(|c: char| c.is_whitespace() || c == ':' || c == '=');
                let rest = rest.trim_end_matches(|c: char| c.is_whitespace() || c == ';');
                if !rest.is_empty() {
                    state.goals.push(Goal {
                        id: "goal_0".to_string(),
                        target: Term::Const(rest.to_string()),
                        hypotheses: vec![],
                    });
                    break;
                }
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Redlog is a fully automated decision procedure — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let script = self.to_redlog(state)?;
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn redcsl/redpsl")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open redcsl stdin"))?;
            stdin
                .write_all(script.as_bytes())
                .await
                .context("Failed to write Redlog script")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for redcsl/redpsl")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_redlog(state)
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
    fn test_redlog_kind() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Redlog);
    }

    #[test]
    fn test_redlog_to_redlog_basic() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("all(x, x^2 + 1 > 0)".to_string()),
            hypotheses: vec![],
        });
        let script = backend.to_redlog(&state).expect("to_redlog failed");
        assert!(script.contains("load_package redlog"));
        assert!(script.contains("rlset reals"));
        assert!(script.contains("formula := all(x, x^2 + 1 > 0);"));
        assert!(script.contains("rlqe formula"));
    }

    #[test]
    fn test_redlog_to_redlog_no_goal_emits_true() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let state = ProofState::default();
        let script = backend.to_redlog(&state).expect("to_redlog failed");
        assert!(script.contains("formula := true;"));
    }

    #[test]
    fn test_redlog_parse_result_true() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let out = "1: rlqe loaded\n2: reals\n3: formula\n4: true\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(r);
    }

    #[test]
    fn test_redlog_parse_result_false() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let out = "4: false\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(!r);
    }

    #[test]
    fn test_redlog_parse_result_residual() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let out = "5: x > 0 and y > 0\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(!r);  // residual formula → not closed
    }

    #[test]
    fn test_redlog_parse_result_error() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let out = "***** Error: package not found\n";
        assert!(backend.parse_result(out).is_err());
    }

    #[tokio::test]
    async fn test_redlog_parse_string_extracts_formula() {
        let config = ProverConfig::default();
        let backend = RedlogBackend::new(config);
        let input = "load_package redlog;\nrlset reals;\nformula := x > 0;\nrlqe formula;\n";
        let state = backend.parse_string(input).await.expect("parse_string failed");
        assert_eq!(state.goals.len(), 1);
    }
}
