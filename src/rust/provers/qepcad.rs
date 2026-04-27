// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! QEPCAD-B backend — cylindrical algebraic decomposition over the
//! reals.
//!
//! QEPCAD-B (Quantifier Elimination by Partial Cylindrical Algebraic
//! Decomposition, B variant) decides quantified statements over the
//! real-closed field by computing a CAD of the polynomial system and
//! reading off the truth value or the equivalent quantifier-free
//! formula.
//!
//! ## Why this backend exists
//!
//! Real quantifier elimination is undecidable for full first-order
//! arithmetic but decidable over the real-closed field via CAD.
//! QEPCAD-B is the canonical CAD implementation; it complements
//! Redlog (also a CAD/QE engine, but built on Reduce CAS) and gives
//! ECHIDNA two independent CAD oracles for cross-checking.
//!
//! ## Input format
//!
//! QEPCAD-B accepts an interactive script with structured lines:
//!
//! ```text
//! [ <description> ]
//! (<var1>,<var2>,...)
//! <num_free_vars>
//! (Q1 x1)(Q2 x2)...[ <formula> ].
//! finish
//! ```
//!
//! - `[ <description> ]` is a free-text label.
//! - `(<var1>,...)` declares the variable order (matters for CAD
//!   complexity).
//! - `<num_free_vars>` is the count of unquantified variables; for
//!   sentence problems this is `0`.
//! - The next line is the prefixed formula; quantifier blocks `(E x)`
//!   / `(A x)` introduce existentials / universals.  The formula
//!   uses `/\`, `\/`, `~`, `==>`, `<==>` for connectives.
//! - `finish` flushes the engine.
//!
//! ## Output parsing
//!
//! On success QEPCAD-B emits:
//!
//! ```text
//! An equivalent quantifier-free formula:
//!
//! TRUE
//! ```
//!
//! (or `FALSE`, or a residual formula).  We treat `TRUE` as
//! `verify_proof = Ok(true)`, `FALSE` as `Ok(false)`, residual
//! formulae as `Ok(false)` (the goal is not closed), and parse
//! errors / "unable to compute" as `Err`.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 2 (CAD result is sound but the
//! implementation has no machine-checked certificate).  Complexity
//! 4 (CAD is doubly-exponential in the variable count; honour the
//! timeout).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// QEPCAD-B backend for real-closed-field quantifier elimination.
pub struct QepcadBackend {
    config: ProverConfig,
}

impl QepcadBackend {
    pub fn new(config: ProverConfig) -> Self {
        QepcadBackend { config }
    }

    /// Convert a `ProofState` into a QEPCAD-B input script.
    ///
    /// We treat the goal as a sentence (no free variables) and emit
    /// every axiom as a conjunctive premise.  The variable order
    /// is read from a `qepcad_var_order` metadata key if set;
    /// otherwise we synthesise a default `(x)` ordering, which
    /// QEPCAD-B will refuse on multi-variable problems — callers
    /// that need a real ordering must set the metadata key.
    fn to_qepcad(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        s.push_str("[ echidna problem ]\n");

        // Variable ordering — defaults to a single dummy variable.
        let var_order = state
            .metadata
            .get("qepcad_var_order")
            .and_then(|v| v.as_str())
            .unwrap_or("(x)")
            .to_string();
        s.push_str(&format!("{}\n", var_order));

        // Number of free variables.  Zero for sentence problems —
        // override via metadata if needed.
        let num_free = state
            .metadata
            .get("qepcad_num_free")
            .and_then(|v| v.as_str())
            .unwrap_or("0");
        s.push_str(&format!("{}\n", num_free));

        // Prefix axioms with implication arrows; emit goal at the end.
        let mut formula = String::new();
        for axiom in &state.context.axioms {
            formula.push_str(&format!("({}) ==> ", axiom));
        }
        if let Some(goal) = state.goals.first() {
            formula.push_str(&goal.target.to_string());
        } else {
            formula.push_str("TRUE");
        }
        s.push_str(&format!("[ {} ].\n", formula));

        s.push_str("finish\n");
        Ok(s)
    }

    /// Parse QEPCAD-B stdout to determine proof success.
    ///
    /// Returns `Ok(true)` on `TRUE`, `Ok(false)` on `FALSE` or any
    /// residual formula, and `Err` on parse errors / "unable to
    /// compute" outputs.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Find the "An equivalent quantifier-free formula:" marker
        // and look at what follows.
        let lower = output.to_ascii_lowercase();
        if lower.contains("error") || lower.contains("unable to compute") {
            return Err(anyhow::anyhow!(
                "QEPCAD-B error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        // Scan for the equivalent-formula block.
        if let Some(idx) = output.find("equivalent quantifier-free formula") {
            let after = &output[idx..];
            let upper = after.to_ascii_uppercase();
            if upper.contains("TRUE") && !upper.contains("FALSE") {
                return Ok(true);
            }
            if upper.contains("FALSE") {
                return Ok(false);
            }
            // Residual formula → goal not closed
            return Ok(false);
        }

        // Generic markers as fallback (for non-standard QEPCAD builds).
        if lower.contains("formula is true") {
            return Ok(true);
        }
        if lower.contains("formula is false") {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "QEPCAD-B output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for QepcadBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Qepcad
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run qepcad -version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.lines().next().unwrap_or("qepcad-b").trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read QEPCAD-B input file")?;
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
            "qepcad_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        // Lightweight extraction: collect the prefixed formula
        // between `[ ... ].` brackets after the variable-order line.
        let mut in_formula = false;
        let mut formula = String::new();
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with('[') && trimmed.ends_with("].") {
                formula.push_str(&trimmed[1..trimmed.len() - 2]);
                in_formula = true;
                break;
            }
        }
        if in_formula && !formula.trim().is_empty() {
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const(formula.trim().to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "QEPCAD-B is a fully automated CAD engine — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let script = self.to_qepcad(state)?;
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn qepcad")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open qepcad stdin"))?;
            stdin
                .write_all(script.as_bytes())
                .await
                .context("Failed to write to qepcad stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for qepcad")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_qepcad(state)
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
    fn test_qepcad_kind() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Qepcad);
    }

    #[test]
    fn test_qepcad_to_qepcad_basic() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let mut state = ProofState::default();
        state.context.axioms.push("x > 0".to_string());
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("(E x)[ x^2 + 1 > 0 ]".to_string()),
            hypotheses: vec![],
        });
        let script = backend.to_qepcad(&state).expect("to_qepcad failed");
        assert!(script.contains("[ echidna problem ]"));
        assert!(script.contains("finish"));
        assert!(script.contains("(E x)"));
    }

    #[test]
    fn test_qepcad_to_qepcad_no_goal_emits_true() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let state = ProofState::default();
        let script = backend.to_qepcad(&state).expect("to_qepcad failed");
        assert!(script.contains("TRUE"));
    }

    #[test]
    fn test_qepcad_parse_result_true() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let out = "An equivalent quantifier-free formula:\n\nTRUE\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(r);
    }

    #[test]
    fn test_qepcad_parse_result_false() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let out = "An equivalent quantifier-free formula:\n\nFALSE\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(!r);
    }

    #[test]
    fn test_qepcad_parse_result_residual() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let out = "An equivalent quantifier-free formula:\n\nx > 0\n";
        let r = backend.parse_result(out).expect("parse_result failed");
        assert!(!r);  // residual formula → goal not closed
    }

    #[test]
    fn test_qepcad_parse_result_error() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let out = "Error: unable to compute CAD";
        assert!(backend.parse_result(out).is_err());
    }

    #[tokio::test]
    async fn test_qepcad_parse_string_extracts_formula() {
        let config = ProverConfig::default();
        let backend = QepcadBackend::new(config);
        let input = "[ test ]\n(x)\n0\n[ (E x)[ x > 0 ] ].\nfinish\n";
        let state = backend.parse_string(input).await.expect("parse_string failed");
        assert_eq!(state.goals.len(), 1);
    }
}
