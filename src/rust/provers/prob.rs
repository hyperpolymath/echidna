// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ProB backend — animator and constraint-based model checker for B,
//! Event-B, Z, TLA+, and Alloy.
//!
//! ProB is the de-facto reference tool for the B-method ecosystem.
//! It performs:
//!
//! - Constraint-based static / dynamic checking (deadlock, invariant)
//! - Bounded model checking via SAT
//! - Refinement checking against an abstract spec
//! - Animation / simulation for spec validation
//!
//! ## Why this backend exists
//!
//! Event-B and the B-method are the lingua franca of formal-methods
//! work in railway / metro signalling, satellite control, and
//! safety-critical software in regulated industries.  No other prover
//! in ECHIDNA's roster covers the B-method directly — Atelier B is
//! commercial; the open-source ProB complements ECHIDNA's free-tooling
//! posture.  TLA+ already has TLAPS / TLC; ProB adds a constraint
//! engine perspective on the same TLA+ specs.
//!
//! ## Input format
//!
//! - `.mch` / `.imp` / `.ref` — classical-B machines, implementations, refinements
//! - `.bcm` / `.eventb` — Event-B model files (Rodin output)
//! - `.tla` — TLA+ specifications (delegates to ProB's TLC subsumption)
//! - `.als` — Alloy specifications
//!
//! ## CLI invocation
//!
//! `probcli <model> -mc -p MAX_INITIALISATIONS 1` for model-check.
//! `probcli <model> -model_check` for simple model-check.
//!
//! ## Output parsing
//!
//! ProB emits status lines:
//!
//! - `Model checking complete: no error nodes found`
//! - `Counter-example found`
//! - `Deadlock found`
//! - `Result: ok | counter-example | timeout`
//!
//! See `parse_result` for the full classifier.
//!
//! ## Integration tier
//!
//! Tier-5j / Phase-4.  Trust tier 2 (constraint-based BMC; widely
//! validated against Atelier-B for railway certification).
//! Complexity 3 (B-method semantics + constraint engine).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// ProB backend for B / Event-B model checking.
pub struct ProBBackend {
    config: ProverConfig,
}

impl ProBBackend {
    pub fn new(config: ProverConfig) -> Self {
        ProBBackend { config }
    }

    /// Render a `ProofState` into a minimal classical-B machine
    /// definition.  ProB is happy to ingest classical-B even when the
    /// underlying model is Event-B; we use B as the lowest-common
    /// denominator.
    fn to_b_machine(state: &ProofState) -> String {
        let mut b = String::new();
        b.push_str("MACHINE EchidnaProblem\n");
        if !state.context.axioms.is_empty() {
            b.push_str("PROPERTIES\n  ");
            let joined = state
                .context
                .axioms
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(" &\n  ");
            b.push_str(&joined);
            b.push('\n');
        }
        if let Some(goal) = state.goals.first() {
            b.push_str("ASSERTIONS\n  ");
            b.push_str(&goal.target.to_string());
            b.push('\n');
        }
        b.push_str("END\n");
        b
    }

    /// Parse ProB's stdout to a boolean verdict.
    fn parse_result(output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        let positive = [
            "no error nodes found",
            "no counterexample",
            "model checking complete: ok",
            "result: ok",
            "all assertions hold",
        ];
        let negative = [
            "counter-example found",
            "counterexample found",
            "deadlock found",
            "invariant violated",
            "assertion violation",
            "result: counter-example",
            "result: invariant",
        ];
        if positive.iter().any(|m| lower.contains(m)) {
            return Ok(true);
        }
        if negative.iter().any(|m| lower.contains(m)) {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "ProB output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for ProBBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::ProB
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run probcli -version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("probcli").to_string()
        } else {
            stderr.lines().next().unwrap_or("probcli").to_string()
        };
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read ProB input")?;
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
            "prob_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        // Walk classical-B / Event-B section markers and capture
        // contents into either axioms (PROPERTIES, INVARIANT, AXIOMS)
        // or the goal (ASSERTIONS, THEOREMS).
        #[derive(PartialEq)]
        enum Section {
            None,
            Property,
            Goal,
        }
        let mut section = Section::None;
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            match trimmed.to_ascii_uppercase().as_str() {
                "PROPERTIES" | "INVARIANT" | "AXIOMS" => {
                    section = Section::Property;
                    continue;
                },
                "ASSERTIONS" | "THEOREMS" => {
                    section = Section::Goal;
                    continue;
                },
                "END" | "OPERATIONS" | "EVENTS" | "VARIABLES" | "MACHINE" | "MODEL" => {
                    section = Section::None;
                    continue;
                },
                _ => {},
            }
            if trimmed.starts_with("MACHINE") || trimmed.starts_with("MODEL") {
                section = Section::None;
                continue;
            }
            match section {
                Section::Property => state.context.axioms.push(trimmed.to_string()),
                Section::Goal => state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(trimmed.to_string()),
                    hypotheses: vec![],
                }),
                Section::None => {},
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "ProB is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let machine = Self::to_b_machine(state);
        let mut child = Command::new(&self.config.executable)
            .arg("/dev/stdin")
            .arg("-mc")
            .arg("-noltl")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn probcli")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open probcli stdin"))?;
            stdin
                .write_all(machine.as_bytes())
                .await
                .context("Failed to write to probcli stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for probcli")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Self::parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(Self::to_b_machine(state))
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
    fn test_prob_kind() {
        let config = ProverConfig::default();
        let backend = ProBBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::ProB);
    }

    #[test]
    fn test_prob_to_b_machine_includes_assertions() {
        let mut state = ProofState::default();
        state.context.axioms.push("x : NAT".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("x >= 0".to_string()),
            hypotheses: vec![],
        });
        let machine = ProBBackend::to_b_machine(&state);
        assert!(machine.contains("MACHINE EchidnaProblem"));
        assert!(machine.contains("PROPERTIES"));
        assert!(machine.contains("ASSERTIONS"));
        assert!(machine.contains("x >= 0"));
        assert!(machine.contains("END"));
    }

    #[test]
    fn test_prob_parse_result_no_errors() {
        assert!(ProBBackend::parse_result("Model checking complete: no error nodes found")
            .expect("parse"));
    }

    #[test]
    fn test_prob_parse_result_counterexample() {
        assert!(!ProBBackend::parse_result("Counter-example found at depth 3").expect("parse"));
    }

    #[test]
    fn test_prob_parse_result_deadlock() {
        assert!(!ProBBackend::parse_result("Deadlock found in state s_42").expect("parse"));
    }

    #[test]
    fn test_prob_parse_result_inconclusive_errors() {
        assert!(ProBBackend::parse_result("warning: nothing happened").is_err());
    }

    #[tokio::test]
    async fn test_prob_parse_string_extracts_b_sections() {
        let config = ProverConfig::default();
        let backend = ProBBackend::new(config);
        let b = "MACHINE Foo\nPROPERTIES\n  x : NAT\n  y : NAT\nASSERTIONS\n  x + y >= 0\nEND\n";
        let state = backend.parse_string(b).await.expect("parse_string");
        assert_eq!(state.context.axioms.len(), 2);
        assert_eq!(state.goals.len(), 1);
    }
}
