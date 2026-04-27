// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! STORM backend — high-performance probabilistic model checker.
//!
//! STORM is the modern successor to PRISM in research benchmarks: a
//! C++ rewrite with better symbolic engines (DD-, sparse-, hybrid-),
//! tight integration with JANI, and SOTA performance on probabilistic
//! and statistical model checking.
//!
//! ## Why this backend exists
//!
//! ECHIDNA already has PRISM as a probabilistic model-checker
//! frontend.  STORM is preferred for:
//!
//! - JANI input (interoperable with mcsta, modest-checker, EPMC, …)
//! - DFT (Dynamic Fault Tree) analysis
//! - Conditional probability queries
//! - Counterexample generation
//!
//! STORM and PRISM are kept distinct so the corpus tracker sees them
//! as separate solvers — their result distributions diverge enough
//! to be useful as an internal cross-check.
//!
//! ## Input format
//!
//! - PRISM `.pm` model files (legacy, supported)
//! - JANI `.jani` model files (preferred)
//! - DFT `.dft` files (Storm-only)
//!
//! Property files use either PRISM property syntax or PCTL/CSL embedded
//! in JANI.
//!
//! ## CLI invocation
//!
//! `storm --jani <model> --prop <pctl-file>` (JANI workflow).
//! `storm --prism <model> --prop <prop>` (PRISM workflow).
//!
//! ## Output parsing
//!
//! STORM writes verdict lines like:
//!
//! - `Result (for initial states): true|false`
//! - `Result (for initial states): 0.0234`
//! - `Property satisfied`
//!
//! For probabilistic results, the goal-side comparator (e.g.
//! `P>=0.95 [F goal]`) is responsible for the boolean reduction —
//! Storm itself reports the numerical value.  We treat any reported
//! value as "the model has been checked" and rely on the goal text
//! being a boolean property.
//!
//! ## Integration tier
//!
//! Tier-5i / Phase-4.  Trust tier 2 (DD/symbolic engines, no
//! certificate output).  Complexity 3 (numerical fixed-point
//! computation; well-understood).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// STORM backend for probabilistic model checking.
pub struct StormBackend {
    config: ProverConfig,
}

impl StormBackend {
    pub fn new(config: ProverConfig) -> Self {
        StormBackend { config }
    }

    /// Render a `ProofState` into a JANI-shaped placeholder for STORM
    /// to ingest via stdin.
    ///
    /// The serializer emits a minimal JANI envelope wrapping each
    /// declared axiom as a model snippet and the goal as the property
    /// query.  Real STORM workloads should use `parse_file` against an
    /// existing `.jani` / `.pm` source — `to_jani` is for round-trip
    /// regression only.
    fn to_jani(state: &ProofState) -> String {
        let mut jani = String::new();
        jani.push_str("{\n");
        jani.push_str("  \"jani-version\": 1,\n");
        jani.push_str("  \"name\": \"echidna_problem\",\n");
        jani.push_str("  \"type\": \"dtmc\",\n");
        jani.push_str("  \"actions\": [],\n");
        jani.push_str("  \"variables\": [],\n");
        jani.push_str("  \"properties\": [\n");
        if let Some(goal) = state.goals.first() {
            jani.push_str(&format!(
                "    {{ \"name\": \"goal\", \"expression\": \"{}\" }}\n",
                goal.target.to_string().replace('"', "\\\"")
            ));
        }
        jani.push_str("  ],\n");
        jani.push_str("  \"automata\": [\n    { \"name\": \"main\", \"locations\": [{\"name\":\"loc\"}], \"initial-locations\": [\"loc\"], \"edges\": [] }\n");
        jani.push_str("  ],\n");
        jani.push_str("  \"system\": { \"elements\": [{\"automaton\": \"main\"}] },\n");
        jani.push_str("  \"axioms\": [\n");
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            let comma = if i + 1 < state.context.axioms.len() { "," } else { "" };
            jani.push_str(&format!(
                "    \"{}\"{}\n",
                axiom.replace('"', "\\\""),
                comma
            ));
        }
        jani.push_str("  ]\n");
        jani.push_str("}\n");
        jani
    }

    /// Parse STORM's stdout to a boolean verdict.
    ///
    /// STORM's natural output is numerical for probabilistic queries;
    /// for `P>=p` / `P<=p` style goals it returns `true`/`false` after
    /// the comparator.  We accept either.
    fn parse_result(output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        if lower.contains("result (for initial states): true")
            || lower.contains("property satisfied")
            || lower.contains("yes")
        {
            return Ok(true);
        }
        if lower.contains("result (for initial states): false")
            || lower.contains("property violated")
            || lower.contains("no\n")
            || lower.ends_with("no")
        {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "STORM output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for StormBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Storm
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run storm --version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.lines().next().unwrap_or("storm").trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read STORM input")?;
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
            "storm_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        // PRISM-format extraction: lines starting with `//`, `module`,
        // or property prefixes `P=?` / `Pmin=?` / `Pmax=?` / `R=?` /
        // `S=?` are captured.  This is intentionally simple — STORM
        // re-parses the source itself.
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("//") {
                continue;
            }
            if trimmed.starts_with("P=?")
                || trimmed.starts_with("Pmin=?")
                || trimmed.starts_with("Pmax=?")
                || trimmed.starts_with("R=?")
                || trimmed.starts_with("S=?")
                || trimmed.starts_with("P>=")
                || trimmed.starts_with("P<=")
            {
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(trimmed.to_string()),
                    hypotheses: vec![],
                });
            } else if trimmed.starts_with("module ")
                || trimmed.starts_with("formula ")
                || trimmed.starts_with("dtmc")
                || trimmed.starts_with("ctmc")
                || trimmed.starts_with("mdp")
            {
                state.context.axioms.push(trimmed.to_string());
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "STORM is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let jani = Self::to_jani(state);
        let mut child = Command::new(&self.config.executable)
            .arg("--jani")
            .arg("/dev/stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn storm")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open storm stdin"))?;
            stdin
                .write_all(jani.as_bytes())
                .await
                .context("Failed to write to storm stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for storm")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Self::parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(Self::to_jani(state))
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
    fn test_storm_kind() {
        let config = ProverConfig::default();
        let backend = StormBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Storm);
    }

    #[test]
    fn test_storm_to_jani_emits_minimal_envelope() {
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("P>=0.95 [F done]".to_string()),
            hypotheses: vec![],
        });
        let jani = StormBackend::to_jani(&state);
        assert!(jani.contains("\"jani-version\": 1"));
        assert!(jani.contains("\"properties\""));
        assert!(jani.contains("P>=0.95 [F done]"));
    }

    #[test]
    fn test_storm_parse_result_satisfied() {
        assert!(StormBackend::parse_result(
            "Result (for initial states): true\nTime for model checking: 0.01s",
        )
        .expect("parse"));
    }

    #[test]
    fn test_storm_parse_result_violated() {
        assert!(!StormBackend::parse_result(
            "Result (for initial states): false\n",
        )
        .expect("parse"));
    }

    #[test]
    fn test_storm_parse_result_unknown_errors() {
        assert!(StormBackend::parse_result("ERROR: parser failed").is_err());
    }

    #[tokio::test]
    async fn test_storm_parse_string_extracts_prism_module_and_property() {
        let config = ProverConfig::default();
        let backend = StormBackend::new(config);
        let prism = "dtmc\nmodule foo end\nP>=0.5 [F done]\n";
        let state = backend.parse_string(prism).await.expect("parse_string");
        assert!(!state.context.axioms.is_empty());
        assert_eq!(state.goals.len(), 1);
    }
}
