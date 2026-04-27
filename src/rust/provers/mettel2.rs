// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! MetTeL2 backend — tableau generator for arbitrary modal logics.
//!
//! MetTeL2 is a Java-based tableau-prover *generator*: it takes a
//! logic specification (axioms + connectives + modalities) and
//! synthesises a sound + complete tableau prover for that logic,
//! which it then runs against a goal formula.
//!
//! ## Why this backend exists
//!
//! ECHIDNA covers many specific modal/temporal logics through
//! dedicated backends (PRISM, Tamarin, ProVerif, Spin, NuSMV, etc.)
//! but no other backend handles *arbitrary* modal logics
//! parametrically.  MetTeL2 fills that niche: any modal logic
//! presentable in MetTeL's spec syntax becomes a usable target.
//!
//! ## Input format
//!
//! MetTeL2 takes two artefacts:
//!
//! 1. A **logic specification** (`<logic>.spec`) describing the
//!    syntax + axioms of the target logic.  The MetTeL2 distribution
//!    ships specs for K, KT, KD45, S4, S5, etc.
//! 2. An **input file** (`<input>.mt`) containing the formula(e) to
//!    decide.
//!
//! For v1 we accept the `mettel_logic` metadata key (defaults to
//! `S4`) as a logic-name selector pointing at one of the bundled
//! specs.  Custom-logic specs are out of scope for v1.
//!
//! ## Output parsing
//!
//! MetTeL2 emits one of:
//!
//! - `Provable.`  — formula provable
//! - `Not provable.`  — formula refuted (counter-model found)
//! - `Unknown.`  — tableau open at depth bound
//!
//! ## CLI invocation
//!
//! Default invocation: `java -jar mettel2.jar -s <logic>.spec -i
//! <input>.mt`.  We pipe the formula on stdin to avoid temp-file
//! plumbing.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 2 (the *generated* tableau is
//! correct by construction, but we don't formally verify the spec).
//! Complexity 4 (JVM cold-start latency, configuration-heavy).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// MetTeL2 backend (tableau generator for modal logics).
pub struct MetTeL2Backend {
    config: ProverConfig,
}

impl MetTeL2Backend {
    pub fn new(config: ProverConfig) -> Self {
        MetTeL2Backend { config }
    }

    /// Convert a `ProofState` into a MetTeL2 input.
    fn to_mettel(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        // Preamble: brief comment for diagnostics.
        s.push_str("// echidna -> mettel2 input\n");

        // Each axiom is a premise; the goal is the conjecture.
        // MetTeL2 input format uses formula-per-line with `.` terminator.
        for axiom in &state.context.axioms {
            s.push_str(&format!("{}.\n", axiom));
        }
        if let Some(goal) = state.goals.first() {
            s.push_str(&format!("{}.\n", goal.target));
        } else {
            s.push_str("true.\n");
        }
        Ok(s)
    }

    /// Determine the logic spec to load.
    fn logic_name(&self, state: &ProofState) -> String {
        state
            .metadata
            .get("mettel_logic")
            .and_then(|v| v.as_str())
            .unwrap_or("S4")
            .to_string()
    }

    /// Parse MetTeL2 stdout to determine proof success.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        if lower.contains("provable.") && !lower.contains("not provable") {
            return Ok(true);
        }
        if lower.contains("not provable.") {
            return Ok(false);
        }
        if lower.contains("unknown.") {
            return Err(anyhow::anyhow!(
                "MetTeL2 tableau open (Unknown): {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }
        if lower.contains("error") || lower.contains("exception") {
            return Err(anyhow::anyhow!(
                "MetTeL2 error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }
        Err(anyhow::anyhow!(
            "MetTeL2 output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for MetTeL2Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::MetTeL2
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run mettel2 -version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.trim().is_empty() {
            stdout.lines().next().unwrap_or("mettel2").to_string()
        } else {
            stderr.lines().next().unwrap_or("mettel2").to_string()
        };
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read MetTeL2 input")?;
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
            "mettel_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        // Lightweight: every non-comment line becomes either an
        // axiom (all but the last) or the goal (the last).
        let mut formulas: Vec<String> = Vec::new();
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with('#') {
                continue;
            }
            let stripped = trimmed.trim_end_matches('.').trim().to_string();
            if !stripped.is_empty() {
                formulas.push(stripped);
            }
        }
        if let Some(goal) = formulas.pop() {
            state.context.axioms.extend(formulas);
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const(goal),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "MetTeL2 generates and runs tableau provers automatically — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let input = self.to_mettel(state)?;
        let logic = self.logic_name(state);
        let mut child = Command::new(&self.config.executable)
            .arg("-logic")
            .arg(&logic)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn mettel2")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open mettel2 stdin"))?;
            stdin
                .write_all(input.as_bytes())
                .await
                .context("Failed to write to mettel2 stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for mettel2")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_mettel(state)
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
    fn test_mettel2_kind() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        assert_eq!(backend.kind(), ProverKind::MetTeL2);
    }

    #[test]
    fn test_mettel2_to_mettel_basic() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let mut state = ProofState::default();
        state.context.axioms.push("[](p -> q)".to_string());
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("[]p -> []q".to_string()),
            hypotheses: vec![],
        });
        let script = backend.to_mettel(&state).expect("to_mettel failed");
        assert!(script.contains("[](p -> q)"));
        assert!(script.contains("[]p -> []q."));
    }

    #[test]
    fn test_mettel2_to_mettel_no_goal_emits_true() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let state = ProofState::default();
        let script = backend.to_mettel(&state).expect("to_mettel failed");
        assert!(script.contains("true."));
    }

    #[test]
    fn test_mettel2_default_logic_s4() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let state = ProofState::default();
        assert_eq!(backend.logic_name(&state), "S4");
    }

    #[test]
    fn test_mettel2_logic_override() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let mut state = ProofState::default();
        state.metadata.insert(
            "mettel_logic".to_string(),
            serde_json::Value::String("KT".to_string()),
        );
        assert_eq!(backend.logic_name(&state), "KT");
    }

    #[test]
    fn test_mettel2_parse_result_provable() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let r = backend
            .parse_result("Tableau closed.\nProvable.")
            .expect("parse_result failed");
        assert!(r);
    }

    #[test]
    fn test_mettel2_parse_result_not_provable() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let r = backend
            .parse_result("Counter-model found.\nNot provable.")
            .expect("parse_result failed");
        assert!(!r);
    }

    #[test]
    fn test_mettel2_parse_result_unknown() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let r = backend.parse_result("Unknown.");
        assert!(r.is_err());
    }

    #[tokio::test]
    async fn test_mettel2_parse_string_extracts_goal_and_axioms() {
        let config = ProverConfig::default();
        let backend = MetTeL2Backend::new(config);
        let input = "[](p -> q).\n[]p.\n[]q.\n";
        let state = backend.parse_string(input).await.expect("parse_string failed");
        assert_eq!(state.context.axioms.len(), 2);
        assert_eq!(state.goals.len(), 1);
    }
}
