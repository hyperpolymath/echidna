// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! SPIN Model Checker Backend
//!
//! SPIN is a widely-used model checker for verifying concurrent and distributed
//! systems. It takes Promela (.pml) specifications as input and verifies
//! properties such as absence of deadlocks, assertion violations, and LTL
//! temporal logic formulae.
//!
//! Features:
//! - Promela input language (proctype, channels, do/od, if/fi)
//! - LTL temporal logic formula verification
//! - Deadlock detection
//! - Assertion checking
//! - On-the-fly verification via `spin -run`

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// SPIN model checker backend
///
/// Integrates the SPIN model checker for verifying concurrent system
/// specifications written in Promela. Uses `spin -run` for simplified
/// verification mode which generates, compiles, and runs the verifier
/// in a single step.
pub struct SpinBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl SpinBackend {
    /// Create a new SPIN backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        SpinBackend { config }
    }

    /// Convert proof state to Promela format
    ///
    /// Generates a valid Promela model from the ECHIDNA proof state.
    /// Axioms become process definitions, goals become assertion checks,
    /// and definitions become inline macros.
    fn to_promela(&self, state: &ProofState) -> Result<String> {
        let mut promela = String::new();

        // Header comment
        promela.push_str("/* ECHIDNA SPIN Export */\n\n");

        // Add definitions as inline macros
        for def in &state.context.definitions {
            promela.push_str(&format!("/* definition: {} */\n", def));
        }

        // Add axioms as process bodies or global assertions
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            promela.push_str(&format!("/* axiom_{}: {} */\n", i, axiom));
        }

        // Add goals as assertion blocks
        for goal in &state.goals {
            promela.push_str(&format!(
                "/* goal {}: assert({}) */\n",
                goal.id, goal.target
            ));
        }

        // If there are raw axioms that look like Promela, include them directly
        for axiom in &state.context.axioms {
            if axiom.contains("proctype")
                || axiom.contains("init")
                || axiom.contains("ltl")
                || axiom.contains("chan")
            {
                promela.push_str(axiom);
                promela.push('\n');
            }
        }

        // If no proctype was added from axioms, wrap goals in an init block
        if !promela.contains("proctype") && !promela.contains("init") {
            promela.push_str("init {\n");
            for goal in &state.goals {
                let target_str = format!("{}", goal.target);
                promela.push_str(&format!("    assert({});\n", target_str));
            }
            promela.push_str("}\n");
        }

        Ok(promela)
    }

    /// Parse SPIN verification output to determine success or failure
    ///
    /// SPIN reports "errors: 0" when verification succeeds.
    /// Any non-zero error count or the presence of "error" markers
    /// indicates a counterexample was found.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Check for successful verification
        if output.contains("errors: 0") {
            return Ok(true);
        }

        // Check for explicit failure markers
        if output.contains("assertion violated")
            || output.contains("errors: ")
            || output.contains("pan: invalid end state")
        {
            return Ok(false);
        }

        // Check for acceptance cycle (LTL violation)
        if output.contains("acceptance cycle") {
            return Ok(false);
        }

        // If SPIN completed without errors marker, treat as inconclusive
        Err(anyhow!(
            "SPIN inconclusive or error: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse Promela source to extract proctype names, channel declarations,
    /// assertions, and LTL formulae into the proof state
    fn parse_promela(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("/*") || trimmed.starts_with("//") {
                continue;
            }

            // Detect proctype declarations
            if trimmed.contains("proctype") || trimmed.starts_with("init") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect channel declarations
            if trimmed.starts_with("chan ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect assertions
            if trimmed.contains("assert(") || trimmed.contains("assert (") {
                // Extract the assertion body
                if let Some(start) = trimmed.find("assert(").or_else(|| trimmed.find("assert (")) {
                    let after_assert = &trimmed[start..];
                    if let Some(paren_start) = after_assert.find('(') {
                        let body = &after_assert[paren_start + 1..];
                        // Find matching closing paren
                        if let Some(end) = body.rfind(')') {
                            let assertion_body = body[..end].trim();
                            state.goals.push(Goal {
                                id: format!("assert_{}", state.goals.len()),
                                target: Term::Const(assertion_body.to_string()),
                                hypotheses: vec![],
                            });
                        }
                    }
                }
            }

            // Detect LTL formulae
            if trimmed.starts_with("ltl ") {
                let formula = trimmed.trim_start_matches("ltl ").trim();
                state.goals.push(Goal {
                    id: format!("ltl_{}", state.goals.len()),
                    target: Term::Const(formula.to_string()),
                    hypotheses: vec![],
                });
            }

            // Detect do/od and if/fi blocks as structural elements
            if trimmed.starts_with("do") || trimmed.starts_with("if") {
                state.context.axioms.push(trimmed.to_string());
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for SpinBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::SPIN
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-V")
            .output()
            .await
            .context("Failed to run spin -V")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // SPIN outputs version to stderr typically
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
            .context("Failed to read Promela file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_promela(content)?;
        state.metadata.insert(
            "spin_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddAssertion: add a new assertion to the model
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "spin" && command == "add_assertion" => {
                let assertion_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("assert_{}", new_state.goals.len()),
                    target: Term::Const(assertion_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // LTLFormula: add an LTL property to verify
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "spin" && command == "ltl_formula" => {
                let ltl_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("ltl_{}", new_state.goals.len()),
                    target: Term::Const(format!("ltl {{ {} }}", ltl_text)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AtomicBlock: wrap existing axioms in an atomic block
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "spin" && command == "atomic_block" => {
                let block_content = args.join(" ");
                let mut new_state = state.clone();
                new_state
                    .context
                    .axioms
                    .push(format!("atomic {{ {} }}", block_content));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for SPIN model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 10),
                Command::new(&self.config.executable)
                    .arg("-run")
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| {
                anyhow!(
                    "SPIN verification timed out after {} seconds",
                    self.config.timeout
                )
            })?
            .context("Failed to execute SPIN")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return self.parse_result(&combined);
        }
        let promela_code = if let Some(src) = state.metadata.get("spin_source").and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_promela(state)?
        };

        // Write Promela to a temporary file (spin -run requires a file)
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for SPIN")?;
        let tmp_file = tmp_dir.path().join("model.pml");
        tokio::fs::write(&tmp_file, &promela_code)
            .await
            .context("Failed to write temporary Promela file")?;

        // Run spin -run which generates, compiles, and runs the verifier
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            Command::new(&self.config.executable)
                .arg("-run")
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "SPIN verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute SPIN")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Combine stdout and stderr for parsing (SPIN uses both)
        let combined = format!("{}\n{}", stdout, stderr);

        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_promela(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "spin".to_string(),
                command: "add_assertion".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "spin".to_string(),
                command: "ltl_formula".to_string(),
                args: vec!["[](!error)".to_string()],
            },
            Tactic::Custom {
                prover: "spin".to_string(),
                command: "atomic_block".to_string(),
                args: vec!["skip".to_string()],
            },
        ];

        tactics.truncate(limit);
        Ok(tactics)
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
    async fn test_spin_promela_export() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };

        let backend = SpinBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "assert_0".to_string(),
            target: Term::Const("1 == 1".to_string()),
            hypotheses: vec![],
        });

        let promela = backend.to_promela(&state).unwrap();

        assert!(promela.contains("ECHIDNA SPIN Export"));
        assert!(promela.contains("init"));
        assert!(promela.contains("assert(1 == 1)"));
    }

    #[tokio::test]
    async fn test_spin_parse_promela() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };

        let backend = SpinBackend::new(config);

        let promela = r#"
proctype Sender() {
    chan c = [1] of { int };
    c ! 42;
    assert(true);
}
ltl p1 { []<> ready }
"#;

        let state = backend.parse_string(promela).await.unwrap();

        // Should have found the proctype, channel, and assertion
        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed axioms"
        );
        assert!(!state.goals.is_empty(), "Should have parsed goals");
    }

    #[test]
    fn test_spin_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };

        let backend = SpinBackend::new(config);

        let success_output = "State-vector 28 byte, depth reached 5\nerrors: 0\n";
        assert!(backend.parse_result(success_output).unwrap());
    }

    #[test]
    fn test_spin_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };

        let backend = SpinBackend::new(config);

        let failure_output = "pan:1: assertion violated (x == 1)\nerrors: 1\n";
        assert!(!backend.parse_result(failure_output).unwrap());

        let deadlock_output = "pan: invalid end state (at depth 7)\nerrors: 1\n";
        assert!(!backend.parse_result(deadlock_output).unwrap());
    }

    #[test]
    fn test_spin_parse_result_acceptance_cycle() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let output = "pan:1: acceptance cycle (at depth 12)\nerrors: 1\n";
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_spin_parse_result_inconclusive() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let output = "some random output with no markers\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_spin_kind() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::SPIN);
    }

    #[test]
    fn test_spin_config_access() {
        let config = ProverConfig {
            executable: PathBuf::from("/usr/bin/spin"),
            timeout: 60,
            ..Default::default()
        };
        let backend = SpinBackend::new(config.clone());
        assert_eq!(backend.config().executable, PathBuf::from("/usr/bin/spin"));
        assert_eq!(backend.config().timeout, 60);
    }

    #[tokio::test]
    async fn test_spin_promela_empty_state() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);
        let state = ProofState::default();
        let promela = backend.to_promela(&state).unwrap();

        assert!(promela.contains("ECHIDNA SPIN Export"));
        // Empty state should still generate init block
        assert!(promela.contains("init"));
    }

    #[tokio::test]
    async fn test_spin_promela_with_raw_proctype() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let mut state = ProofState::default();
        state
            .context
            .axioms
            .push("proctype P() { skip }".to_string());

        let promela = backend.to_promela(&state).unwrap();
        assert!(promela.contains("proctype P()"));
        // Should NOT add init block since proctype exists
        assert!(!promela.contains("init {"));
    }

    #[tokio::test]
    async fn test_spin_parse_channel_declaration() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let promela = "chan c = [1] of { int };\nassert(true);\n";
        let state = backend.parse_promela(promela).unwrap();

        assert!(!state.context.axioms.is_empty(), "Should parse channel");
        assert!(!state.goals.is_empty(), "Should parse assertion");
    }

    #[tokio::test]
    async fn test_spin_parse_ltl_formula() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let promela = "ltl p1 { []<> ready }\n";
        let state = backend.parse_promela(promela).unwrap();

        assert_eq!(state.goals.len(), 1);
        assert!(state.goals[0].id.starts_with("ltl_"));
    }

    #[tokio::test]
    async fn test_spin_parse_empty_input() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);

        let state = backend.parse_promela("").unwrap();
        assert!(state.goals.is_empty());
        assert!(state.context.axioms.is_empty());
    }

    #[tokio::test]
    async fn test_spin_suggest_tactics() {
        let config = ProverConfig {
            executable: PathBuf::from("spin"),
            timeout: 30,
            ..Default::default()
        };
        let backend = SpinBackend::new(config);
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 2).await.unwrap();
        assert_eq!(tactics.len(), 2);
    }
}
