// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Viper verification infrastructure backend
//!
//! Viper (Verification Infrastructure for Permission-based Reasoning) is a
//! verification framework for heap-manipulating programs using permissions
//! and separation logic.
//!
//! Features:
//! - Silver intermediate verification language (.vpr files)
//! - Silicon verifier (symbolic execution)
//! - Carbon verifier (verification condition generation via Boogie)
//! - Implicit dynamic frames / separation logic permissions
//! - Fractional permissions, predicates, magic wands
//! - Used as backend by Prusti (Rust), Gobra (Go), Nagini (Python)

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Viper verification infrastructure backend
///
/// Wraps the Viper toolchain, which provides two verification backends:
/// - **Silicon**: symbolic execution-based verifier (default)
/// - **Carbon**: verification condition generation via Boogie/Z3
///
/// Input is written in Viper's Silver intermediate language (.vpr),
/// which models heap-manipulating programs with permission-based
/// reasoning (implicit dynamic frames / separation logic).
pub struct ViperBackend {
    config: ProverConfig,
}

impl ViperBackend {
    /// Create a new Viper backend with the given configuration.
    pub fn new(config: ProverConfig) -> Self {
        ViperBackend { config }
    }

    /// Convert proof state to Viper Silver language format.
    ///
    /// Axioms are emitted as `assume` statements inside a method body,
    /// definitions become domain axioms, and the goal becomes an
    /// `assert` statement to be verified.
    fn to_silver(&self, state: &ProofState) -> Result<String> {
        let mut silver = String::new();

        // Emit a domain for axioms and definitions
        if !state.context.axioms.is_empty() || !state.context.definitions.is_empty() {
            silver.push_str("domain EchidnaAxioms {\n");

            for (i, axiom) in state.context.axioms.iter().enumerate() {
                silver.push_str(&format!("  axiom axiom_{} {{ {} }}\n", i, axiom));
            }

            for (i, def) in state.context.definitions.iter().enumerate() {
                silver.push_str(&format!("  axiom definition_{} {{ {} }}\n", i, def));
            }

            silver.push_str("}\n\n");
        }

        // Emit a method with the goal as an assertion
        silver.push_str("method echidna_verify()\n");
        silver.push_str("{\n");

        if let Some(goal) = state.goals.first() {
            silver.push_str(&format!("  assert {}\n", goal.target));
        }

        silver.push_str("}\n");

        Ok(silver)
    }

    /// Parse Viper verifier output to determine verification success.
    ///
    /// Both Silicon and Carbon report results in a similar format:
    /// - "No errors found" indicates successful verification
    /// - "X error(s) found" indicates verification failure
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("No errors found")
            || output.contains("0 error(s)")
            || output.contains("Verification successful")
        {
            Ok(true)
        } else if output.contains("error(s) found")
            || output.contains("Verification failed")
            || output.contains("Assert might fail")
            || output.contains("Postcondition of")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "Viper inconclusive or error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for ViperBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Viper
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run viper --version")?;

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

    /// Parse a Silver (.vpr) program into a ProofState.
    ///
    /// Extracts domain axioms into the context and `assert` statements
    /// into goals. Comments (// and /* */) are skipped.
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "viper_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }

            // Extract domain axioms as context axioms
            if line.starts_with("axiom") {
                if let Some(body) = line.split('{').nth(1) {
                    let body = body.trim_end_matches('}').trim();
                    state.context.axioms.push(body.to_string());
                }
            }

            // Extract assert statements as goals
            if line.starts_with("assert") {
                let assertion = line
                    .trim_start_matches("assert")
                    .trim()
                    .trim_end_matches(';')
                    .trim();
                if !assertion.is_empty() {
                    state.goals.push(Goal {
                        id: format!("goal_{}", state.goals.len()),
                        target: Term::Const(assertion.to_string()),
                        hypotheses: vec![],
                    });
                }
            }

            // Extract requires/ensures as hypotheses/goals
            if line.starts_with("requires") {
                let precondition = line
                    .trim_start_matches("requires")
                    .trim()
                    .trim_end_matches(';')
                    .trim();
                if !precondition.is_empty() {
                    state.context.axioms.push(precondition.to_string());
                }
            }

            if line.starts_with("ensures") {
                let postcondition = line
                    .trim_start_matches("ensures")
                    .trim()
                    .trim_end_matches(';')
                    .trim();
                if !postcondition.is_empty() {
                    state.goals.push(Goal {
                        id: format!("goal_{}", state.goals.len()),
                        target: Term::Const(postcondition.to_string()),
                        hypotheses: vec![],
                    });
                }
            }
        }

        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Viper is an automated verifier - interactive tactics not supported"
        ))
    }

    /// Verify a proof state by invoking the Viper verifier (Silicon by default).
    ///
    /// The Silver program is written to stdin and the verifier is run with
    /// the configured timeout. Both Silicon and Carbon are supported via
    /// the `--backend` flag (configurable through extra args).
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg("--timeout")
                    .arg(format!("{}", self.config.timeout))
                    .args(&self.config.args)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("Viper timed out")??;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            return self
                .parse_result(&stdout)
                .or_else(|_| self.parse_result(&stderr));
        }
        let silver_code = if let Some(src) = state.metadata.get("viper_source").and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_silver(state)?
        };

        let mut child = Command::new(&self.config.executable)
            .arg("--timeout")
            .arg(format!("{}", self.config.timeout))
            .args(&self.config.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Viper process")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(silver_code.as_bytes())
                .await
                .context("Failed to write to Viper stdin")?;
            stdin.flush().await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("Viper timed out")??;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        self.parse_result(&stdout)
            .or_else(|_| self.parse_result(&stderr))
    }

    /// Export proof state as Silver (.vpr) source code.
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_silver(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Viper is a deductive verification infrastructure for Silver programs.
        // Suggestions are Silver contract annotations and Viper-level hints.
        let tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "viper".to_string(),
                command: "add_precondition".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "viper".to_string(),
                command: "add_postcondition".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "viper".to_string(),
                command: "add_invariant".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "viper".to_string(),
                command: "exhale".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "viper".to_string(),
                command: "assert".to_string(),
                args: vec![],
            },
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Viper delegates to SMT back-ends; no native theorem-search interface.
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
    async fn test_viper_silver_export() {
        let config = ProverConfig {
            executable: PathBuf::from("silicon"),
            timeout: 10,
            ..Default::default()
        };

        let backend = ViperBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("x > 0".to_string());
        state.context.axioms.push("y > 0".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("x + y > 0".to_string()),
            hypotheses: vec![],
        });

        let silver = backend.to_silver(&state).unwrap();

        assert!(silver.contains("axiom axiom_0 { x > 0 }"));
        assert!(silver.contains("axiom axiom_1 { y > 0 }"));
        assert!(silver.contains("assert x + y > 0"));
    }

    #[tokio::test]
    async fn test_viper_parse_silver() {
        let config = ProverConfig {
            executable: PathBuf::from("silicon"),
            timeout: 10,
            ..Default::default()
        };

        let backend = ViperBackend::new(config);

        let silver = r#"
            // A simple Viper verification example
            requires x > 0
            ensures x > 0
            assert x > 0
        "#;

        let state = backend.parse_string(silver).await.unwrap();

        assert_eq!(state.context.axioms.len(), 1);
        assert_eq!(state.context.axioms[0], "x > 0");
        assert_eq!(state.goals.len(), 2); // ensures + assert
    }

    #[tokio::test]
    async fn test_viper_parse_result() {
        let config = ProverConfig {
            executable: PathBuf::from("silicon"),
            timeout: 10,
            ..Default::default()
        };

        let backend = ViperBackend::new(config);

        assert!(backend.parse_result("No errors found.").unwrap());
        assert!(!backend.parse_result("1 error(s) found.").unwrap());
        assert!(backend.parse_result("Inconclusive garbage").is_err());
    }

    #[tokio::test]
    #[ignore] // Requires Viper (Silicon) to be installed
    async fn test_viper_simple_verification() {
        let config = ProverConfig {
            executable: PathBuf::from("silicon"),
            timeout: 30,
            ..Default::default()
        };

        let backend = ViperBackend::new(config);

        let silver = "method test() { assert true }";
        let state = backend.parse_string(silver).await.unwrap();

        let result = backend.verify_proof(&state).await;

        match result {
            Ok(true) => println!("Viper verified assertion"),
            Ok(false) => panic!("Viper failed to verify trivial assertion"),
            Err(e) => println!("Viper not installed or error: {}", e),
        }
    }
}
