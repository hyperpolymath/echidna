// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! TLC Model Checker Backend
//!
//! TLC is the explicit-state model checker for TLA+ specifications.
//! It exhaustively checks finite models of TLA+ specifications against
//! temporal logic properties (invariants, liveness, fairness).
//!
//! Input format: TLA+ specifications (.tla files) with a configuration (.cfg).
//! Executable: `tlc2` (Java-based, typically invoked via `java -jar tla2tools.jar`).
//!
//! Features:
//! - Exhaustive state exploration for finite models
//! - Invariant checking (state predicates that must always hold)
//! - Temporal property checking (liveness, fairness)
//! - Symmetry reduction and state constraints
//! - Distributed model checking mode

#![allow(dead_code)]

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// TLC TLA+ model checker backend
///
/// Integrates the TLC model checker for verifying TLA+ specifications.
/// TLC performs exhaustive state-space exploration of finite instances
/// and checks invariants, temporal properties, and deadlock freedom.
pub struct TLCBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl TLCBackend {
    /// Create a new TLC backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        TLCBackend { config }
    }

    /// Convert proof state to TLA+ specification format
    ///
    /// Generates a valid TLA+ module from the ECHIDNA proof state.
    /// Axioms become operator definitions, goals become invariant
    /// or temporal property assertions.
    fn to_tla(&self, state: &ProofState) -> Result<String> {
        let mut tla = String::new();

        // Header
        tla.push_str("\\* ECHIDNA TLC Export\n");
        tla.push_str("---- MODULE EchidnaModel ----\n");
        tla.push_str("EXTENDS Naturals, Sequences, TLC\n\n");

        // Add definitions as TLA+ operators
        for def in &state.context.definitions {
            tla.push_str(&format!("{}\n", def.name));
        }

        // Add axioms as TLA+ definitions or ASSUME statements
        for axiom in &state.context.axioms {
            if axiom.contains("==") || axiom.contains("VARIABLE") || axiom.contains("Init") {
                tla.push_str(axiom);
                tla.push('\n');
            } else {
                tla.push_str(&format!("ASSUME {}\n", axiom));
            }
        }

        // Add goals as property definitions
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            tla.push_str(&format!("\\* Property: {}\n", goal.id));
            tla.push_str(&format!("{} == {}\n", goal.id, target_str));
        }

        tla.push_str("\n====\n");

        Ok(tla)
    }

    /// Generate a TLC configuration (.cfg) file for the specification
    ///
    /// Lists invariants and temporal properties for TLC to check.
    fn to_cfg(&self, state: &ProofState) -> String {
        let mut cfg = String::new();
        cfg.push_str("\\* ECHIDNA TLC Configuration\n");

        // Add invariants and properties
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            if target_str.contains("[]") || target_str.contains("<>") || target_str.contains("~>") {
                cfg.push_str(&format!("PROPERTY {}\n", goal.id));
            } else {
                cfg.push_str(&format!("INVARIANT {}\n", goal.id));
            }
        }

        cfg
    }

    /// Parse TLC verification output to determine success or failure
    ///
    /// TLC reports "Model checking completed. No error has been found."
    /// on success, and "Error:" followed by a violation trace on failure.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Check for successful completion
        if output.contains("Model checking completed. No error has been found") {
            return Ok(true);
        }

        // Check for invariant violation
        if output.contains("Invariant") && output.contains("is violated") {
            return Ok(false);
        }

        // Check for temporal property violation
        if output.contains("Temporal properties were violated") {
            return Ok(false);
        }

        // Check for deadlock
        if output.contains("Deadlock reached") {
            return Ok(false);
        }

        // Check for generic error
        if output.contains("Error:") || output.contains("TLC threw") {
            return Err(anyhow!("TLC error: {}", output.lines().take(10).collect::<Vec<_>>().join("\n")));
        }

        Err(anyhow!(
            "TLC inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse TLA+ source to extract operator definitions, variables,
    /// and property specifications into the proof state
    fn parse_tla(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("\\*") || trimmed.starts_with("----") || trimmed.starts_with("====") {
                continue;
            }

            // Detect VARIABLE declarations
            if trimmed.starts_with("VARIABLE") || trimmed.starts_with("VARIABLES") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect operator definitions (Init, Next, etc.)
            if trimmed.contains("==") {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("TLA_OP".to_string()),
                    body: Term::Const(trimmed.to_string()),
                });
            }

            // Detect ASSUME statements
            if trimmed.starts_with("ASSUME") {
                let assume_body = trimmed.trim_start_matches("ASSUME").trim();
                state.context.axioms.push(assume_body.to_string());
            }

            // Detect THEOREM or property assertions
            if trimmed.starts_with("THEOREM") {
                let theorem = trimmed.trim_start_matches("THEOREM").trim();
                state.goals.push(Goal {
                    id: format!("theorem_{}", state.goals.len()),
                    target: Term::Const(theorem.to_string()),
                    hypotheses: vec![],
                });
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for TLCBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::TLC
    }

    async fn version(&self) -> Result<String> {
        // TLC is Java-based; running with -h or no args typically outputs version
        let output = Command::new(&self.config.executable)
            .arg("-h")
            .output()
            .await
            .context("Failed to run tlc2 -h")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("TLC") || l.contains("Version") || l.contains("version"))
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read TLA+ file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_tla(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddInvariant: add an invariant to check
            Tactic::Custom { prover, command, args }
                if prover == "tlc" && command == "add_invariant" =>
            {
                let inv_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("inv_{}", new_state.goals.len()),
                    target: Term::Const(inv_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }

            // AddProperty: add a temporal property to check
            Tactic::Custom { prover, command, args }
                if prover == "tlc" && command == "add_property" =>
            {
                let prop_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("prop_{}", new_state.goals.len()),
                    target: Term::Const(prop_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }

            // SetConstraint: add a state constraint to reduce the state space
            Tactic::Custom { prover, command, args }
                if prover == "tlc" && command == "set_constraint" =>
            {
                let constraint = args.join(" ");
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "constraint".to_string(),
                    serde_json::Value::String(constraint),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for TLC model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let tla_code = self.to_tla(state)?;
        let cfg_code = self.to_cfg(state);

        // Write TLA+ and CFG to temporary files
        let tmp_dir = tempfile::tempdir()
            .context("Failed to create temporary directory for TLC")?;
        let tla_file = tmp_dir.path().join("EchidnaModel.tla");
        let cfg_file = tmp_dir.path().join("EchidnaModel.cfg");

        tokio::fs::write(&tla_file, &tla_code)
            .await
            .context("Failed to write temporary TLA+ file")?;
        tokio::fs::write(&cfg_file, &cfg_code)
            .await
            .context("Failed to write temporary TLC config file")?;

        // Run TLC on the specification
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&tla_file)
                .arg("-config")
                .arg(&cfg_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("TLC timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute TLC")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tla(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "tlc".to_string(),
                command: "add_invariant".to_string(),
                args: vec!["TypeOK".to_string()],
            },
            Tactic::Custom {
                prover: "tlc".to_string(),
                command: "add_property".to_string(),
                args: vec!["[]<>(done)".to_string()],
            },
            Tactic::Custom {
                prover: "tlc".to_string(),
                command: "set_constraint".to_string(),
                args: vec!["counter < 10".to_string()],
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
    async fn test_tlc_tla_export() {
        let config = ProverConfig {
            executable: PathBuf::from("tlc2"),
            timeout: 30,
            ..Default::default()
        };

        let backend = TLCBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "inv_0".to_string(),
            target: Term::Const("x > 0".to_string()),
            hypotheses: vec![],
        });

        let tla = backend.to_tla(&state).unwrap();

        assert!(tla.contains("ECHIDNA TLC Export"));
        assert!(tla.contains("MODULE EchidnaModel"));
        assert!(tla.contains("inv_0 == x > 0"));
    }

    #[tokio::test]
    async fn test_tlc_parse_tla() {
        let config = ProverConfig {
            executable: PathBuf::from("tlc2"),
            timeout: 30,
            ..Default::default()
        };

        let backend = TLCBackend::new(config);

        let tla = r#"
---- MODULE Counter ----
EXTENDS Naturals
VARIABLE counter
Init == counter = 0
Next == counter' = counter + 1
THEOREM Spec => []<>(counter > 10)
====
"#;

        let state = backend.parse_string(tla).await.unwrap();

        assert!(!state.context.definitions.is_empty(), "Should have parsed definitions");
        assert!(!state.goals.is_empty(), "Should have parsed theorem");
    }

    #[test]
    fn test_tlc_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("tlc2"),
            timeout: 30,
            ..Default::default()
        };

        let backend = TLCBackend::new(config);

        let success = "Model checking completed. No error has been found.\nFinished in 00:01:23\n";
        assert!(backend.parse_result(success).unwrap());
    }

    #[test]
    fn test_tlc_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("tlc2"),
            timeout: 30,
            ..Default::default()
        };

        let backend = TLCBackend::new(config);

        let inv_fail = "Invariant TypeOK is violated.\n";
        assert!(!backend.parse_result(inv_fail).unwrap());

        let deadlock = "Deadlock reached.\n";
        assert!(!backend.parse_result(deadlock).unwrap());
    }

    #[test]
    fn test_tlc_cfg_generation() {
        let config = ProverConfig {
            executable: PathBuf::from("tlc2"),
            timeout: 30,
            ..Default::default()
        };

        let backend = TLCBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "inv_0".to_string(),
            target: Term::Const("TypeOK".to_string()),
            hypotheses: vec![],
        });
        state.goals.push(Goal {
            id: "prop_0".to_string(),
            target: Term::Const("[]<>(done)".to_string()),
            hypotheses: vec![],
        });

        let cfg = backend.to_cfg(&state);
        assert!(cfg.contains("INVARIANT inv_0"));
        assert!(cfg.contains("PROPERTY prop_0"));
    }
}
