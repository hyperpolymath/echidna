// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! PRISM Probabilistic Model Checker Backend
//!
//! PRISM is a probabilistic model checker for formal modelling and analysis
//! of systems that exhibit random or probabilistic behaviour. It supports
//! DTMCs, CTMCs, MDPs, and PTAs.
//!
//! Input format: PRISM language (.pm/.prism files) with properties (.pctl/.csl).
//! Executable: `prism`.
//!
//! Features:
//! - DTMC (Discrete-Time Markov Chain) analysis
//! - CTMC (Continuous-Time Markov Chain) analysis
//! - MDP (Markov Decision Process) analysis
//! - PTA (Probabilistic Timed Automata) analysis
//! - PCTL / CSL / LTL property checking
//! - Quantitative probability computation
//! - Reward-based properties

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// PRISM probabilistic model checker backend
///
/// Integrates the PRISM model checker for analysing probabilistic systems.
/// Supports multiple model types (DTMC, CTMC, MDP) and property languages
/// (PCTL, CSL, LTL, reward-based).
pub struct PrismBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl PrismBackend {
    /// Create a new PRISM backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        PrismBackend { config }
    }

    /// Convert proof state to PRISM model format
    ///
    /// Generates a valid PRISM model from the ECHIDNA proof state.
    /// Axioms become module definitions, goals become property specifications.
    fn to_prism_model(&self, state: &ProofState) -> Result<String> {
        let mut model = String::new();

        // Header
        model.push_str("// ECHIDNA PRISM Export\n\n");

        // Determine model type from metadata or default to DTMC
        let model_type = state
            .metadata
            .get("model_type")
            .and_then(|v| v.as_str())
            .unwrap_or("dtmc");
        model.push_str(&format!("{}\n\n", model_type));

        // Check if axioms contain raw PRISM (module declarations)
        let has_raw_prism = state.context.axioms.iter().any(|a| a.contains("module "));

        if has_raw_prism {
            for axiom in &state.context.axioms {
                model.push_str(axiom);
                model.push('\n');
            }
        } else {
            // Generate a minimal module wrapper
            model.push_str("module EchidnaModule\n");

            // Add definitions as variable declarations
            for def in &state.context.definitions {
                model.push_str(&format!("  {}\n", def.name));
            }

            // Add axioms as transitions
            for axiom in &state.context.axioms {
                model.push_str(&format!("  {}\n", axiom));
            }

            model.push_str("endmodule\n");
        }

        Ok(model)
    }

    /// Convert goals to PRISM property specification format
    fn to_prism_properties(&self, state: &ProofState) -> String {
        let mut props = String::new();
        props.push_str("// ECHIDNA PRISM Properties\n\n");

        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            props.push_str(&format!("// Property: {}\n", goal.id));
            props.push_str(&format!("{}\n\n", target_str));
        }

        props
    }

    /// Parse PRISM verification output to determine success or failure
    ///
    /// PRISM reports property results as "Result: true/false" or
    /// probability/reward values depending on the property type.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let mut found_result = false;

        for line in output.lines() {
            let trimmed = line.trim();

            // Boolean property result
            if trimmed.starts_with("Result:") {
                let value = trimmed.trim_start_matches("Result:").trim();
                if value == "true" || value.starts_with("true ") {
                    found_result = true;
                } else if value == "false" || value.starts_with("false ") {
                    return Ok(false);
                }
                // Numerical results (probabilities) are considered informational
            }

            // Property satisfied
            if trimmed.contains("Property satisfied") {
                found_result = true;
            }

            // Property not satisfied
            if trimmed.contains("Property NOT satisfied") {
                return Ok(false);
            }

            // Error
            if trimmed.starts_with("Error:") || trimmed.starts_with("Syntax error") {
                return Err(anyhow!("PRISM error: {}", trimmed));
            }
        }

        if found_result {
            Ok(true)
        } else {
            Err(anyhow!(
                "PRISM inconclusive: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }

    /// Parse PRISM source to extract model type, module definitions,
    /// and property specifications into the proof state
    fn parse_prism(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("//") {
                continue;
            }

            // Detect model type declarations
            if trimmed == "dtmc" || trimmed == "ctmc" || trimmed == "mdp" || trimmed == "pta" {
                state.metadata.insert(
                    "model_type".to_string(),
                    serde_json::Value::String(trimmed.to_string()),
                );
            }

            // Detect module declarations
            if trimmed.starts_with("module ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect variable declarations
            if trimmed.contains(": [") || trimmed.contains(": bool") {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("PRISM_VAR".to_string()),
                    body: Term::Const(trimmed.to_string()),
                    type_info: None,
                });
            }

            // Detect transition rules (lines with -> and :)
            if trimmed.contains("->") && trimmed.contains(":") && !trimmed.starts_with("//") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect property specifications (P, R, S operators)
            if trimmed.starts_with("P")
                && (trimmed.contains("=?") || trimmed.contains(">=") || trimmed.contains("<="))
            {
                state.goals.push(Goal {
                    id: format!("pctl_{}", state.goals.len()),
                    target: Term::Const(trimmed.to_string()),
                    hypotheses: vec![],
                });
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for PrismBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Prism
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run prism -version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("PRISM") || l.contains("version") || l.contains("Version"))
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read PRISM file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_prism(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddProperty: add a PCTL/CSL property to check
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "prism" && command == "add_property" => {
                let prop_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("prop_{}", new_state.goals.len()),
                    target: Term::Const(prop_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // SetModelType: set the model type (dtmc, ctmc, mdp, pta)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "prism" && command == "set_model_type" => {
                let model_type = args.first().cloned().unwrap_or_else(|| "dtmc".to_string());
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "model_type".to_string(),
                    serde_json::Value::String(model_type),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddReward: add a reward structure
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "prism" && command == "add_reward" => {
                let reward_text = args.join(" ");
                let mut new_state = state.clone();
                new_state
                    .context
                    .axioms
                    .push(format!("rewards {}", reward_text));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for PRISM model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let model_code = self.to_prism_model(state)?;
        let props_code = self.to_prism_properties(state);

        // Write model and properties to temporary files
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for PRISM")?;
        let model_file = tmp_dir.path().join("model.pm");
        let props_file = tmp_dir.path().join("props.pctl");

        tokio::fs::write(&model_file, &model_code)
            .await
            .context("Failed to write temporary PRISM model file")?;
        tokio::fs::write(&props_file, &props_code)
            .await
            .context("Failed to write temporary PRISM properties file")?;

        // Run PRISM on the model with properties
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&model_file)
                .arg(&props_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("PRISM timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute PRISM")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_prism_model(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "prism".to_string(),
                command: "add_property".to_string(),
                args: vec!["P>=1 [ F \"done\" ]".to_string()],
            },
            Tactic::Custom {
                prover: "prism".to_string(),
                command: "set_model_type".to_string(),
                args: vec!["dtmc".to_string()],
            },
            Tactic::Custom {
                prover: "prism".to_string(),
                command: "add_reward".to_string(),
                args: vec!["\"time\" true : 1;".to_string()],
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
    async fn test_prism_model_export() {
        let config = ProverConfig {
            executable: PathBuf::from("prism"),
            timeout: 30,
            ..Default::default()
        };

        let backend = PrismBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "reach".to_string(),
            target: Term::Const("P>=1 [ F \"done\" ]".to_string()),
            hypotheses: vec![],
        });

        let model = backend.to_prism_model(&state).unwrap();

        assert!(model.contains("ECHIDNA PRISM Export"));
        assert!(model.contains("dtmc"));
        assert!(model.contains("module EchidnaModule"));
    }

    #[tokio::test]
    async fn test_prism_parse() {
        let config = ProverConfig {
            executable: PathBuf::from("prism"),
            timeout: 30,
            ..Default::default()
        };

        let backend = PrismBackend::new(config);

        let prism = r#"
dtmc
module Coin
  s : [0..2] init 0;
  [] s=0 -> 0.5 : (s'=1) + 0.5 : (s'=2);
endmodule
"#;

        let state = backend.parse_string(prism).await.unwrap();

        assert_eq!(
            state.metadata.get("model_type"),
            Some(&serde_json::Value::String("dtmc".to_string()))
        );
        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed module/transitions"
        );
    }

    #[test]
    fn test_prism_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("prism"),
            timeout: 30,
            ..Default::default()
        };

        let backend = PrismBackend::new(config);

        let success = "Model checking: P>=1 [ F \"done\" ]\nResult: true\n";
        assert!(backend.parse_result(success).unwrap());
    }

    #[test]
    fn test_prism_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("prism"),
            timeout: 30,
            ..Default::default()
        };

        let backend = PrismBackend::new(config);

        let failure = "Model checking: P>=0.9 [ F \"done\" ]\nResult: false\n";
        assert!(!backend.parse_result(failure).unwrap());
    }

    #[test]
    fn test_prism_properties_export() {
        let config = ProverConfig {
            executable: PathBuf::from("prism"),
            timeout: 30,
            ..Default::default()
        };

        let backend = PrismBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "reach".to_string(),
            target: Term::Const("P>=1 [ F \"done\" ]".to_string()),
            hypotheses: vec![],
        });

        let props = backend.to_prism_properties(&state);
        assert!(props.contains("P>=1 [ F \"done\" ]"));
    }
}
