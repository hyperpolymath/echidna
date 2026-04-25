// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Alloy Relational Model Finder Backend
//!
//! Alloy is a lightweight formal modelling language based on relational logic,
//! with an automatic analyser that finds instances and counterexamples.
//! The Alloy Analyzer uses SAT solving under the hood to explore bounded
//! model spaces.
//!
//! Input format: Alloy specification language (.als files).
//! Executable: `alloy` (Java JAR, invoked via command-line interface).
//!
//! Features:
//! - First-order relational logic with transitive closure
//! - Automatic instance finding (run commands)
//! - Counterexample finding (check commands)
//! - Bounded analysis with configurable scopes
//! - Signature hierarchies and multiplicity constraints

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// Alloy relational model finder backend
///
/// Integrates the Alloy Analyzer for bounded verification of relational
/// models. Uses SAT-based analysis to find instances satisfying predicates
/// or counterexamples violating assertions.
pub struct AlloyBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl AlloyBackend {
    /// Create a new Alloy backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        AlloyBackend { config }
    }

    /// Convert proof state to Alloy specification format
    ///
    /// Generates a valid Alloy module from the ECHIDNA proof state.
    /// Definitions become signature declarations, axioms become facts,
    /// and goals become assertions with check commands.
    fn to_alloy(&self, state: &ProofState) -> Result<String> {
        let mut als = String::new();

        // Header
        als.push_str("// ECHIDNA Alloy Export\n");
        als.push_str("module EchidnaModel\n\n");

        // Check if axioms contain raw Alloy (sig declarations)
        let has_raw_alloy = state.context.axioms.iter().any(|a| a.contains("sig "));

        if has_raw_alloy {
            // Include raw Alloy axioms directly
            for axiom in &state.context.axioms {
                als.push_str(axiom);
                als.push('\n');
            }
        } else {
            // Add definitions as abstract signatures
            for def in &state.context.definitions {
                als.push_str(&format!("// definition: {}\n", def.name));
            }

            // Add axioms as facts
            if !state.context.axioms.is_empty() {
                als.push_str("fact Constraints {\n");
                for axiom in &state.context.axioms {
                    als.push_str(&format!("  {}\n", axiom));
                }
                als.push_str("}\n\n");
            }
        }

        // Add goals as assertions with check commands
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            als.push_str(&format!("assert {} {{\n  {}\n}}\n", goal.id, target_str));
            als.push_str(&format!("check {} for 5\n\n", goal.id));
        }

        Ok(als)
    }

    /// Parse Alloy Analyzer output to determine success or failure
    ///
    /// Alloy reports "No counterexample found" when an assertion holds
    /// within the given scope, or "Counterexample found" when it fails.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Check for no counterexample (assertion holds within scope)
        if output.contains("No counterexample found")
            || output.contains("no counterexample")
            || output.contains("0 counterexample")
        {
            return Ok(true);
        }

        // Check for counterexample found (assertion violated)
        if output.contains("Counterexample found")
            || output.contains("counterexample found")
            || output.contains("Instance found")
        {
            return Ok(false);
        }

        // Check for unsatisfiable (no instance exists)
        if output.contains("No instance found") || output.contains("Unsatisfiable") {
            return Ok(true);
        }

        // Check for error
        if output.contains("Syntax error") || output.contains("Type error") {
            return Err(anyhow!(
                "Alloy error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        Err(anyhow!(
            "Alloy inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse Alloy source to extract signatures, facts, predicates,
    /// and assertions into the proof state
    fn parse_alloy(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("--") {
                continue;
            }

            // Detect signature declarations
            if trimmed.contains("sig ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect fact blocks
            if trimmed.starts_with("fact ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect predicate definitions
            if trimmed.starts_with("pred ") {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("ALLOY_DEF".to_string()),
                    body: Term::Const(trimmed.to_string()),
                    type_info: None,
                });
            }

            // Detect function definitions
            if trimmed.starts_with("fun ") {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("ALLOY_DEF".to_string()),
                    body: Term::Const(trimmed.to_string()),
                    type_info: None,
                });
            }

            // Detect assertions
            if trimmed.starts_with("assert ") {
                let assertion = trimmed.trim_start_matches("assert ").trim();
                state.goals.push(Goal {
                    id: format!("assert_{}", state.goals.len()),
                    target: Term::Const(assertion.to_string()),
                    hypotheses: vec![],
                });
            }

            // Detect check commands
            if trimmed.starts_with("check ") {
                let check = trimmed.trim_start_matches("check ").trim();
                state.goals.push(Goal {
                    id: format!("check_{}", state.goals.len()),
                    target: Term::Const(check.to_string()),
                    hypotheses: vec![],
                });
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for AlloyBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Alloy
    }

    async fn version(&self) -> Result<String> {
        // Alloy is typically a Java JAR; try getting version info
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run alloy --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("Alloy") || l.contains("version") || l.contains("Version"))
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read Alloy file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_alloy(content)?;
        state.metadata.insert(
            "alloy_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddAssertion: add an assertion to check
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "alloy" && command == "add_assertion" => {
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

            // SetScope: set the analysis scope (bound)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "alloy" && command == "set_scope" => {
                let scope = args.first().cloned().unwrap_or_else(|| "5".to_string());
                let mut new_state = state.clone();
                new_state
                    .metadata
                    .insert("scope".to_string(), serde_json::Value::String(scope));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddFact: add a fact constraint
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "alloy" && command == "add_fact" => {
                let fact_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.context.axioms.push(fact_text);
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for Alloy model finder",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Prefer the original .als source; `to_alloy(state)` round-trips
        // through the generic Term IR and cannot reconstruct real models.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout),
                Command::new(&self.config.executable)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| anyhow!("Alloy timed out after {} seconds", self.config.timeout))?
            .context("Failed to execute Alloy")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return self.parse_result(&combined);
        }

        let alloy_code = if let Some(src) = state
            .metadata
            .get("alloy_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_alloy(state)?
        };

        // Write Alloy to a temporary file
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for Alloy")?;
        let tmp_file = tmp_dir.path().join("model.als");
        tokio::fs::write(&tmp_file, &alloy_code)
            .await
            .context("Failed to write temporary Alloy file")?;

        // Run Alloy Analyzer in command-line mode
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("Alloy timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute Alloy")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_alloy(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "alloy".to_string(),
                command: "add_assertion".to_string(),
                args: vec!["all x: Node | x in x.^next".to_string()],
            },
            Tactic::Custom {
                prover: "alloy".to_string(),
                command: "set_scope".to_string(),
                args: vec!["10".to_string()],
            },
            Tactic::Custom {
                prover: "alloy".to_string(),
                command: "add_fact".to_string(),
                args: vec!["no iden & next".to_string()],
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
    async fn test_alloy_export() {
        let config = ProverConfig {
            executable: PathBuf::from("alloy"),
            timeout: 30,
            ..Default::default()
        };

        let backend = AlloyBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "no_cycles".to_string(),
            target: Term::Const("all n: Node | n not in n.^next".to_string()),
            hypotheses: vec![],
        });

        let als = backend.to_alloy(&state).unwrap();

        assert!(als.contains("ECHIDNA Alloy Export"));
        assert!(als.contains("module EchidnaModel"));
        assert!(als.contains("assert no_cycles"));
        assert!(als.contains("check no_cycles for 5"));
    }

    #[tokio::test]
    async fn test_alloy_parse() {
        let config = ProverConfig {
            executable: PathBuf::from("alloy"),
            timeout: 30,
            ..Default::default()
        };

        let backend = AlloyBackend::new(config);

        let als = r#"
module LinkedList
sig Node { next: lone Node }
fact { no iden & next }
pred connected { all n: Node | Node in n.*next }
assert NoSelfLoop { no n: Node | n = n.next }
check NoSelfLoop for 5
"#;

        let state = backend.parse_string(als).await.unwrap();

        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed sigs and facts"
        );
        assert!(
            !state.context.definitions.is_empty(),
            "Should have parsed predicates"
        );
        assert!(
            !state.goals.is_empty(),
            "Should have parsed assertions/checks"
        );
    }

    #[test]
    fn test_alloy_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("alloy"),
            timeout: 30,
            ..Default::default()
        };

        let backend = AlloyBackend::new(config);

        let success = "Executing \"Check NoSelfLoop for 5\"\nNo counterexample found. Assertion may be valid.\n";
        assert!(backend.parse_result(success).unwrap());
    }

    #[test]
    fn test_alloy_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("alloy"),
            timeout: 30,
            ..Default::default()
        };

        let backend = AlloyBackend::new(config);

        let failure =
            "Executing \"Check NoSelfLoop for 5\"\nCounterexample found. Assertion is invalid.\n";
        assert!(!backend.parse_result(failure).unwrap());
    }

    #[test]
    fn test_alloy_parse_result_unsatisfiable() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);

        let output = "Unsatisfiable. No instance found.\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_alloy_parse_result_syntax_error() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);

        let output = "Syntax error at line 5\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_alloy_parse_result_instance_found() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);

        let output = "Instance found. Predicate is consistent.\n";
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_alloy_kind() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Alloy);
    }

    #[tokio::test]
    async fn test_alloy_export_with_axioms() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("no iden & next".to_string());
        state.goals.push(Goal {
            id: "no_cycles".to_string(),
            target: Term::Const("all n: Node | n not in n.^next".to_string()),
            hypotheses: vec![],
        });

        let als = backend.to_alloy(&state).unwrap();
        assert!(als.contains("fact Constraints"));
        assert!(als.contains("no iden & next"));
    }

    #[tokio::test]
    async fn test_alloy_parse_fun_definitions() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);

        let als = "fun f[n: Node] : set Node { n.^next }\n";
        let state = backend.parse_string(als).await.unwrap();

        assert_eq!(state.context.definitions.len(), 1);
    }

    #[tokio::test]
    async fn test_alloy_suggest_tactics() {
        let config = ProverConfig::default();
        let backend = AlloyBackend::new(config);
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 3).await.unwrap();
        assert_eq!(tactics.len(), 3);
    }
}
