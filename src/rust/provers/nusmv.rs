// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! NuSMV / nuXmv Symbolic Model Checker Backend
//!
//! NuSMV is a symbolic model checker for verifying finite state systems against
//! CTL and LTL temporal logic specifications. nuXmv extends NuSMV with
//! infinite-state model checking capabilities via SMT solvers.
//!
//! Input format: SMV specification language (.smv files).
//! Output: property verification results (TRUE/FALSE with counterexamples).
//!
//! Features:
//! - CTL and LTL model checking
//! - BDD-based and SAT-based verification
//! - Bounded model checking (BMC)
//! - Counterexample generation
//! - Fairness constraints

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// NuSMV / nuXmv symbolic model checker backend
///
/// Integrates the NuSMV symbolic model checker for verifying finite state
/// systems. Supports both CTL and LTL property specification, BDD-based
/// and SAT-based (BMC) verification modes.
pub struct NuSMVBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl NuSMVBackend {
    /// Create a new NuSMV backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        NuSMVBackend { config }
    }

    /// Convert proof state to SMV specification format
    ///
    /// Generates a valid SMV model from the ECHIDNA proof state.
    /// Axioms become variable declarations and transition relations,
    /// goals become CTL/LTL property specifications.
    fn to_smv(&self, state: &ProofState) -> Result<String> {
        let mut smv = String::new();

        // Header comment
        smv.push_str("-- ECHIDNA NuSMV Export\n\n");

        // Check if any axiom contains raw SMV (MODULE declaration)
        let has_raw_smv = state.context.axioms.iter().any(|a| a.contains("MODULE"));

        if has_raw_smv {
            // Include raw SMV axioms directly
            for axiom in &state.context.axioms {
                smv.push_str(axiom);
                smv.push('\n');
            }
        } else {
            // Generate a minimal MODULE main wrapper
            smv.push_str("MODULE main\n");

            // Add definitions as variable declarations
            if !state.context.definitions.is_empty() {
                smv.push_str("  VAR\n");
                for def in &state.context.definitions {
                    smv.push_str(&format!("    {} : boolean;\n", def.name));
                }
            }

            // Add axioms as ASSIGN or TRANS constraints
            if !state.context.axioms.is_empty() {
                smv.push_str("  TRANS\n");
                for (i, axiom) in state.context.axioms.iter().enumerate() {
                    if i > 0 {
                        smv.push_str("  & ");
                    } else {
                        smv.push_str("    ");
                    }
                    smv.push_str(axiom);
                    smv.push('\n');
                }
            }
        }

        // Add goals as CTLSPEC or LTLSPEC properties
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            if target_str.starts_with("ltl ")
                || target_str.contains("F ")
                || target_str.contains("G ")
            {
                smv.push_str(&format!("  LTLSPEC {}\n", target_str));
            } else {
                smv.push_str(&format!("  CTLSPEC {}\n", target_str));
            }
        }

        Ok(smv)
    }

    /// Parse NuSMV verification output to determine success or failure
    ///
    /// NuSMV reports "is true" for satisfied properties and "is false"
    /// for violated properties, along with counterexample traces.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let mut found_result = false;

        for line in output.lines() {
            let trimmed = line.trim();

            // Property verified successfully
            if trimmed.contains("is true") {
                found_result = true;
                // Continue checking — all properties must pass
            }

            // Property violated (counterexample found)
            if trimmed.contains("is false") {
                return Ok(false);
            }

            // Error in specification
            if trimmed.starts_with("***") && trimmed.contains("error") {
                return Err(anyhow!("NuSMV error: {}", trimmed));
            }
        }

        if found_result {
            Ok(true)
        } else {
            Err(anyhow!(
                "NuSMV inconclusive: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }

    /// Parse SMV source to extract module definitions, variable declarations,
    /// and property specifications into the proof state
    fn parse_smv(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("--") {
                continue;
            }

            // Detect MODULE declarations
            if trimmed.starts_with("MODULE") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect VAR declarations
            if trimmed.contains(": boolean") || trimmed.contains(": 0..") {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("SMV_VAR".to_string()),
                    body: Term::Const(trimmed.to_string()),
                    type_info: None,
                });
            }

            // Detect CTLSPEC properties
            if trimmed.starts_with("CTLSPEC") || trimmed.starts_with("SPEC") {
                let spec = trimmed
                    .trim_start_matches("CTLSPEC")
                    .trim_start_matches("SPEC")
                    .trim();
                state.goals.push(Goal {
                    id: format!("ctl_{}", state.goals.len()),
                    target: Term::Const(spec.to_string()),
                    hypotheses: vec![],
                });
            }

            // Detect LTLSPEC properties
            if trimmed.starts_with("LTLSPEC") {
                let spec = trimmed.trim_start_matches("LTLSPEC").trim();
                state.goals.push(Goal {
                    id: format!("ltl_{}", state.goals.len()),
                    target: Term::Const(spec.to_string()),
                    hypotheses: vec![],
                });
            }

            // Detect TRANS constraints
            if trimmed.starts_with("TRANS") {
                let trans = trimmed.trim_start_matches("TRANS").trim();
                state.context.axioms.push(trans.to_string());
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for NuSMVBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::NuSMV
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-help")
            .output()
            .await
            .context("Failed to run nuXmv/NuSMV")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // NuSMV/nuXmv prints version info in the first line
        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("NuSMV") || l.contains("nuXmv") || l.contains("version"))
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read SMV file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_smv(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddCTLSpec: add a CTL property specification
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "nusmv" && command == "add_ctlspec" => {
                let spec_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("ctl_{}", new_state.goals.len()),
                    target: Term::Const(spec_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddLTLSpec: add an LTL property specification
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "nusmv" && command == "add_ltlspec" => {
                let spec_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("ltl_{}", new_state.goals.len()),
                    target: Term::Const(spec_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // BMC: enable bounded model checking mode
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "nusmv" && command == "bmc" => {
                let mut new_state = state.clone();
                let bound = args.first().cloned().unwrap_or_else(|| "10".to_string());
                new_state
                    .metadata
                    .insert("bmc_bound".to_string(), serde_json::Value::String(bound));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for NuSMV model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let smv_code = self.to_smv(state)?;

        // Write SMV to a temporary file (nuXmv requires a file)
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for NuSMV")?;
        let tmp_file = tmp_dir.path().join("model.smv");
        tokio::fs::write(&tmp_file, &smv_code)
            .await
            .context("Failed to write temporary SMV file")?;

        // Run NuSMV/nuXmv on the file
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("NuSMV timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute NuSMV")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_smv(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "nusmv".to_string(),
                command: "add_ctlspec".to_string(),
                args: vec!["AG (!error)".to_string()],
            },
            Tactic::Custom {
                prover: "nusmv".to_string(),
                command: "add_ltlspec".to_string(),
                args: vec!["G F ready".to_string()],
            },
            Tactic::Custom {
                prover: "nusmv".to_string(),
                command: "bmc".to_string(),
                args: vec!["20".to_string()],
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
    async fn test_nusmv_smv_export() {
        let config = ProverConfig {
            executable: PathBuf::from("nuXmv"),
            timeout: 30,
            ..Default::default()
        };

        let backend = NuSMVBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "ctl_0".to_string(),
            target: Term::Const("AG (!error)".to_string()),
            hypotheses: vec![],
        });

        let smv = backend.to_smv(&state).unwrap();

        assert!(smv.contains("ECHIDNA NuSMV Export"));
        assert!(smv.contains("MODULE main"));
        assert!(smv.contains("AG (!error)"));
    }

    #[tokio::test]
    async fn test_nusmv_parse_smv() {
        let config = ProverConfig {
            executable: PathBuf::from("nuXmv"),
            timeout: 30,
            ..Default::default()
        };

        let backend = NuSMVBackend::new(config);

        let smv = r#"
MODULE main
  VAR
    state : boolean;
  TRANS
    next(state) = !state
  CTLSPEC AG (state -> AF !state)
  LTLSPEC G F state
"#;

        let state = backend.parse_string(smv).await.unwrap();

        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed module/transitions"
        );
        assert_eq!(state.goals.len(), 2, "Should have parsed CTL and LTL specs");
    }

    #[test]
    fn test_nusmv_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("nuXmv"),
            timeout: 30,
            ..Default::default()
        };

        let backend = NuSMVBackend::new(config);

        let success = "-- specification AG (!error) is true\n";
        assert!(backend.parse_result(success).unwrap());
    }

    #[test]
    fn test_nusmv_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("nuXmv"),
            timeout: 30,
            ..Default::default()
        };

        let backend = NuSMVBackend::new(config);

        let failure = "-- specification AG (x = 1) is false\n-- as demonstrated by the following execution sequence\n";
        assert!(!backend.parse_result(failure).unwrap());
    }

    #[test]
    fn test_nusmv_parse_result_error() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);

        let output = "*** error in model specification\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_nusmv_parse_result_inconclusive() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);

        let output = "no property results here\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_nusmv_kind() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::NuSMV);
    }

    #[tokio::test]
    async fn test_nusmv_smv_export_with_ltlspec() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "ltl_0".to_string(),
            target: Term::Const("G F ready".to_string()),
            hypotheses: vec![],
        });

        let smv = backend.to_smv(&state).unwrap();
        assert!(smv.contains("LTLSPEC"));
        assert!(smv.contains("G F ready"));
    }

    #[tokio::test]
    async fn test_nusmv_parse_smv_trans() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);

        let smv = "TRANS next(state) = !state\n";
        let state = backend.parse_string(smv).await.unwrap();

        assert!(!state.context.axioms.is_empty());
    }

    #[tokio::test]
    async fn test_nusmv_suggest_tactics() {
        let config = ProverConfig::default();
        let backend = NuSMVBackend::new(config);
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 2).await.unwrap();
        assert_eq!(tactics.len(), 2);
    }
}
