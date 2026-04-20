// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Tamarin Security Protocol Prover Backend
//!
//! Tamarin is a powerful tool for the symbolic verification of security
//! protocols. It operates on multiset rewriting rules in the Dolev-Yao model
//! and takes .spthy (security protocol theory) files as input.
//!
//! Features:
//! - Multiset rewriting rules for protocol modelling
//! - Dolev-Yao adversary model (symbolic cryptography)
//! - Lemma verification (trace properties, equivalence properties)
//! - Both automatic (`--prove`) and interactive proving modes
//! - Equational theories (Diffie-Hellman, bilinear pairings, etc.)
//! - Restriction rules for constraining protocol traces
//! - Built-in support for hashing, signing, encryption primitives

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// Tamarin security protocol prover backend
///
/// Integrates the Tamarin prover for symbolic verification of security
/// protocols. Tamarin uses multiset rewriting rules to model protocols
/// and reasons about all possible interleavings under the Dolev-Yao
/// adversary model. Input files use the .spthy format.
///
/// The backend supports both automatic proving (`tamarin-prover --prove`)
/// and structured interactive proof construction via ECHIDNA tactics.
pub struct TamarinBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl TamarinBackend {
    /// Create a new Tamarin backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        TamarinBackend { config }
    }

    /// Convert proof state to Tamarin .spthy format
    ///
    /// Generates a valid security protocol theory from the ECHIDNA proof state.
    /// Axioms become multiset rewriting rules, definitions become function
    /// declarations and equations, and goals become lemmas to verify.
    fn to_spthy(&self, state: &ProofState) -> Result<String> {
        let mut spthy = String::new();

        // Header comment
        spthy.push_str("/* ECHIDNA Tamarin Export */\n\n");

        // Theory header — derive a theory name from the first goal or use default
        let theory_name = state
            .goals
            .first()
            .map(|g| {
                // Sanitise goal ID into a valid Tamarin identifier
                g.id.chars()
                    .map(|c| {
                        if c.is_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect::<String>()
            })
            .unwrap_or_else(|| "echidna_theory".to_string());

        spthy.push_str(&format!("theory {}\nbegin\n\n", theory_name));

        // Built-in functions (default to hashing)
        spthy.push_str("builtins: hashing, signing, symmetric-encryption\n\n");

        // Add definitions as function declarations or equations
        for def in &state.context.definitions {
            spthy.push_str(&format!("/* definition: {} */\n", def));
        }

        // Add axioms as multiset rewriting rules or restrictions
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            // If the axiom text already looks like Tamarin syntax, include directly
            if axiom.contains("rule ")
                || axiom.contains("restriction ")
                || axiom.contains("lemma ")
                || axiom.contains("builtins:")
                || axiom.contains("functions:")
                || axiom.contains("equations:")
            {
                spthy.push_str(axiom);
                spthy.push('\n');
            } else {
                // Wrap as a commented rule placeholder
                spthy.push_str(&format!("/* axiom_{}: {} */\n", i, axiom));
            }
        }

        spthy.push('\n');

        // Add goals as lemmas to verify
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            // Sanitise the goal ID for Tamarin identifiers
            let lemma_name = goal
                .id
                .chars()
                .map(|c| {
                    if c.is_alphanumeric() || c == '_' {
                        c
                    } else {
                        '_'
                    }
                })
                .collect::<String>();

            spthy.push_str(&format!("lemma {}:\n  \"{}\"\n\n", lemma_name, target_str));
        }

        spthy.push_str("end\n");

        Ok(spthy)
    }

    /// Parse Tamarin verification output to determine success or failure
    ///
    /// Tamarin reports verification results per-lemma:
    /// - "verified" indicates the lemma holds
    /// - "falsified" indicates a counterexample (attack) was found
    /// - "analysis incomplete" indicates the prover could not decide
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Check for any falsified lemma — indicates an attack was found
        if output.contains("falsified") {
            return Ok(false);
        }

        // Check for successful verification of all lemmas
        if output.contains("verified") {
            // Ensure no lemma was left incomplete alongside verified ones
            if output.contains("analysis incomplete") {
                return Err(anyhow!(
                    "Tamarin analysis incomplete: some lemmas could not be decided"
                ));
            }
            return Ok(true);
        }

        // Check for analysis timeout or incompleteness
        if output.contains("analysis incomplete") {
            return Err(anyhow!(
                "Tamarin analysis incomplete: could not decide all lemmas"
            ));
        }

        // Check for parse errors
        if output.contains("parse error") || output.contains("wellformedness check failed") {
            return Err(anyhow!(
                "Tamarin parse/wellformedness error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        // Inconclusive — no clear result markers found
        Err(anyhow!(
            "Tamarin inconclusive or error: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse a .spthy file to extract rules, lemmas, restrictions,
    /// builtins, and function declarations into the proof state
    fn parse_spthy(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty()
                || trimmed.starts_with("/*")
                || trimmed.starts_with("//")
                || trimmed.starts_with("*")
            {
                continue;
            }

            // Detect theory header (informational, not stored as axiom)
            if trimmed.starts_with("theory ") || trimmed == "begin" || trimmed == "end" {
                continue;
            }

            // Detect builtins declarations
            if trimmed.starts_with("builtins:") {
                state.context.definitions.push(Definition {
                    name: "builtins".to_string(),
                    ty: Term::Const("builtin-declaration".to_string()),
                    body: Term::Const(trimmed.to_string()),
                });
            }

            // Detect function declarations
            if trimmed.starts_with("functions:") {
                state.context.definitions.push(Definition {
                    name: "functions".to_string(),
                    ty: Term::Const("function-declaration".to_string()),
                    body: Term::Const(trimmed.to_string()),
                });
            }

            // Detect equations
            if trimmed.starts_with("equations:") {
                state.context.definitions.push(Definition {
                    name: "equations".to_string(),
                    ty: Term::Const("equation-declaration".to_string()),
                    body: Term::Const(trimmed.to_string()),
                });
            }

            // Detect multiset rewriting rules
            if trimmed.starts_with("rule ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect restrictions (formerly axioms in older Tamarin)
            if trimmed.starts_with("restriction ") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Detect lemmas — these become goals to verify
            if trimmed.starts_with("lemma ") {
                // Extract lemma name
                let after_lemma = trimmed.trim_start_matches("lemma ");
                // Lemma name ends at ':' or '[' (for annotations like [reuse])
                let name_end = after_lemma
                    .find([':', '[', ' '])
                    .unwrap_or(after_lemma.len());
                let lemma_name = after_lemma[..name_end].trim().to_string();

                state.goals.push(Goal {
                    id: lemma_name.clone(),
                    target: Term::Const(format!("lemma {}", lemma_name)),
                    hypotheses: vec![],
                });
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for TamarinBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Tamarin
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run tamarin-prover --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Tamarin typically outputs version to stdout
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("unknown").to_string()
        } else {
            stderr.lines().next().unwrap_or("unknown").to_string()
        };

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read .spthy file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_spthy(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddRule: add a multiset rewriting rule to the protocol model
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "tamarin" && command == "add_rule" => {
                let rule_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.context.axioms.push(format!("rule {}", rule_text));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddLemma: add a security lemma to verify
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "tamarin" && command == "add_lemma" => {
                let lemma_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("lemma_{}", new_state.goals.len()),
                    target: Term::Const(format!("lemma {}", lemma_text)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddRestriction: add a trace restriction (constraint on valid traces)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "tamarin" && command == "add_restriction" => {
                let restriction_text = args.join(" ");
                let mut new_state = state.clone();
                new_state
                    .context
                    .axioms
                    .push(format!("restriction {}", restriction_text));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddBuiltin: add a cryptographic builtin (hashing, signing, etc.)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "tamarin" && command == "add_builtin" => {
                let builtin_text = args.join(", ");
                let mut new_state = state.clone();
                new_state.context.definitions.push(Definition {
                    name: "builtins".to_string(),
                    ty: Term::Const("builtin-declaration".to_string()),
                    body: Term::Const(format!("builtins: {}", builtin_text)),
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for Tamarin prover",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let spthy_code = self.to_spthy(state)?;

        // Write .spthy to a temporary file (tamarin-prover requires a file)
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for Tamarin")?;
        let tmp_file = tmp_dir.path().join("theory.spthy");
        tokio::fs::write(&tmp_file, &spthy_code)
            .await
            .context("Failed to write temporary .spthy file")?;

        // Run tamarin-prover --prove which attempts automatic proof of all lemmas
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            Command::new(&self.config.executable)
                .arg("--prove")
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "Tamarin verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute tamarin-prover")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Combine stdout and stderr for parsing
        let combined = format!("{}\n{}", stdout, stderr);

        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_spthy(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "tamarin".to_string(),
                command: "add_rule".to_string(),
                args: vec!["Fresh: [ Fr(~k) ] --> [ !Key(~k) ]".to_string()],
            },
            Tactic::Custom {
                prover: "tamarin".to_string(),
                command: "add_lemma".to_string(),
                args: vec!["secrecy: All x #i. Secret(x) @i ==> not (Ex #j. K(x) @j)".to_string()],
            },
            Tactic::Custom {
                prover: "tamarin".to_string(),
                command: "add_restriction".to_string(),
                args: vec!["Eq: All x y #i. Eq(x, y) @i ==> x = y".to_string()],
            },
            Tactic::Custom {
                prover: "tamarin".to_string(),
                command: "add_builtin".to_string(),
                args: vec!["diffie-hellman".to_string()],
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
    async fn test_tamarin_spthy_export() {
        let config = ProverConfig {
            executable: PathBuf::from("tamarin-prover"),
            timeout: 60,
            ..Default::default()
        };

        let backend = TamarinBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "secrecy".to_string(),
            target: Term::Const("All x #i. Secret(x) @i ==> not (Ex #j. K(x) @j)".to_string()),
            hypotheses: vec![],
        });

        let spthy = backend.to_spthy(&state).unwrap();

        assert!(spthy.contains("ECHIDNA Tamarin Export"));
        assert!(spthy.contains("theory secrecy"));
        assert!(spthy.contains("begin"));
        assert!(spthy.contains("end"));
        assert!(spthy.contains("lemma secrecy:"));
    }

    #[tokio::test]
    async fn test_tamarin_parse_spthy() {
        let config = ProverConfig {
            executable: PathBuf::from("tamarin-prover"),
            timeout: 60,
            ..Default::default()
        };

        let backend = TamarinBackend::new(config);

        let spthy = r#"
theory NeedhamSchroeder
begin

builtins: symmetric-encryption

rule Register_Key:
    [ Fr(~k) ] --> [ !SharedKey($A, $B, ~k) ]

rule Send:
    [ !SharedKey($A, $B, k) ]
    --[ Secret(k) ]->
    [ Out(senc(~m, k)) ]

restriction Eq:
    "All x y #i. Eq(x, y) @i ==> x = y"

lemma secrecy:
    "All x #i. Secret(x) @i ==> not (Ex #j. K(x) @j)"

lemma authentication [reuse]:
    "All a b t #i. Commit(a, b, t) @i ==> Ex #j. Running(a, b, t) @j"

end
"#;

        let state = backend.parse_string(spthy).await.unwrap();

        // Should have found builtins as a definition
        assert!(
            state
                .context
                .definitions
                .iter()
                .any(|d| d.name == "builtins"),
            "Should have parsed builtins declaration"
        );

        // Should have found rules and restriction as axioms
        assert!(
            state.context.axioms.iter().any(|a| a.contains("rule ")),
            "Should have parsed rules"
        );
        assert!(
            state
                .context
                .axioms
                .iter()
                .any(|a| a.contains("restriction ")),
            "Should have parsed restrictions"
        );

        // Should have found both lemmas as goals
        assert_eq!(state.goals.len(), 2, "Should have parsed two lemmas");
        assert_eq!(state.goals[0].id, "secrecy");
        assert_eq!(state.goals[1].id, "authentication");
    }

    #[test]
    fn test_tamarin_parse_result_verified() {
        let config = ProverConfig {
            executable: PathBuf::from("tamarin-prover"),
            timeout: 60,
            ..Default::default()
        };

        let backend = TamarinBackend::new(config);

        let success_output = "summary of summaries:\n  secrecy (all-traces): verified (4 steps)\n";
        assert!(backend.parse_result(success_output).unwrap());
    }

    #[test]
    fn test_tamarin_parse_result_falsified() {
        let config = ProverConfig {
            executable: PathBuf::from("tamarin-prover"),
            timeout: 60,
            ..Default::default()
        };

        let backend = TamarinBackend::new(config);

        let failure_output =
            "summary of summaries:\n  secrecy (all-traces): falsified - found trace (8 steps)\n";
        assert!(!backend.parse_result(failure_output).unwrap());
    }

    #[test]
    fn test_tamarin_parse_result_incomplete() {
        let config = ProverConfig {
            executable: PathBuf::from("tamarin-prover"),
            timeout: 60,
            ..Default::default()
        };

        let backend = TamarinBackend::new(config);

        let incomplete_output = "summary of summaries:\n  secrecy: analysis incomplete\n";
        assert!(backend.parse_result(incomplete_output).is_err());
    }
}
