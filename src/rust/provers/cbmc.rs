// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! CBMC Bounded Model Checker Backend
//!
//! CBMC (C Bounded Model Checker) is a bounded model checker for C and C++
//! programs. It verifies properties such as array bounds, pointer safety,
//! arithmetic overflow, and user-defined assertions (__CPROVER_assert).
//!
//! Features:
//! - Bounded model checking with configurable unwind depth
//! - __CPROVER_assert / __CPROVER_assume primitives
//! - Array bounds and pointer safety checking
//! - Arithmetic overflow detection
//! - Supports ANSI-C and subsets of C++

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Default unwind bound for CBMC bounded model checking
const DEFAULT_UNWIND_BOUND: u32 = 10;

/// CBMC bounded model checker backend
///
/// Integrates the CBMC bounded model checker for verifying C programs.
/// Uses `cbmc --unwind N program.c` to verify assertions up to a given
/// loop unrolling bound.
pub struct CBMCBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,

    /// Unwind bound for loop unrolling (default: 10)
    unwind_bound: u32,
}

impl CBMCBackend {
    /// Create a new CBMC backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        CBMCBackend {
            config,
            unwind_bound: DEFAULT_UNWIND_BOUND,
        }
    }

    /// Convert proof state to C source with CPROVER assertions
    ///
    /// Generates a valid C program from the ECHIDNA proof state.
    /// Goals become __CPROVER_assert calls, axioms become declarations,
    /// and assumptions become __CPROVER_assume calls.
    fn to_c_source(&self, state: &ProofState) -> Result<String> {
        let mut source = String::new();

        // Header
        source.push_str("/* ECHIDNA CBMC Export */\n");
        source.push_str("#include <assert.h>\n\n");

        // Add axioms as declarations or raw C code
        for axiom in &state.context.axioms {
            if axiom.contains("__CPROVER")
                || axiom.contains("int ")
                || axiom.contains("void ")
                || axiom.contains("#")
            {
                source.push_str(axiom);
                source.push('\n');
            } else {
                source.push_str(&format!("/* axiom: {} */\n", axiom));
            }
        }

        // Add definitions
        for def in &state.context.definitions {
            source.push_str(&format!("/* definition: {} */\n", def));
        }

        // Wrap goals in a main function with __CPROVER_assert
        source.push_str("\nint main() {\n");

        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            source.push_str(&format!(
                "    __CPROVER_assert({}, \"{}\");\n",
                target_str, goal.id
            ));
        }

        source.push_str("    return 0;\n");
        source.push_str("}\n");

        Ok(source)
    }

    /// Parse CBMC output to determine verification result
    ///
    /// CBMC reports "VERIFICATION SUCCESSFUL" when all assertions hold
    /// within the given unwind bound. "VERIFICATION FAILED" indicates
    /// a counterexample was found.
    fn parse_result(&self, output: &str) -> Result<bool> {
        if output.contains("VERIFICATION SUCCESSFUL") {
            return Ok(true);
        }

        if output.contains("VERIFICATION FAILED") {
            return Ok(false);
        }

        // Check for specific CBMC error patterns
        if output.contains("PARSING ERROR") || output.contains("CONVERSION ERROR") {
            return Err(anyhow!(
                "CBMC input error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        Err(anyhow!(
            "CBMC inconclusive or error: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse C source to extract __CPROVER_assert and __CPROVER_assume
    /// directives into the proof state
    fn parse_c_source(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("/*") {
                continue;
            }

            // Detect __CPROVER_assert
            if trimmed.contains("__CPROVER_assert(") || trimmed.contains("__CPROVER_assert (") {
                if let Some(body) = self.extract_cprover_call(trimmed, "__CPROVER_assert") {
                    // __CPROVER_assert has two args: condition and description
                    // Split on first comma to get the condition
                    let condition = if let Some(comma_pos) = body.find(',') {
                        body[..comma_pos].trim().to_string()
                    } else {
                        body.clone()
                    };

                    state.goals.push(Goal {
                        id: format!("cprover_assert_{}", state.goals.len()),
                        target: Term::Const(condition),
                        hypotheses: vec![],
                    });
                }
            }

            // Detect __CPROVER_assume
            if trimmed.contains("__CPROVER_assume(") || trimmed.contains("__CPROVER_assume (") {
                if let Some(body) = self.extract_cprover_call(trimmed, "__CPROVER_assume") {
                    state
                        .context
                        .axioms
                        .push(format!("__CPROVER_assume({})", body));
                }
            }

            // Detect standard assert()
            if trimmed.contains("assert(") && !trimmed.contains("__CPROVER_assert") {
                if let Some(start) = trimmed.find("assert(") {
                    let after = &trimmed[start + 7..];
                    if let Some(end) = after.rfind(')') {
                        let body = after[..end].trim();
                        state.goals.push(Goal {
                            id: format!("assert_{}", state.goals.len()),
                            target: Term::Const(body.to_string()),
                            hypotheses: vec![],
                        });
                    }
                }
            }

            // Detect function declarations as context
            if trimmed.starts_with("int ")
                || trimmed.starts_with("void ")
                || trimmed.starts_with("unsigned ")
                || trimmed.starts_with("char ")
            {
                state.context.axioms.push(trimmed.to_string());
            }
        }

        Ok(state)
    }

    /// Extract the body of a __CPROVER_* call from a source line
    fn extract_cprover_call(&self, line: &str, function_name: &str) -> Option<String> {
        let start_idx = line.find(function_name)?;
        let after_name = &line[start_idx + function_name.len()..];
        let paren_start = after_name.find('(')?;
        let body = &after_name[paren_start + 1..];

        // Find matching closing paren (handle nesting)
        let mut depth = 1;
        let mut end_pos = 0;
        for (i, ch) in body.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end_pos = i;
                        break;
                    }
                },
                _ => {},
            }
        }

        if depth == 0 {
            Some(body[..end_pos].trim().to_string())
        } else {
            None
        }
    }
}

#[async_trait]
impl ProverBackend for CBMCBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::CBMC
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run cbmc --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read C source file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_c_source(content)?;
        state.metadata.insert(
            "cbmc_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // SetUnwindBound: adjust the loop unrolling bound
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "cbmc" && command == "set_unwind_bound" => {
                let bound_str = args
                    .first()
                    .ok_or_else(|| anyhow!("set_unwind_bound requires a numeric argument"))?;
                let _bound: u32 = bound_str
                    .parse()
                    .map_err(|_| anyhow!("Invalid unwind bound: {}", bound_str))?;

                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "cbmc_unwind_bound".to_string(),
                    serde_json::Value::String(bound_str.clone()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddAssumption: add a __CPROVER_assume constraint
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "cbmc" && command == "add_assumption" => {
                let assumption_text = args.join(" ");
                let mut new_state = state.clone();
                new_state
                    .context
                    .axioms
                    .push(format!("__CPROVER_assume({})", assumption_text));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddAssertion: add a new __CPROVER_assert to verify
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "cbmc" && command == "add_assertion" => {
                let assertion_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("cprover_assert_{}", new_state.goals.len()),
                    target: Term::Const(assertion_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for CBMC bounded model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Determine unwind bound from metadata or use default
        let unwind = state
            .metadata
            .get("cbmc_unwind_bound")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(self.unwind_bound);

        // Prefer the original .c source — `to_c_source(state)` round-trips
        // through the generic Term IR and silently mangles anything real.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 10),
                Command::new(&self.config.executable)
                    .arg("--unwind")
                    .arg(format!("{}", unwind))
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| {
                anyhow!(
                    "CBMC verification timed out after {} seconds",
                    self.config.timeout
                )
            })?
            .context("Failed to execute CBMC")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return self.parse_result(&combined);
        }

        let c_source = if let Some(src) = state.metadata.get("cbmc_source").and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_c_source(state)?
        };

        // Write C source to a temporary file (CBMC requires a file)
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for CBMC")?;
        let tmp_file = tmp_dir.path().join("program.c");
        tokio::fs::write(&tmp_file, &c_source)
            .await
            .context("Failed to write temporary C file")?;

        // Run cbmc with unwind bound
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            Command::new(&self.config.executable)
                .arg("--unwind")
                .arg(format!("{}", unwind))
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "CBMC verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute CBMC")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Combine stdout and stderr for parsing
        let combined = format!("{}\n{}", stdout, stderr);

        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_c_source(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "cbmc".to_string(),
                command: "set_unwind_bound".to_string(),
                args: vec!["10".to_string()],
            },
            Tactic::Custom {
                prover: "cbmc".to_string(),
                command: "add_assumption".to_string(),
                args: vec!["x >= 0".to_string()],
            },
            Tactic::Custom {
                prover: "cbmc".to_string(),
                command: "add_assertion".to_string(),
                args: vec!["y > 0".to_string()],
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
    async fn test_cbmc_c_export() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };

        let backend = CBMCBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "assert_0".to_string(),
            target: Term::Const("1 == 1".to_string()),
            hypotheses: vec![],
        });

        let c_source = backend.to_c_source(&state).unwrap();

        assert!(c_source.contains("ECHIDNA CBMC Export"));
        assert!(c_source.contains("__CPROVER_assert(1 == 1"));
        assert!(c_source.contains("int main()"));
    }

    #[tokio::test]
    async fn test_cbmc_parse_c_source() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };

        let backend = CBMCBackend::new(config);

        let c_code = r#"
int x;
void foo() {
    __CPROVER_assume(x > 0);
    __CPROVER_assert(x >= 1, "positive implies >= 1");
}
"#;

        let state = backend.parse_string(c_code).await.unwrap();

        assert!(
            !state.goals.is_empty(),
            "Should have parsed CPROVER_assert goals"
        );
        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed axioms"
        );
    }

    #[test]
    fn test_cbmc_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };

        let backend = CBMCBackend::new(config);

        let success_output = "** 0 of 1 failed\nVERIFICATION SUCCESSFUL\n";
        assert!(backend.parse_result(success_output).unwrap());
    }

    #[test]
    fn test_cbmc_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };

        let backend = CBMCBackend::new(config);

        let failure_output = "** 1 of 1 failed\nVERIFICATION FAILED\n";
        assert!(!backend.parse_result(failure_output).unwrap());
    }

    #[test]
    fn test_cbmc_parse_result_parsing_error() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);

        let error_output = "PARSING ERROR: syntax error\n";
        assert!(backend.parse_result(error_output).is_err());
    }

    #[test]
    fn test_cbmc_parse_result_inconclusive() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);

        let output = "some random output\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_cbmc_kind() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::CBMC);
    }

    #[test]
    fn test_cbmc_default_unwind_bound() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);
        assert_eq!(backend.unwind_bound, DEFAULT_UNWIND_BOUND);
    }

    #[test]
    fn test_cbmc_extract_cprover_call_nested() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);

        let line = "__CPROVER_assert(f(g(x)), \"nested\");";
        let result = backend.extract_cprover_call(line, "__CPROVER_assert");
        assert!(result.is_some());
        assert_eq!(result.unwrap(), "f(g(x)), \"nested\"");
    }

    #[test]
    fn test_cbmc_extract_cprover_call_missing() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);

        let line = "int x = 5;";
        let result = backend.extract_cprover_call(line, "__CPROVER_assert");
        assert!(result.is_none());
    }

    #[tokio::test]
    async fn test_cbmc_c_export_with_axioms() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("int x = 5;".to_string());
        state.goals.push(Goal {
            id: "assert_0".to_string(),
            target: Term::Const("x > 0".to_string()),
            hypotheses: vec![],
        });

        let c_source = backend.to_c_source(&state).unwrap();
        assert!(c_source.contains("int x = 5;"));
        assert!(c_source.contains("__CPROVER_assert(x > 0"));
    }

    #[tokio::test]
    async fn test_cbmc_suggest_tactics() {
        let config = ProverConfig {
            executable: PathBuf::from("cbmc"),
            timeout: 30,
            ..Default::default()
        };
        let backend = CBMCBackend::new(config);
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 1).await.unwrap();
        assert_eq!(tactics.len(), 1);
    }
}
