// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! SeaHorn Verification Framework Backend
//!
//! SeaHorn is an LLVM-based automated verification framework that uses
//! abstract interpretation and SMT solving over Constrained Horn Clauses (CHC).
//! It can verify safety properties of C programs and LLVM bitcode.
//!
//! Features:
//! - LLVM-based verification via abstract interpretation
//! - Constrained Horn Clauses (CHC) as intermediate representation
//! - Bounded model checking mode (`--bmc`)
//! - CHC solving mode (`--horn-solve`)
//! - Supports C source files and LLVM bitcode (.bc) as input
//! - Integrates with Z3/Spacer as the default CHC solver
//! - Configurable analysis tactics (widening, inline, etc.)

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Default BMC unwind bound for SeaHorn bounded model checking mode
const DEFAULT_BMC_BOUND: u32 = 256;

/// SeaHorn analysis mode selector
///
/// SeaHorn supports multiple front-end analysis strategies. The two primary
/// modes are bounded model checking and CHC-based horn solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SeaHornMode {
    /// Bounded model checking (`--bmc`): unrolls loops up to a bound
    BMC,

    /// CHC solving (`--horn-solve`): encodes program into Constrained Horn
    /// Clauses and solves using an SMT-based CHC solver (e.g., Spacer/Z3)
    #[default]
    HornSolve,
}

/// SeaHorn LLVM-based verification framework backend
///
/// Integrates the SeaHorn automated verification framework for verifying
/// safety properties of C programs and LLVM bitcode. SeaHorn encodes
/// verification conditions as Constrained Horn Clauses (CHC) and solves
/// them using abstract interpretation and SMT.
///
/// Typical invocation:
/// ```text
/// sea pf --bmc program.c          # bounded model checking
/// sea pf --horn-solve program.c   # CHC solving (default)
/// sea pf program.bc               # from LLVM bitcode
/// ```
pub struct SeaHornBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,

    /// Analysis mode: BMC or HornSolve
    mode: SeaHornMode,

    /// BMC unwind bound (only used in BMC mode)
    bmc_bound: u32,
}

impl SeaHornBackend {
    /// Create a new SeaHorn backend with the given configuration
    ///
    /// Defaults to HornSolve mode with a BMC bound of 256 (used when
    /// switching to BMC mode).
    pub fn new(config: ProverConfig) -> Self {
        SeaHornBackend {
            config,
            mode: SeaHornMode::default(),
            bmc_bound: DEFAULT_BMC_BOUND,
        }
    }

    /// Convert proof state to C source with assertion annotations
    ///
    /// Generates a valid C program from the ECHIDNA proof state. Goals
    /// become `sassert()` calls (SeaHorn's assertion macro), axioms become
    /// declarations or `__CPROVER_assume` / `assume()` calls, and
    /// definitions become comments.
    fn to_c_source(&self, state: &ProofState) -> Result<String> {
        let mut source = String::new();

        // Header with SeaHorn-compatible includes
        source.push_str("/* ECHIDNA SeaHorn Export */\n");
        source.push_str("#include \"seahorn/seahorn.h\"\n");
        source.push_str("#include <assert.h>\n\n");

        // SeaHorn uses sassert() macro for verification conditions
        source.push_str("extern void sassert(int);\n");
        source.push_str("extern int nd_int(void);\n\n");

        // Add axioms as declarations or raw C code
        for axiom in &state.context.axioms {
            if axiom.contains("assume")
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

        // Add definitions as comments
        for def in &state.context.definitions {
            source.push_str(&format!("/* definition: {} */\n", def));
        }

        // Wrap goals in a main function with sassert() calls
        source.push_str("\nint main() {\n");

        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            source.push_str(&format!("    sassert({}); /* {} */\n", target_str, goal.id));
        }

        source.push_str("    return 0;\n");
        source.push_str("}\n");

        Ok(source)
    }

    /// Parse SeaHorn output to determine verification result
    ///
    /// SeaHorn reports verification outcomes as follows:
    /// - `sat` or `BRUNCH_STAT Result TRUE` — the program is safe (all
    ///   assertions verified)
    /// - `unsat` or `BRUNCH_STAT Result FALSE` — the program is unsafe
    ///   (a counterexample exists)
    /// - Timeout or resource exhaustion — inconclusive
    fn parse_result(&self, output: &str) -> Result<bool> {
        // SeaHorn "sat" means the CHC system is satisfiable, i.e., safe
        if output.contains("BRUNCH_STAT Result TRUE")
            || output.contains("sat") && !output.contains("unsat") && !output.contains("unknown")
        {
            return Ok(true);
        }

        // "unsat" means the CHC system has no solution, i.e., unsafe
        if output.contains("BRUNCH_STAT Result FALSE") || output.contains("unsat") {
            return Ok(false);
        }

        // Check for timeout indicators
        if output.contains("BRUNCH_STAT Result TIMEOUT")
            || output.contains("timeout")
            || output.contains("UNKNOWN")
            || output.contains("unknown")
        {
            return Err(anyhow!(
                "SeaHorn inconclusive (timeout or unknown): {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        // Check for SeaHorn-specific error patterns
        if output.contains("ERROR") || output.contains("error:") {
            return Err(anyhow!(
                "SeaHorn error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        Err(anyhow!(
            "SeaHorn inconclusive or unexpected output: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse C source to extract assertion-based goals into proof state
    ///
    /// Recognises `sassert()`, `assert()`, `__CPROVER_assert()`, and
    /// `assume()` / `__CPROVER_assume()` directives.
    fn parse_c_source(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("/*") {
                continue;
            }

            // Detect sassert() — SeaHorn's assertion macro
            if trimmed.contains("sassert(") || trimmed.contains("sassert (") {
                if let Some(body) = self.extract_call_body(trimmed, "sassert") {
                    state.goals.push(Goal {
                        id: format!("seahorn_assert_{}", state.goals.len()),
                        target: Term::Const(body),
                        hypotheses: vec![],
                    });
                }
            }

            // Detect standard assert()
            if trimmed.contains("assert(")
                && !trimmed.contains("sassert")
                && !trimmed.contains("__CPROVER_assert")
            {
                if let Some(body) = self.extract_call_body(trimmed, "assert") {
                    state.goals.push(Goal {
                        id: format!("assert_{}", state.goals.len()),
                        target: Term::Const(body),
                        hypotheses: vec![],
                    });
                }
            }

            // Detect __CPROVER_assert (CBMC-compatible)
            if trimmed.contains("__CPROVER_assert(") || trimmed.contains("__CPROVER_assert (") {
                if let Some(body) = self.extract_call_body(trimmed, "__CPROVER_assert") {
                    // Split on first comma to extract the condition
                    let condition = if let Some(comma_pos) = body.find(',') {
                        body[..comma_pos].trim().to_string()
                    } else {
                        body
                    };

                    state.goals.push(Goal {
                        id: format!("cprover_assert_{}", state.goals.len()),
                        target: Term::Const(condition),
                        hypotheses: vec![],
                    });
                }
            }

            // Detect assume() and __CPROVER_assume() as axioms
            if trimmed.contains("assume(") && !trimmed.contains("__CPROVER_assume") {
                if let Some(body) = self.extract_call_body(trimmed, "assume") {
                    state.context.axioms.push(format!("assume({})", body));
                }
            }

            if trimmed.contains("__CPROVER_assume(") || trimmed.contains("__CPROVER_assume (") {
                if let Some(body) = self.extract_call_body(trimmed, "__CPROVER_assume") {
                    state
                        .context
                        .axioms
                        .push(format!("__CPROVER_assume({})", body));
                }
            }

            // Detect function declarations / variable declarations as context
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

    /// Extract the body of a function call from a source line
    ///
    /// Given a line containing e.g. `sassert(x > 0)`, returns `"x > 0"`.
    /// Handles nested parentheses correctly.
    fn extract_call_body(&self, line: &str, function_name: &str) -> Option<String> {
        let start_idx = line.find(function_name)?;
        let after_name = &line[start_idx + function_name.len()..];

        // Find opening paren (may have whitespace between name and paren)
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

    /// Build the `sea pf` command with appropriate flags
    ///
    /// Constructs the command-line invocation for SeaHorn's `pf` (proof)
    /// sub-command, including mode selection, BMC bound, and any extra
    /// arguments from the configuration.
    fn build_command(&self, input_path: &PathBuf) -> Command {
        let mut cmd = Command::new(&self.config.executable);

        // SeaHorn uses the `pf` sub-command for verification
        cmd.arg("pf");

        // Select analysis mode
        match self.mode {
            SeaHornMode::BMC => {
                cmd.arg("--bmc");
                cmd.arg(format!("--bound={}", self.bmc_bound));
            },
            SeaHornMode::HornSolve => {
                cmd.arg("--horn-solve");
            },
        }

        // Add any extra arguments from config
        for extra_arg in &self.config.args {
            cmd.arg(extra_arg);
        }

        // Input file (C source or LLVM bitcode)
        cmd.arg(input_path);

        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        cmd
    }
}

#[async_trait]
impl ProverBackend for SeaHornBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::SeaHorn
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run sea --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // SeaHorn may print version to stdout or stderr
        let version_text = if stdout.trim().is_empty() {
            stderr.trim().to_string()
        } else {
            stdout.trim().to_string()
        };

        Ok(version_text)
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");

        let mut state = match extension {
            "c" | "h" => {
                // Parse C source to extract assertions and assumptions
                let content = tokio::fs::read_to_string(&path)
                    .await
                    .context("Failed to read C source file for SeaHorn")?;
                self.parse_string(&content).await?
            },
            "bc" | "ll" => {
                // LLVM bitcode / IR — we cannot parse assertions directly,
                // so create a minimal proof state referencing the file
                let mut state = ProofState::default();
                state.metadata.insert(
                    "seahorn_input_file".to_string(),
                    serde_json::Value::String(path.display().to_string()),
                );
                state.metadata.insert(
                    "seahorn_input_type".to_string(),
                    serde_json::Value::String(extension.to_string()),
                );
                state
            },
            _ => {
                return Err(anyhow!(
                    "SeaHorn: unsupported file extension '.{}' (expected .c, .bc, or .ll)",
                    extension
                ));
            },
        };
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_c_source(content)?;
        state.metadata.insert(
            "seahorn_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // set_mode: switch between BMC and HornSolve modes
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "seahorn" && command == "set_mode" => {
                let mode_str = args.first().ok_or_else(|| {
                    anyhow!("set_mode requires an argument: 'bmc' or 'horn-solve'")
                })?;

                // Validate mode string
                match mode_str.as_str() {
                    "bmc" | "horn-solve" | "horn_solve" => {},
                    _ => {
                        return Ok(TacticResult::Error(format!(
                            "Unknown SeaHorn mode '{}' (expected 'bmc' or 'horn-solve')",
                            mode_str
                        )));
                    },
                }

                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "seahorn_mode".to_string(),
                    serde_json::Value::String(mode_str.clone()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // set_bmc_bound: configure the BMC unrolling bound
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "seahorn" && command == "set_bmc_bound" => {
                let bound_str = args
                    .first()
                    .ok_or_else(|| anyhow!("set_bmc_bound requires a numeric argument"))?;
                let _bound: u32 = bound_str
                    .parse()
                    .map_err(|_| anyhow!("Invalid BMC bound: {}", bound_str))?;

                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "seahorn_bmc_bound".to_string(),
                    serde_json::Value::String(bound_str.clone()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_assumption: add an assume() constraint
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "seahorn" && command == "add_assumption" => {
                let assumption_text = args.join(" ");
                let mut new_state = state.clone();
                new_state
                    .context
                    .axioms
                    .push(format!("assume({})", assumption_text));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_assertion: add a new sassert() goal to verify
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "seahorn" && command == "add_assertion" => {
                let assertion_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("seahorn_assert_{}", new_state.goals.len()),
                    target: Term::Const(assertion_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // inline: request function inlining (SeaHorn optimisation flag)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "seahorn" && command == "inline" => {
                let mut new_state = state.clone();
                let inline_depth = args
                    .first()
                    .and_then(|s| s.parse::<u32>().ok())
                    .unwrap_or(1);
                new_state.metadata.insert(
                    "seahorn_inline_depth".to_string(),
                    serde_json::Value::Number(serde_json::Number::from(inline_depth)),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for SeaHorn verification framework",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Determine input: either a referenced file or generated C source
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for SeaHorn")?;

        let input_path = if let Some(path) =
            state.metadata.get("source_path").and_then(|v| v.as_str())
        {
            PathBuf::from(path)
        } else if let Some(serde_json::Value::String(file_path)) =
            state.metadata.get("seahorn_input_file")
        {
            // Use the referenced input file directly (bitcode or C source)
            PathBuf::from(file_path)
        } else if let Some(src) = state
            .metadata
            .get("seahorn_source")
            .and_then(|v| v.as_str())
        {
            let tmp_file = tmp_dir.path().join("program.c");
            tokio::fs::write(&tmp_file, src)
                .await
                .context("Failed to write temporary C file for SeaHorn")?;
            tmp_file
        } else {
            // Generate C source from proof state
            let c_source = self.to_c_source(state)?;
            let tmp_file = tmp_dir.path().join("program.c");
            tokio::fs::write(&tmp_file, &c_source)
                .await
                .context("Failed to write temporary C file for SeaHorn")?;
            tmp_file
        };

        // Resolve analysis mode from metadata (tactic may have overridden it)
        let effective_mode = state
            .metadata
            .get("seahorn_mode")
            .and_then(|v| v.as_str())
            .map(|s| match s {
                "bmc" => SeaHornMode::BMC,
                _ => SeaHornMode::HornSolve,
            })
            .unwrap_or(self.mode);

        // Resolve BMC bound from metadata or use default
        let effective_bmc_bound = state
            .metadata
            .get("seahorn_bmc_bound")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(self.bmc_bound);

        // Build and run the SeaHorn command
        let mut cmd = Command::new(&self.config.executable);
        cmd.arg("pf");

        match effective_mode {
            SeaHornMode::BMC => {
                cmd.arg("--bmc");
                cmd.arg(format!("--bound={}", effective_bmc_bound));
            },
            SeaHornMode::HornSolve => {
                cmd.arg("--horn-solve");
            },
        }

        // Add inline depth if specified
        if let Some(serde_json::Value::Number(depth)) = state.metadata.get("seahorn_inline_depth") {
            if let Some(d) = depth.as_u64() {
                cmd.arg(format!("--inline={}", d));
            }
        }

        // Add extra arguments from config
        for extra_arg in &self.config.args {
            cmd.arg(extra_arg);
        }

        cmd.arg(&input_path);
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            cmd.output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "SeaHorn verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute SeaHorn (sea)")?;

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
                prover: "seahorn".to_string(),
                command: "set_mode".to_string(),
                args: vec!["horn-solve".to_string()],
            },
            Tactic::Custom {
                prover: "seahorn".to_string(),
                command: "set_mode".to_string(),
                args: vec!["bmc".to_string()],
            },
            Tactic::Custom {
                prover: "seahorn".to_string(),
                command: "set_bmc_bound".to_string(),
                args: vec!["256".to_string()],
            },
            Tactic::Custom {
                prover: "seahorn".to_string(),
                command: "add_assumption".to_string(),
                args: vec!["x >= 0".to_string()],
            },
            Tactic::Custom {
                prover: "seahorn".to_string(),
                command: "add_assertion".to_string(),
                args: vec!["y > 0".to_string()],
            },
            Tactic::Custom {
                prover: "seahorn".to_string(),
                command: "inline".to_string(),
                args: vec!["2".to_string()],
            },
        ];

        tactics.truncate(limit);
        Ok(tactics)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // SeaHorn is an automated verifier; no theorem library to search
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

    /// Helper to create a test backend with default configuration
    fn test_backend() -> SeaHornBackend {
        let config = ProverConfig {
            executable: PathBuf::from("sea"),
            timeout: 30,
            ..Default::default()
        };
        SeaHornBackend::new(config)
    }

    #[tokio::test]
    async fn test_seahorn_c_export() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "safety_0".to_string(),
            target: Term::Const("x > 0".to_string()),
            hypotheses: vec![],
        });

        let c_source = backend.to_c_source(&state).unwrap();

        assert!(c_source.contains("ECHIDNA SeaHorn Export"));
        assert!(c_source.contains("sassert(x > 0)"));
        assert!(c_source.contains("int main()"));
        assert!(c_source.contains("seahorn/seahorn.h"));
    }

    #[tokio::test]
    async fn test_seahorn_parse_sassert() {
        let backend = test_backend();

        let c_code = r#"
#include "seahorn/seahorn.h"
extern void sassert(int);

int main() {
    int x = nd_int();
    assume(x > 0);
    sassert(x >= 1);
    return 0;
}
"#;

        let state = backend.parse_string(c_code).await.unwrap();

        assert!(!state.goals.is_empty(), "Should have parsed sassert goals");
        assert_eq!(state.goals[0].id, "seahorn_assert_0");
    }

    #[tokio::test]
    async fn test_seahorn_parse_assume() {
        let backend = test_backend();

        let c_code = r#"
int main() {
    assume(x > 0);
    sassert(x >= 1);
    return 0;
}
"#;

        let state = backend.parse_string(c_code).await.unwrap();

        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed assume axioms"
        );
        assert!(state
            .context
            .axioms
            .iter()
            .any(|a| a.contains("assume(x > 0)")));
    }

    #[test]
    fn test_seahorn_parse_result_safe() {
        let backend = test_backend();

        let safe_output = "BRUNCH_STAT Result TRUE\nBRUNCH_STAT Time 1.23\n";
        assert!(backend.parse_result(safe_output).unwrap());
    }

    #[test]
    fn test_seahorn_parse_result_unsafe() {
        let backend = test_backend();

        let unsafe_output = "BRUNCH_STAT Result FALSE\nBRUNCH_STAT Time 0.45\n";
        assert!(!backend.parse_result(unsafe_output).unwrap());
    }

    #[test]
    fn test_seahorn_parse_result_timeout() {
        let backend = test_backend();

        let timeout_output = "BRUNCH_STAT Result TIMEOUT\n";
        assert!(backend.parse_result(timeout_output).is_err());
    }

    #[test]
    fn test_seahorn_parse_result_sat() {
        let backend = test_backend();

        // Plain "sat" output (CHC solver result)
        let sat_output = "sat\n";
        assert!(backend.parse_result(sat_output).unwrap());
    }

    #[test]
    fn test_seahorn_parse_result_unsat() {
        let backend = test_backend();

        let unsat_output = "unsat\n";
        assert!(!backend.parse_result(unsat_output).unwrap());
    }

    #[tokio::test]
    async fn test_seahorn_apply_set_mode() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "seahorn".to_string(),
            command: "set_mode".to_string(),
            args: vec!["bmc".to_string()],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();
        match result {
            TacticResult::Success(new_state) => {
                assert_eq!(
                    new_state
                        .metadata
                        .get("seahorn_mode")
                        .unwrap()
                        .as_str()
                        .unwrap(),
                    "bmc"
                );
            },
            other => panic!("Expected TacticResult::Success, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_seahorn_apply_set_bmc_bound() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "seahorn".to_string(),
            command: "set_bmc_bound".to_string(),
            args: vec!["512".to_string()],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();
        match result {
            TacticResult::Success(new_state) => {
                assert_eq!(
                    new_state
                        .metadata
                        .get("seahorn_bmc_bound")
                        .unwrap()
                        .as_str()
                        .unwrap(),
                    "512"
                );
            },
            other => panic!("Expected TacticResult::Success, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_seahorn_apply_add_assertion() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "seahorn".to_string(),
            command: "add_assertion".to_string(),
            args: vec!["n".to_string(), ">=".to_string(), "0".to_string()],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();
        match result {
            TacticResult::Success(new_state) => {
                assert_eq!(new_state.goals.len(), 1);
                assert_eq!(format!("{}", new_state.goals[0].target), "n >= 0");
            },
            other => panic!("Expected TacticResult::Success, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_seahorn_suggest_tactics() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 3).await.unwrap();
        assert_eq!(tactics.len(), 3);
    }

    #[test]
    fn test_seahorn_extract_call_body() {
        let backend = test_backend();

        assert_eq!(
            backend.extract_call_body("sassert(x > 0);", "sassert"),
            Some("x > 0".to_string())
        );
        assert_eq!(
            backend.extract_call_body("sassert (foo(bar(x)));", "sassert"),
            Some("foo(bar(x))".to_string())
        );
        assert_eq!(
            backend.extract_call_body("assume(n >= 0);", "assume"),
            Some("n >= 0".to_string())
        );
    }

    #[test]
    fn test_seahorn_default_mode() {
        let backend = test_backend();
        assert_eq!(backend.mode, SeaHornMode::HornSolve);
        assert_eq!(backend.bmc_bound, DEFAULT_BMC_BOUND);
    }
}
