// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Frama-C WP (Weakest Precondition) Program Verifier Backend
//!
//! Frama-C is an extensible C program analysis framework. Its WP plugin
//! generates proof obligations from ACSL (ANSI/ISO C Specification Language)
//! annotations and discharges them via SMT solvers (Alt-Ergo by default).
//!
//! Input format: ACSL-annotated C source files with function contracts
//! (`/*@ requires ...; ensures ...; */`), loop invariants
//! (`/*@ loop invariant ...; loop variant ...; */`), and assertions
//! (`/*@ assert ...; */`).
//!
//! Output: Per-goal proof status — "Proved" (valid), "Unknown" (cannot prove),
//! or "Timeout" (solver exceeded time limit).
//!
//! Frama-C is ECHIDNA's deductive C verification backend in the Tier 9
//! program verifiers category, complementing CBMC's bounded model checking
//! with unbounded, annotation-driven formal verification.

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Default WP prover used by Frama-C (Alt-Ergo is the standard default)
const DEFAULT_WP_PROVER: &str = "alt-ergo";

/// Default WP timeout in seconds for individual proof obligations
const DEFAULT_WP_TIMEOUT: u32 = 30;

/// Frama-C WP deductive verification backend
///
/// Integrates the Frama-C platform with its WP (Weakest Precondition) plugin
/// for verifying ACSL-annotated C programs. Proof obligations are generated
/// from function contracts, loop invariants, and assertions, then discharged
/// by an SMT solver (Alt-Ergo by default, or Z3/CVC4/CVC5).
pub struct FramaCBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,

    /// WP prover to use for discharging proof obligations (e.g. "alt-ergo", "z3")
    wp_prover: String,

    /// Per-obligation timeout in seconds (passed to frama-c -wp-timeout)
    wp_timeout: u32,
}

impl FramaCBackend {
    /// Create a new Frama-C backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        FramaCBackend {
            config,
            wp_prover: DEFAULT_WP_PROVER.to_string(),
            wp_timeout: DEFAULT_WP_TIMEOUT,
        }
    }

    /// Parse ACSL-annotated C source into a ProofState
    ///
    /// Extracts:
    /// - Function contracts (`requires`, `ensures`, `assigns`) as goals
    /// - Loop invariants (`loop invariant`, `loop variant`) as goals
    /// - Inline assertions (`assert`) as goals
    /// - Function declarations/definitions as context axioms
    ///
    /// Each ACSL annotation block is identified by the `/*@ ... */` or
    /// `//@ ...` delimiters per the ACSL specification.
    fn parse_acsl_source(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        let mut in_acsl_block = false;
        let mut acsl_buffer = String::new();
        let mut current_function: Option<String> = None;
        let mut goal_counter: usize = 0;

        for line in content.lines() {
            let trimmed = line.trim();

            // Track current function context for goal naming
            if !in_acsl_block {
                if let Some(func_name) = Self::extract_function_name(trimmed) {
                    current_function = Some(func_name);
                }
            }

            // Detect single-line ACSL annotations: //@ ...
            if let Some(rest) = trimmed.strip_prefix("//@") {
                let acsl_text = rest.trim();
                self.process_acsl_clause(
                    acsl_text,
                    &current_function,
                    &mut state,
                    &mut goal_counter,
                );
                continue;
            }

            // Detect start of multi-line ACSL block: /*@ ... */
            if trimmed.contains("/*@") {
                // Check if it's a single-line block: /*@ ... */
                if let Some(end_idx) = trimmed.find("*/") {
                    let start_idx = trimmed.find("/*@").unwrap();
                    let acsl_text = &trimmed[start_idx + 3..end_idx];
                    for clause in acsl_text.split(';') {
                        let clause = clause.trim();
                        if !clause.is_empty() {
                            self.process_acsl_clause(
                                clause,
                                &current_function,
                                &mut state,
                                &mut goal_counter,
                            );
                        }
                    }
                } else {
                    // Start of multi-line block
                    in_acsl_block = true;
                    let start_idx = trimmed.find("/*@").unwrap();
                    acsl_buffer = trimmed[start_idx + 3..].to_string();
                }
                continue;
            }

            // Inside a multi-line ACSL block
            if in_acsl_block {
                if trimmed.contains("*/") {
                    // End of multi-line block
                    let end_idx = trimmed.find("*/").unwrap();
                    acsl_buffer.push(' ');
                    acsl_buffer.push_str(&trimmed[..end_idx]);
                    in_acsl_block = false;

                    // Process all clauses in the accumulated block
                    for clause in acsl_buffer.split(';') {
                        let clause = clause.trim();
                        if !clause.is_empty() {
                            self.process_acsl_clause(
                                clause,
                                &current_function,
                                &mut state,
                                &mut goal_counter,
                            );
                        }
                    }
                    acsl_buffer.clear();
                } else {
                    acsl_buffer.push(' ');
                    acsl_buffer.push_str(trimmed);
                }
                continue;
            }

            // Track C declarations as axioms for context
            if trimmed.starts_with("int ")
                || trimmed.starts_with("void ")
                || trimmed.starts_with("unsigned ")
                || trimmed.starts_with("char ")
                || trimmed.starts_with("long ")
                || trimmed.starts_with("double ")
                || trimmed.starts_with("float ")
                || trimmed.starts_with("struct ")
                || trimmed.starts_with("#include")
                || trimmed.starts_with("#define")
            {
                state.context.axioms.push(trimmed.to_string());
            }
        }

        // Store the WP prover and timeout in metadata for roundtripping
        state.metadata.insert(
            "framac_wp_prover".to_string(),
            serde_json::Value::String(self.wp_prover.clone()),
        );
        state.metadata.insert(
            "framac_wp_timeout".to_string(),
            serde_json::Value::Number(serde_json::Number::from(self.wp_timeout)),
        );

        Ok(state)
    }

    /// Process a single ACSL clause and add it to the proof state
    ///
    /// Recognises: requires, ensures, assigns, loop invariant,
    /// loop variant, assert, assumes, decreases.
    fn process_acsl_clause(
        &self,
        clause: &str,
        current_function: &Option<String>,
        state: &mut ProofState,
        goal_counter: &mut usize,
    ) {
        let clause = clause.trim();
        if clause.is_empty() {
            return;
        }

        let func_prefix = current_function.as_deref().unwrap_or("global");

        // requires: precondition — becomes a goal
        if let Some(body) = clause.strip_prefix("requires") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__requires_{}", func_prefix, goal_counter),
                target: Term::Const(format!("requires {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
            return;
        }

        // ensures: postcondition — becomes a goal
        if let Some(body) = clause.strip_prefix("ensures") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__ensures_{}", func_prefix, goal_counter),
                target: Term::Const(format!("ensures {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
            return;
        }

        // loop invariant — becomes a goal
        if let Some(body) = clause.strip_prefix("loop invariant") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__loop_invariant_{}", func_prefix, goal_counter),
                target: Term::Const(format!("loop invariant {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
            return;
        }

        // loop variant — becomes a goal (termination measure)
        if let Some(body) = clause.strip_prefix("loop variant") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__loop_variant_{}", func_prefix, goal_counter),
                target: Term::Const(format!("loop variant {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
            return;
        }

        // assert — inline assertion becomes a goal
        if let Some(body) = clause.strip_prefix("assert") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__assert_{}", func_prefix, goal_counter),
                target: Term::Const(format!("assert {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
            return;
        }

        // assigns — frame condition, stored as context
        if let Some(body) = clause.strip_prefix("assigns") {
            let body = body.trim();
            state.context.axioms.push(format!("assigns {}", body));
            return;
        }

        // assumes — hypothesis, stored as context axiom
        if let Some(body) = clause.strip_prefix("assumes") {
            let body = body.trim();
            state.context.axioms.push(format!("assumes {}", body));
            return;
        }

        // decreases — termination measure, stored as goal
        if let Some(body) = clause.strip_prefix("decreases") {
            let body = body.trim();
            state.goals.push(Goal {
                id: format!("{}__decreases_{}", func_prefix, goal_counter),
                target: Term::Const(format!("decreases {}", body)),
                hypotheses: vec![],
            });
            *goal_counter += 1;
        }
    }

    /// Extract a function name from a C function definition/declaration line
    ///
    /// Handles patterns like `int foo(...)`, `void bar(int x)`, etc.
    fn extract_function_name(line: &str) -> Option<String> {
        // Match "type name(" pattern — simple heuristic for C function signatures
        let line = line.trim();

        // Skip lines that are clearly not function declarations
        if line.starts_with('#')
            || line.starts_with("//")
            || line.starts_with("/*")
            || line.starts_with("}")
            || line.starts_with("{")
        {
            return None;
        }

        // Look for "word word(" or "word* word(" patterns
        if let Some(paren_idx) = line.find('(') {
            let before_paren = line[..paren_idx].trim();
            let parts: Vec<&str> = before_paren.split_whitespace().collect();
            if parts.len() >= 2 {
                // Last token before '(' is likely the function name
                let candidate = parts.last()?;
                // Strip leading * for pointer-returning functions
                let name = candidate.trim_start_matches('*');
                if !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    return Some(name.to_string());
                }
            }
        }

        None
    }

    /// Generate ACSL-annotated C source from a ProofState
    ///
    /// Reconstructs function contracts and assertions from the proof state
    /// goals. Context axioms that look like C declarations are emitted
    /// directly; ACSL-specific axioms (assigns, assumes) are wrapped in
    /// annotation blocks.
    fn to_acsl_source(&self, state: &ProofState) -> Result<String> {
        let mut source = String::new();

        // File header
        source.push_str("/* ECHIDNA Frama-C WP Export */\n");
        source.push_str("/* Verify with: frama-c -wp -wp-prover ");
        source.push_str(&self.wp_prover);
        source.push_str(" <file>.c */\n\n");

        // Emit #include and #define axioms first
        for axiom in &state.context.axioms {
            if axiom.starts_with("#include") || axiom.starts_with("#define") {
                source.push_str(axiom);
                source.push('\n');
            }
        }
        source.push('\n');

        // Collect ACSL contract goals and inline assertion goals
        let mut contract_goals: Vec<&Goal> = Vec::new();
        let mut assert_goals: Vec<&Goal> = Vec::new();

        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            if target_str.starts_with("requires ")
                || target_str.starts_with("ensures ")
                || target_str.starts_with("loop invariant ")
                || target_str.starts_with("loop variant ")
                || target_str.starts_with("decreases ")
            {
                contract_goals.push(goal);
            } else if target_str.starts_with("assert ") {
                assert_goals.push(goal);
            } else {
                // Treat unknown goals as assertions
                assert_goals.push(goal);
            }
        }

        // Emit contract goals as a function contract block
        if !contract_goals.is_empty() {
            source.push_str("/*@\n");
            for goal in &contract_goals {
                let target_str = format!("{}", goal.target);
                source.push_str(&format!("  {};\n", target_str));
            }

            // Emit ACSL-specific axioms (assigns, assumes)
            for axiom in &state.context.axioms {
                if axiom.starts_with("assigns ") || axiom.starts_with("assumes ") {
                    source.push_str(&format!("  {};\n", axiom));
                }
            }

            source.push_str("*/\n");
        }

        // Emit C declarations from context (non-preprocessor, non-ACSL)
        for axiom in &state.context.axioms {
            if !axiom.starts_with("#include")
                && !axiom.starts_with("#define")
                && !axiom.starts_with("assigns ")
                && !axiom.starts_with("assumes ")
            {
                source.push_str(axiom);
                source.push('\n');
            }
        }

        // Emit C definitions from context
        for def in &state.context.definitions {
            source.push_str(&format!("/* definition: {} */\n", def));
        }

        // Generate a main-like function with inline assertions
        if !assert_goals.is_empty() {
            source.push_str("\nvoid echidna_assertions(void) {\n");
            for goal in &assert_goals {
                let target_str = format!("{}", goal.target);
                if let Some(body) = target_str.strip_prefix("assert ") {
                    source.push_str(&format!("    /*@ assert {}; */\n", body));
                } else {
                    source.push_str(&format!("    /*@ assert {}; */\n", target_str));
                }
            }
            source.push_str("}\n");
        }

        Ok(source)
    }

    /// Parse Frama-C WP output to determine verification result
    ///
    /// Frama-C WP reports per-goal results. The overall verification succeeds
    /// when all goals are "Proved". Any "Unknown", "Timeout", or "Failed"
    /// result means the overall verification did not fully succeed.
    ///
    /// Output patterns:
    /// - `[wp] Proved goals:    N / N` — all proved
    /// - `[wp] Qed:             N`     — goals discharged by Qed
    /// - `[wp] Alt-Ergo:        N`     — goals discharged by Alt-Ergo
    /// - Goal status lines contain "Valid", "Unknown", "Timeout"
    fn parse_wp_result(output: &str) -> Result<bool> {
        let mut total_goals: Option<u32> = None;
        let mut proved_goals: Option<u32> = None;
        let mut has_unknown = false;
        let mut has_timeout = false;
        let mut has_failed = false;

        for line in output.lines() {
            let line = line.trim();

            // Parse "[wp] Proved goals:    N / M"
            if line.contains("Proved goals:") || line.contains("proved goals:") {
                if let Some(fraction) = Self::extract_fraction(line) {
                    proved_goals = Some(fraction.0);
                    total_goals = Some(fraction.1);
                }
            }

            // Detect failure indicators
            if line.contains("Unknown") && !line.contains("Proved") {
                has_unknown = true;
            }
            if line.contains("Timeout") {
                has_timeout = true;
            }
            if line.contains("Failed") || line.contains("FAILED") {
                has_failed = true;
            }
        }

        // If we found a proved goals fraction, check if all are proved
        if let (Some(proved), Some(total)) = (proved_goals, total_goals) {
            if total == 0 {
                // No goals to prove — vacuously true
                return Ok(true);
            }
            return Ok(proved == total);
        }

        // If no fraction found but we have explicit failure indicators
        if has_failed || has_unknown || has_timeout {
            return Ok(false);
        }

        // Look for simple "Valid" / "Proved" with no failure markers
        let has_valid = output.contains("Valid") || output.contains("Proved");
        if has_valid && !has_unknown && !has_timeout && !has_failed {
            return Ok(true);
        }

        Err(anyhow!(
            "Frama-C WP output inconclusive: {}",
            output.lines().take(15).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Extract a "N / M" fraction from a Frama-C output line
    ///
    /// Returns Some((proved, total)) if found.
    fn extract_fraction(line: &str) -> Option<(u32, u32)> {
        // Find "N / M" pattern
        let parts: Vec<&str> = line.split('/').collect();
        if parts.len() == 2 {
            // Get the last number from the left part and the first number from the right
            let left_num = parts[0].split_whitespace().last()?.parse::<u32>().ok()?;
            let right_num = parts[1].split_whitespace().next()?.parse::<u32>().ok()?;
            Some((left_num, right_num))
        } else {
            None
        }
    }
}

#[async_trait]
impl ProverBackend for FramaCBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::FramaC
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run frama-c -version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| {
                l.contains("Frama-C")
                    || l.contains("frama-c")
                    || l.contains("Version")
                    || l.contains("version")
            })
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .with_context(|| format!("Failed to read ACSL-annotated C file: {:?}", path))?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_acsl_source(content)?;
        state.metadata.insert(
            "framac_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // set_wp_prover: change the underlying WP SMT prover
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "set_wp_prover" => {
                let prover_name = args.first().ok_or_else(|| {
                    anyhow!("set_wp_prover requires a prover name argument (e.g. alt-ergo, z3)")
                })?;

                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "framac_wp_prover".to_string(),
                    serde_json::Value::String(prover_name.clone()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // set_wp_timeout: adjust per-obligation SMT timeout
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "set_wp_timeout" => {
                let timeout_str = args.first().ok_or_else(|| {
                    anyhow!("set_wp_timeout requires a numeric argument (seconds)")
                })?;
                let _timeout: u32 = timeout_str
                    .parse()
                    .map_err(|_| anyhow!("Invalid timeout value: {}", timeout_str))?;

                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "framac_wp_timeout".to_string(),
                    serde_json::Value::String(timeout_str.clone()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_requires: add a precondition
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "add_requires" => {
                let predicate = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("requires_{}", new_state.goals.len()),
                    target: Term::Const(format!("requires {}", predicate)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_ensures: add a postcondition
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "add_ensures" => {
                let predicate = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("ensures_{}", new_state.goals.len()),
                    target: Term::Const(format!("ensures {}", predicate)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_loop_invariant: add a loop invariant
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "add_loop_invariant" => {
                let predicate = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("loop_invariant_{}", new_state.goals.len()),
                    target: Term::Const(format!("loop invariant {}", predicate)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // add_assert: add an inline ACSL assertion
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "framac" && command == "add_assert" => {
                let predicate = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("assert_{}", new_state.goals.len()),
                    target: Term::Const(format!("assert {}", predicate)),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for Frama-C WP verifier",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Read WP prover from metadata (may have been changed via tactic)
        let wp_prover = state
            .metadata
            .get("framac_wp_prover")
            .and_then(|v| v.as_str())
            .unwrap_or(&self.wp_prover);

        // Read WP timeout from metadata
        let wp_timeout = state
            .metadata
            .get("framac_wp_timeout")
            .and_then(|v| v.as_str().or_else(|| v.as_u64().map(|_| "")))
            .and_then(|s| s.parse::<u32>().ok())
            .or_else(|| {
                state
                    .metadata
                    .get("framac_wp_timeout")
                    .and_then(|v| v.as_u64())
                    .map(|n| n as u32)
            })
            .unwrap_or(self.wp_timeout);

        // Prefer the original ACSL-annotated .c file; `to_acsl_source` is
        // lossy for anything beyond trivial function stubs.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 10),
                Command::new(&self.config.executable)
                    .arg("-wp")
                    .arg("-wp-prover")
                    .arg(wp_prover)
                    .arg("-wp-timeout")
                    .arg(format!("{}", wp_timeout))
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| {
                anyhow!(
                    "Frama-C WP verification timed out after {} seconds",
                    self.config.timeout
                )
            })?
            .context("Failed to execute Frama-C")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return Self::parse_wp_result(&combined);
        }

        if state.goals.is_empty()
            && state
                .metadata
                .get("framac_source")
                .and_then(|v| v.as_str())
                .is_none()
        {
            return Ok(true);
        }

        let acsl_source = if let Some(src) = state
            .metadata
            .get("framac_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_acsl_source(state)?
        };

        // Write ACSL-annotated C source to a temporary file
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for Frama-C")?;
        let tmp_file = tmp_dir.path().join("program.c");
        tokio::fs::write(&tmp_file, &acsl_source)
            .await
            .context("Failed to write temporary ACSL-annotated C file")?;

        // Run: frama-c -wp -wp-prover <prover> -wp-timeout <timeout> <file>
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            Command::new(&self.config.executable)
                .arg("-wp")
                .arg("-wp-prover")
                .arg(wp_prover)
                .arg("-wp-timeout")
                .arg(format!("{}", wp_timeout))
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "Frama-C WP verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute Frama-C")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);

        Self::parse_wp_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_acsl_source(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "add_requires".to_string(),
                args: vec!["x >= 0".to_string()],
            },
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "add_ensures".to_string(),
                args: vec!["\\result >= 0".to_string()],
            },
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "add_loop_invariant".to_string(),
                args: vec!["0 <= i <= n".to_string()],
            },
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "add_assert".to_string(),
                args: vec!["x > 0".to_string()],
            },
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "set_wp_prover".to_string(),
                args: vec!["z3".to_string()],
            },
            Tactic::Custom {
                prover: "framac".to_string(),
                command: "set_wp_timeout".to_string(),
                args: vec!["60".to_string()],
            },
        ];

        tactics.truncate(limit);
        Ok(tactics)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Frama-C WP does not have a theorem library in the traditional sense
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

    /// Helper: create a FramaCBackend with default test configuration
    fn test_backend() -> FramaCBackend {
        let config = ProverConfig {
            executable: PathBuf::from("frama-c"),
            timeout: 30,
            ..Default::default()
        };
        FramaCBackend::new(config)
    }

    #[tokio::test]
    async fn test_parse_acsl_function_contract() {
        let backend = test_backend();

        let acsl_source = r#"
/*@ requires x >= 0;
    ensures \result >= 0;
    assigns \nothing;
*/
int abs(int x) {
    if (x < 0) return -x;
    return x;
}
"#;

        let state = backend.parse_string(acsl_source).await.unwrap();

        // Should have parsed requires and ensures as goals
        assert!(
            state.goals.len() >= 2,
            "Expected at least 2 goals (requires + ensures), got {}",
            state.goals.len()
        );

        // Check that goals contain the expected ACSL clauses
        let goal_texts: Vec<String> = state
            .goals
            .iter()
            .map(|g| format!("{}", g.target))
            .collect();

        assert!(
            goal_texts
                .iter()
                .any(|t| t.contains("requires") && t.contains("x >= 0")),
            "Missing requires goal in {:?}",
            goal_texts
        );
        assert!(
            goal_texts
                .iter()
                .any(|t| t.contains("ensures") && t.contains("\\result >= 0")),
            "Missing ensures goal in {:?}",
            goal_texts
        );

        // assigns should be in context axioms, not goals
        assert!(
            state.context.axioms.iter().any(|a| a.contains("assigns")),
            "assigns clause should be stored as context axiom"
        );
    }

    #[tokio::test]
    async fn test_parse_acsl_loop_invariant() {
        let backend = test_backend();

        let acsl_source = r#"
int sum(int n) {
    int s = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant s == i * (i - 1) / 2;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        s += i;
    }
    return s;
}
"#;

        let state = backend.parse_string(acsl_source).await.unwrap();

        assert!(
            state.goals.len() >= 3,
            "Expected at least 3 goals (2 loop invariants + 1 loop variant), got {}",
            state.goals.len()
        );

        let goal_texts: Vec<String> = state
            .goals
            .iter()
            .map(|g| format!("{}", g.target))
            .collect();

        assert!(
            goal_texts
                .iter()
                .any(|t| t.contains("loop invariant") && t.contains("0 <= i <= n")),
            "Missing loop invariant goal in {:?}",
            goal_texts
        );
        assert!(
            goal_texts
                .iter()
                .any(|t| t.contains("loop variant") && t.contains("n - i")),
            "Missing loop variant goal in {:?}",
            goal_texts
        );
    }

    #[test]
    fn test_export_acsl_format() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "abs__requires_0".to_string(),
            target: Term::Const("requires x >= 0".to_string()),
            hypotheses: vec![],
        });
        state.goals.push(Goal {
            id: "abs__ensures_1".to_string(),
            target: Term::Const("ensures \\result >= 0".to_string()),
            hypotheses: vec![],
        });
        state.context.axioms.push("assigns \\nothing".to_string());

        let source = backend.to_acsl_source(&state).unwrap();

        assert!(
            source.contains("ECHIDNA Frama-C WP Export"),
            "Missing export header"
        );
        assert!(
            source.contains("requires x >= 0"),
            "Missing requires clause in export"
        );
        assert!(
            source.contains("ensures \\result >= 0"),
            "Missing ensures clause in export"
        );
        assert!(
            source.contains("assigns \\nothing"),
            "Missing assigns clause in export"
        );
        assert!(
            source.contains("/*@"),
            "Missing ACSL annotation block delimiter"
        );
    }

    #[test]
    fn test_parse_wp_result_all_proved() {
        let output = r#"
[kernel] Parsing program.c (with preprocessing)
[wp] Running WP plugin...
[wp] 3 goals scheduled
[wp] Proved goals:    3 / 3
  Qed:             1
  Alt-Ergo:        2
"#;

        assert!(
            FramaCBackend::parse_wp_result(output).unwrap(),
            "All goals proved should return true"
        );
    }

    #[test]
    fn test_parse_wp_result_partial_proof() {
        let output = r#"
[kernel] Parsing program.c (with preprocessing)
[wp] Running WP plugin...
[wp] 3 goals scheduled
[wp] Proved goals:    2 / 3
  Qed:             1
  Alt-Ergo:        1 (1 Unknown)
"#;

        assert!(
            !FramaCBackend::parse_wp_result(output).unwrap(),
            "Partial proof (2/3) should return false"
        );
    }

    #[test]
    fn test_parse_wp_result_timeout() {
        let output = r#"
[wp] Proved goals:    1 / 2
  Qed:             1
  Alt-Ergo:        0 (1 Timeout)
"#;

        assert!(
            !FramaCBackend::parse_wp_result(output).unwrap(),
            "Timeout should return false"
        );
    }

    #[test]
    fn test_extract_function_name() {
        assert_eq!(
            FramaCBackend::extract_function_name("int abs(int x) {"),
            Some("abs".to_string())
        );
        assert_eq!(
            FramaCBackend::extract_function_name("void process(void) {"),
            Some("process".to_string())
        );
        assert_eq!(
            FramaCBackend::extract_function_name("unsigned long factorial(int n)"),
            Some("factorial".to_string())
        );
        assert_eq!(
            FramaCBackend::extract_function_name("#include <stdio.h>"),
            None
        );
        assert_eq!(FramaCBackend::extract_function_name("// comment"), None);
    }

    #[tokio::test]
    async fn test_parse_single_line_acsl() {
        let backend = test_backend();

        let acsl_source = r#"
//@ requires n > 0;
//@ ensures \result > 0;
int positive(int n) {
    return n;
}
"#;

        let state = backend.parse_string(acsl_source).await.unwrap();

        assert_eq!(
            state.goals.len(),
            2,
            "Expected 2 goals from single-line ACSL annotations"
        );
    }

    #[test]
    fn test_extract_fraction() {
        assert_eq!(
            FramaCBackend::extract_fraction("[wp] Proved goals:    3 / 3"),
            Some((3, 3))
        );
        assert_eq!(
            FramaCBackend::extract_fraction("[wp] Proved goals:    0 / 5"),
            Some((0, 5))
        );
        assert_eq!(FramaCBackend::extract_fraction("no fraction here"), None);
    }
}
