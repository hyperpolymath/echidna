// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! KeY Deductive Java Verification Backend
//!
//! KeY is a deductive verification platform for sequential Java programs.
//! It uses Java Dynamic Logic (JavaDL) — a first-order dynamic logic for
//! reasoning about Java programs — and supports both automatic and interactive
//! proof strategies. Specifications are written in JML (Java Modeling Language)
//! annotations embedded in Java source files.
//!
//! Input formats:
//!   - `.key` files — KeY proof problem files (JavaDL sequents, taclet rules)
//!   - `.java` files — Java source with JML annotations (`//@ requires`, `//@ ensures`,
//!     `/*@ invariant */`, `/*@ loop_invariant */`, etc.)
//!
//! Logic: Java Dynamic Logic (JavaDL), a many-sorted first-order dynamic logic
//! with modalities `\<p\>phi` (diamond, total correctness) and `[p]phi`
//! (box, partial correctness) for Java program fragments `p`.
//!
//! Proof strategies:
//!   - Automatic: `auto` — runs the KeY auto strategy (symbolic execution + decision procedures)
//!   - Interactive: `apply_rule`, `apply_macro`, `set_strategy`, `prune` — fine-grained control
//!
//! Output parsing:
//!   - "Proof closed" or "CLOSED" → all goals discharged (success)
//!   - "open goals" or "OPEN GOAL" → incomplete proof (remaining obligations)
//!   - "ERROR" or "Exception" → verification error
//!
//! KeY is ECHIDNA's deductive Java verification backend in the Tier 9
//! program verifiers category, complementing Frama-C (C/ACSL) and Viper
//! (permission-based) with Java/JML-focused deductive verification.

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Default KeY proof strategy (automatic symbolic execution + decision procedures)
const DEFAULT_STRATEGY: &str = "auto";

/// Maximum number of automatic proof steps before giving up
const DEFAULT_MAX_STEPS: u32 = 10_000;

/// KeY deductive verification backend for Java/JML
///
/// Integrates the KeY platform for verifying JML-annotated Java programs using
/// Java Dynamic Logic (JavaDL). KeY supports both fully automatic proof search
/// (symbolic execution + built-in decision procedures) and interactive proof
/// construction via rule application, macros, and strategy configuration.
///
/// The backend can process both `.key` proof problem files (containing raw JavaDL
/// sequents and taclet definitions) and `.java` source files with embedded JML
/// annotations (function contracts, class invariants, loop invariants).
pub struct KeyBackend {
    /// Backend configuration (executable path, timeout, library paths, etc.)
    config: ProverConfig,

    /// Proof strategy to use ("auto", "javaDL", "simplification", etc.)
    strategy: String,

    /// Maximum number of automatic proof steps before the prover gives up
    max_steps: u32,
}

impl KeyBackend {
    /// Create a new KeY backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        KeyBackend {
            config,
            strategy: DEFAULT_STRATEGY.to_string(),
            max_steps: DEFAULT_MAX_STEPS,
        }
    }

    /// Convert an ECHIDNA proof state into a KeY-compatible input string.
    ///
    /// Generates a `.key` problem file containing JavaDL sequents derived from
    /// the proof state's axioms (as antecedent assumptions) and goals (as
    /// succedent proof obligations).
    fn to_key_format(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        // KeY problem file header
        output.push_str("\\profile \"Java Profile\";\n\n");

        // Emit axioms as JavaDL assumptions in the antecedent
        if !state.context.axioms.is_empty() {
            output.push_str("\\functions {\n");
            for (i, axiom) in state.context.axioms.iter().enumerate() {
                output.push_str(&format!("  // axiom {}: {}\n", i, axiom));
            }
            output.push_str("}\n\n");
        }

        // Emit goals as proof obligations
        output.push_str("\\problem {\n");
        if let Some(goal) = state.goals.first() {
            // Wrap goal target in a JavaDL formula
            output.push_str(&format!("  {}\n", goal.target));

            // Add hypotheses as antecedent context
            if !goal.hypotheses.is_empty() {
                output.push_str("  // hypotheses:\n");
                for hyp in &goal.hypotheses {
                    output.push_str(&format!("  // {}: {}\n", hyp.name, hyp.ty));
                }
            }
        } else {
            output.push_str("  true\n");
        }
        output.push_str("}\n");

        // Append strategy settings
        output.push_str("\n\\settings {\n");
        output.push_str(&format!(
            "  \"[Strategy]ActiveStrategy\" : \"{}\"\n",
            self.strategy
        ));
        output.push_str(&format!(
            "  \"[Strategy]MaximumNumberOfAutomaticApplications\" : \"{}\"\n",
            self.max_steps
        ));
        output.push_str("}\n");

        Ok(output)
    }

    /// Parse KeY output to determine proof outcome.
    ///
    /// KeY reports proof status in its console output:
    /// - "Proof closed" / "CLOSED" → all goals discharged, proof complete
    /// - "open goals" / "OPEN GOAL" → proof incomplete, remaining obligations
    /// - "ERROR" / "Exception" → verification failure or internal error
    fn parse_result(&self, output: &str) -> Result<bool> {
        let lower = output.to_lowercase();

        if lower.contains("proof closed") || lower.contains("closed") {
            Ok(true)
        } else if lower.contains("open goal") || lower.contains("open goals") {
            Ok(false)
        } else if lower.contains("error") || lower.contains("exception") {
            Err(anyhow!(
                "KeY verification error: {}",
                Self::extract_error(output)
            ))
        } else {
            // If no recognisable status, treat as inconclusive
            Err(anyhow!(
                "KeY output inconclusive — could not determine proof status"
            ))
        }
    }

    /// Extract the first error or exception line from KeY output for diagnostics
    fn extract_error(output: &str) -> String {
        for line in output.lines() {
            let trimmed = line.trim();
            if trimmed.contains("ERROR") || trimmed.contains("Exception") {
                return trimmed.to_string();
            }
        }
        "unknown error".to_string()
    }

    /// Format a Tactic enum variant as a human-readable string for KeY command dispatch
    fn tactic_to_string(tactic: &Tactic) -> String {
        match tactic {
            Tactic::Apply(name) => format!("apply {}", name),
            Tactic::Intro(name) => format!("intro {}", name.as_deref().unwrap_or("_")),
            Tactic::Cases(term) => format!("cases {}", term),
            Tactic::Induction(term) => format!("induction {}", term),
            Tactic::Rewrite(name) => format!("rewrite {}", name),
            Tactic::Simplify => "simplify".to_string(),
            Tactic::Reflexivity => "reflexivity".to_string(),
            Tactic::Assumption => "assumption".to_string(),
            Tactic::Exact(term) => format!("exact {}", term),
            Tactic::Custom { command, args, .. } => {
                if args.is_empty() {
                    command.clone()
                } else {
                    format!("{} {}", command, args.join(" "))
                }
            },
        }
    }

    /// Parse a JML-annotated Java source file into proof obligations.
    ///
    /// Extracts JML contracts (`requires`, `ensures`, `invariant`, `loop_invariant`,
    /// `assignable`, `decreases`) from Java source and creates one goal per
    /// annotated method or invariant.
    fn parse_jml_annotations(&self, content: &str) -> Vec<Goal> {
        let mut goals = Vec::new();
        let mut current_method: Option<String> = None;
        let mut jml_block = String::new();
        let mut in_jml = false;

        for line in content.lines() {
            let trimmed = line.trim();

            // Detect JML annotation blocks: //@ single-line or /*@ ... @*/ multi-line
            if trimmed.starts_with("//@") {
                let annotation = trimmed.trim_start_matches("//@").trim();
                jml_block.push_str(annotation);
                jml_block.push('\n');
                in_jml = true;
            } else if trimmed.starts_with("/*@") {
                in_jml = true;
                let rest = trimmed.trim_start_matches("/*@").trim();
                if !rest.is_empty() && !rest.starts_with("@*/") {
                    jml_block.push_str(rest.trim_end_matches("@*/").trim());
                    jml_block.push('\n');
                }
                if trimmed.contains("@*/") {
                    in_jml = false;
                }
            } else if in_jml {
                let cleaned = trimmed
                    .trim_start_matches('@')
                    .trim_start_matches('*')
                    .trim();
                if trimmed.contains("@*/") {
                    let before_close = cleaned
                        .trim_end_matches("@*/")
                        .trim_end_matches("*/")
                        .trim();
                    if !before_close.is_empty() {
                        jml_block.push_str(before_close);
                        jml_block.push('\n');
                    }
                    in_jml = false;
                } else if !cleaned.is_empty() {
                    jml_block.push_str(cleaned);
                    jml_block.push('\n');
                }
            } else if !jml_block.is_empty() {
                // First non-JML line after a JML block — try to find the method signature
                if trimmed.contains('(') && !trimmed.starts_with("//") {
                    // Extract method name from signature
                    if let Some(name) = Self::extract_method_name(trimmed) {
                        current_method = Some(name);
                    }
                }

                // Create a goal from the accumulated JML block
                if let Some(ref method) = current_method {
                    goals.push(Goal {
                        id: format!("jml_{}_{}", method, goals.len()),
                        target: Term::Const(jml_block.trim().to_string()),
                        hypotheses: vec![],
                    });
                } else {
                    // Class-level invariant or standalone annotation
                    goals.push(Goal {
                        id: format!("jml_invariant_{}", goals.len()),
                        target: Term::Const(jml_block.trim().to_string()),
                        hypotheses: vec![],
                    });
                }

                jml_block.clear();
                current_method = None;
            }
        }

        // Handle trailing JML block without a following method
        if !jml_block.is_empty() {
            goals.push(Goal {
                id: format!("jml_trailing_{}", goals.len()),
                target: Term::Const(jml_block.trim().to_string()),
                hypotheses: vec![],
            });
        }

        goals
    }

    /// Extract a method name from a Java method signature line.
    ///
    /// Handles signatures like `public int factorial(int n)`, `void run()`, etc.
    fn extract_method_name(line: &str) -> Option<String> {
        // Find the opening paren, then walk backwards to find the method name
        let paren_pos = line.find('(')?;
        let before_paren = line[..paren_pos].trim();
        let name = before_paren.split_whitespace().last()?;
        Some(name.to_string())
    }

    /// Parse a `.key` proof problem file into goals.
    ///
    /// Extracts the `\problem { ... }` block as the primary goal and any
    /// `\functions`, `\sorts`, or `\predicates` declarations as context.
    fn parse_key_file(&self, content: &str) -> (Vec<Goal>, Vec<String>) {
        let mut goals = Vec::new();
        let mut axioms = Vec::new();
        let mut in_problem = false;
        let mut problem_content = String::new();
        let mut brace_depth: i32 = 0;

        for line in content.lines() {
            let trimmed = line.trim();

            if trimmed.starts_with("\\problem") {
                in_problem = true;
                // Count braces on this line
                for ch in trimmed.chars() {
                    match ch {
                        '{' => brace_depth += 1,
                        '}' => brace_depth -= 1,
                        _ => {},
                    }
                }
                // Grab content after the opening brace
                if let Some(pos) = trimmed.find('{') {
                    let after = &trimmed[pos + 1..];
                    let cleaned = after.trim_end_matches('}').trim();
                    if !cleaned.is_empty() {
                        problem_content.push_str(cleaned);
                        problem_content.push('\n');
                    }
                }
                continue;
            }

            if in_problem {
                for ch in trimmed.chars() {
                    match ch {
                        '{' => brace_depth += 1,
                        '}' => brace_depth -= 1,
                        _ => {},
                    }
                }

                if brace_depth <= 0 {
                    // End of problem block — strip trailing brace
                    let cleaned = trimmed.trim_end_matches('}').trim();
                    if !cleaned.is_empty() {
                        problem_content.push_str(cleaned);
                    }
                    in_problem = false;
                } else {
                    problem_content.push_str(trimmed);
                    problem_content.push('\n');
                }
            }

            // Collect function/sort/predicate declarations as axiom context
            if trimmed.starts_with("\\functions")
                || trimmed.starts_with("\\sorts")
                || trimmed.starts_with("\\predicates")
            {
                axioms.push(trimmed.to_string());
            }
        }

        if !problem_content.is_empty() {
            goals.push(Goal {
                id: "key_problem_0".to_string(),
                target: Term::Const(problem_content.trim().to_string()),
                hypotheses: vec![],
            });
        }

        (goals, axioms)
    }
}

#[async_trait]
impl ProverBackend for KeyBackend {
    /// Returns the prover kind identifier for KeY
    fn kind(&self) -> ProverKind {
        ProverKind::KeY
    }

    /// Query the KeY installation for its version string
    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to execute KeY — is it installed and on PATH?")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let version_line = stdout
            .lines()
            .find(|l| l.contains("KeY") || l.contains("version"))
            .unwrap_or("unknown");

        Ok(version_line.trim().to_string())
    }

    /// Parse a `.key` or `.java` file into an ECHIDNA proof state
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context(format!("Failed to read KeY input file: {}", path.display()))?;

        let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");

        let mut state = match ext {
            "key" => {
                // Parse .key proof problem file
                let (goals, axioms) = self.parse_key_file(&content);
                ProofState {
                    goals: if goals.is_empty() {
                        vec![Goal {
                            id: "key_goal_0".to_string(),
                            target: Term::Const("true".to_string()),
                            hypotheses: vec![],
                        }]
                    } else {
                        goals
                    },
                    context: crate::core::Context {
                        axioms,
                        ..Default::default()
                    },
                    ..Default::default()
                }
            },
            "java" => {
                // Parse JML-annotated Java source
                let goals = self.parse_jml_annotations(&content);
                ProofState {
                    goals: if goals.is_empty() {
                        vec![Goal {
                            id: "java_goal_0".to_string(),
                            target: Term::Const("true".to_string()),
                            hypotheses: vec![],
                        }]
                    } else {
                        goals
                    },
                    ..Default::default()
                }
            },
            _ => {
                return Err(anyhow!(
                    "Unsupported file extension '{}' for KeY backend — expected .key or .java",
                    ext
                ));
            },
        };
        state.metadata.insert(
            "key_source".to_string(),
            serde_json::Value::String(content.clone()),
        );
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    /// Parse a proof problem from a raw string (assumes `.key` format)
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let (goals, axioms) = self.parse_key_file(content);

        let computed_goals = if goals.is_empty() {
            // Fallback: treat each non-empty, non-comment line as a goal
            let mut fallback_goals = Vec::new();
            for line in content.lines() {
                let trimmed = line.trim();
                if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with('\\') {
                    continue;
                }
                fallback_goals.push(Goal {
                    id: format!("goal_{}", fallback_goals.len()),
                    target: Term::Const(trimmed.to_string()),
                    hypotheses: vec![],
                });
            }
            if fallback_goals.is_empty() {
                vec![Goal {
                    id: "goal_0".to_string(),
                    target: Term::Const("true".to_string()),
                    hypotheses: vec![],
                }]
            } else {
                fallback_goals
            }
        } else {
            goals
        };

        let mut state = ProofState {
            goals: computed_goals,
            context: crate::core::Context {
                axioms,
                ..Default::default()
            },
            ..Default::default()
        };
        state.metadata.insert(
            "key_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        Ok(state)
    }

    /// Apply an interactive tactic to the current proof state.
    ///
    /// KeY supports interactive proof construction via `Tactic::Custom` with
    /// prover="key" and commands:
    ///   - `apply_rule <rule_name>` — apply a specific taclet/rule
    ///   - `apply_macro <macro_name>` — run a proof macro (e.g., "Full Auto")
    ///   - `set_strategy <strategy>` — change the active proof strategy
    ///   - `prune` — prune a proof branch back to parent node
    ///   - `auto` — run the automatic proof strategy
    ///
    /// Also supports generic tactics (Apply, Simplify, etc.) mapped to KeY equivalents.
    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // KeY-specific custom tactics
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "key" => {
                let tactic_str = if args.is_empty() {
                    command.clone()
                } else {
                    format!("{} {}", command, args.join(" "))
                };

                match command.as_str() {
                    "apply_rule" | "apply_macro" | "auto" => {
                        // These tactics invoke KeY's proof engine
                        let input = self.to_key_format(state)?;
                        let mut child = Command::new(&self.config.executable)
                            .args(["--auto", "--script"])
                            .arg(&tactic_str)
                            .stdin(Stdio::piped())
                            .stdout(Stdio::piped())
                            .stderr(Stdio::piped())
                            .spawn()
                            .context("Failed to spawn KeY for tactic application")?;

                        if let Some(mut stdin) = child.stdin.take() {
                            stdin.write_all(input.as_bytes()).await?;
                            drop(stdin);
                        }

                        let output = tokio::time::timeout(
                            tokio::time::Duration::from_secs(self.config.timeout + 5),
                            child.wait_with_output(),
                        )
                        .await
                        .context("KeY tactic application timed out")??;

                        let combined = format!(
                            "{}\n{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        );

                        match self.parse_result(&combined) {
                            Ok(true) => Ok(TacticResult::QED),
                            Ok(false) => {
                                let mut new_state = state.clone();
                                new_state.proof_script.push(tactic.clone());
                                Ok(TacticResult::Success(new_state))
                            },
                            Err(e) => Ok(TacticResult::Error(e.to_string())),
                        }
                    },
                    "set_strategy" => {
                        // Strategy change is metadata-only, no KeY invocation
                        let strategy_name = args.first().ok_or_else(|| {
                            anyhow!("set_strategy requires a strategy name argument")
                        })?;
                        let mut new_state = state.clone();
                        new_state.metadata.insert(
                            "key_strategy".to_string(),
                            serde_json::Value::String(strategy_name.clone()),
                        );
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    },
                    "prune" => {
                        // Prune removes the last proof step
                        let mut new_state = state.clone();
                        new_state.proof_script.pop();
                        Ok(TacticResult::Success(new_state))
                    },
                    _ => Ok(TacticResult::Error(format!(
                        "Unknown KeY command '{}'. Supported: apply_rule, apply_macro, \
                         set_strategy, prune, auto",
                        command
                    ))),
                }
            },

            // Map generic ECHIDNA tactics to KeY equivalents
            Tactic::Simplify => {
                let mut new_state = state.clone();
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => {
                // For other generic tactics, record and attempt
                let tactic_str = Self::tactic_to_string(tactic);
                Ok(TacticResult::Error(format!(
                    "KeY does not directly support tactic '{}'. \
                     Use Tactic::Custom {{ prover: \"key\", command: \"...\", args: [...] }} \
                     for KeY-specific commands.",
                    tactic_str
                )))
            },
        }
    }

    /// Verify a proof by running KeY's automatic strategy on the proof state.
    ///
    /// Spawns the KeY prover in headless/batch mode, feeds it the proof problem,
    /// and parses the output for "Proof closed" (success) or "open goals" (failure).
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Prefer the original .key/.java file — `to_key_format(state)` is
        // lossy for anything beyond trivial goals.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .args(["--auto", "--no-gui"])
                    .args(["--max-steps", &self.max_steps.to_string()])
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("KeY verification timed out")??;
            let combined = format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return self.parse_result(&combined);
        }

        let input = if let Some(src) = state.metadata.get("key_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_key_format(state)?
        };

        let mut child = Command::new(&self.config.executable)
            .args(["--auto", "--no-gui"])
            .args(["--max-steps", &self.max_steps.to_string()])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn KeY — is it installed and on PATH?")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("KeY verification timed out")??;

        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        self.parse_result(&combined)
    }

    /// Export the proof state to KeY `.key` problem file format
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_key_format(state)
    }

    /// Suggest interactive tactics for the current proof state.
    ///
    /// Returns KeY-specific tactics as `Tactic::Custom` variants. These cover
    /// the most commonly used KeY proof commands: automatic strategy, proof macros,
    /// JavaDL rule applications, and proof tree management.
    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Common KeY proof tactics, ordered by general usefulness
        let suggestions: Vec<Tactic> = vec![
            Tactic::Custom {
                prover: "key".to_string(),
                command: "auto".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_macro".to_string(),
                args: vec!["Full Auto".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_macro".to_string(),
                args: vec!["Finish Symbolic Execution".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["andRight".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["impRight".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["allRight".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["assignment".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["methodCall".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "apply_rule".to_string(),
                args: vec!["loopInvariant".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "set_strategy".to_string(),
                args: vec!["JavaCardDLStrategy".to_string()],
            },
            Tactic::Custom {
                prover: "key".to_string(),
                command: "prune".to_string(),
                args: vec![],
            },
        ];

        Ok(suggestions.into_iter().take(limit).collect())
    }

    /// Search for KeY taclets, rules, or lemmas matching a pattern.
    ///
    /// KeY has a rich built-in rule base (taclets). This performs a simple
    /// keyword match against well-known taclet categories.
    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        let lower = pattern.to_lowercase();
        let known_taclets: Vec<&str> = vec![
            "andLeft",
            "andRight",
            "orLeft",
            "orRight",
            "impLeft",
            "impRight",
            "notLeft",
            "notRight",
            "allLeft",
            "allRight",
            "exLeft",
            "exRight",
            "cut",
            "close",
            "closeTrue",
            "closeFalse",
            "assignment",
            "methodCall",
            "methodBodyExpand",
            "loopInvariant",
            "loopUnwind",
            "ifElseSplit",
            "ifThenElse",
            "pullOut",
            "simplify",
            "concrete",
            "hideLeft",
            "hideRight",
            "eqSymm",
            "eqClose",
            "induction",
            "wellOrderedInduction",
        ];

        let matches: Vec<String> = known_taclets
            .into_iter()
            .filter(|t| t.to_lowercase().contains(&lower))
            .map(|t| t.to_string())
            .collect();

        Ok(matches)
    }

    /// Return the current prover configuration
    fn config(&self) -> &ProverConfig {
        &self.config
    }

    /// Update the prover configuration
    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a test backend with default config
    fn test_backend() -> KeyBackend {
        KeyBackend::new(ProverConfig {
            executable: PathBuf::from("key"),
            timeout: 10,
            ..Default::default()
        })
    }

    #[tokio::test]
    async fn test_key_export_format() {
        let backend = test_backend();
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("x > 0 -> x >= 0".to_string()),
            hypotheses: vec![],
        });
        let output = backend.to_key_format(&state).unwrap();
        assert!(output.contains("\\profile"));
        assert!(output.contains("\\problem"));
        assert!(output.contains("x > 0 -> x >= 0"));
        assert!(output.contains("\\settings"));
    }

    #[tokio::test]
    async fn test_key_parse_string() {
        let backend = test_backend();
        let input = r#"
\profile "Java Profile";
\problem {
  \forall int x; (x > 0 -> x >= 0)
}
"#;
        let state = backend.parse_string(input).await.unwrap();
        assert!(!state.goals.is_empty());
        assert!(state.goals[0].target.to_string().contains("forall"));
    }

    #[test]
    fn test_key_parse_result_closed() {
        let backend = test_backend();
        assert!(backend.parse_result("Proof closed successfully.").unwrap());
    }

    #[test]
    fn test_key_parse_result_open() {
        let backend = test_backend();
        assert!(!backend.parse_result("3 open goals remaining").unwrap());
    }

    #[test]
    fn test_key_parse_result_error() {
        let backend = test_backend();
        assert!(backend.parse_result("ERROR: file not found").is_err());
    }

    #[test]
    fn test_key_jml_parsing() {
        let backend = test_backend();
        let java_src = r#"
public class Factorial {
    //@ requires n >= 0;
    //@ ensures \result >= 1;
    public static int factorial(int n) {
        if (n == 0) return 1;
        return n * factorial(n - 1);
    }
}
"#;
        let goals = backend.parse_jml_annotations(java_src);
        assert!(!goals.is_empty(), "Should extract JML annotations as goals");
        let goal_text = goals[0].target.to_string();
        assert!(
            goal_text.contains("requires") || goal_text.contains("ensures"),
            "Goal should contain JML contract terms"
        );
    }

    #[test]
    fn test_key_extract_method_name() {
        assert_eq!(
            KeyBackend::extract_method_name("public static int factorial(int n)"),
            Some("factorial".to_string())
        );
        assert_eq!(
            KeyBackend::extract_method_name("void run()"),
            Some("run".to_string())
        );
        assert_eq!(KeyBackend::extract_method_name("// just a comment"), None);
    }

    #[tokio::test]
    async fn test_key_suggest_tactics() {
        let backend = test_backend();
        let state = ProofState::default();
        let tactics = backend.suggest_tactics(&state, 3).await.unwrap();
        assert_eq!(tactics.len(), 3);
    }

    #[tokio::test]
    async fn test_key_search_theorems() {
        let backend = test_backend();
        let results = backend.search_theorems("loop").await.unwrap();
        assert!(results.iter().any(|r| r.contains("loop")));
    }

    #[test]
    fn test_key_parse_key_file() {
        let backend = test_backend();
        let content = r#"
\profile "Java Profile";

\sorts {
    MySort;
}

\functions {
    int f(int);
}

\problem {
    \forall int x; (f(x) >= 0)
}
"#;
        let (goals, axioms) = backend.parse_key_file(content);
        assert_eq!(goals.len(), 1);
        assert!(goals[0].target.to_string().contains("forall"));
        assert!(
            !axioms.is_empty(),
            "Should capture \\functions as axiom context"
        );
    }

    #[tokio::test]
    async fn test_key_apply_tactic_set_strategy() {
        let backend = test_backend();
        let state = ProofState::default();
        let tactic = Tactic::Custom {
            prover: "key".to_string(),
            command: "set_strategy".to_string(),
            args: vec!["JavaCardDLStrategy".to_string()],
        };
        let result = backend.apply_tactic(&state, &tactic).await.unwrap();
        match result {
            TacticResult::Success(new_state) => {
                assert!(new_state.metadata.contains_key("key_strategy"));
            },
            _ => panic!("Expected TacticResult::Success for set_strategy"),
        }
    }

    #[tokio::test]
    async fn test_key_apply_tactic_unsupported() {
        let backend = test_backend();
        let state = ProofState::default();
        let tactic = Tactic::Reflexivity;
        let result = backend.apply_tactic(&state, &tactic).await.unwrap();
        match result {
            TacticResult::Error(_) => {}, // Expected
            _ => panic!("Expected TacticResult::Error for unsupported tactic"),
        }
    }
}
