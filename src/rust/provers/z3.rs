// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! Z3 SMT Solver Backend
//!
//! Implements Z3 theorem prover integration with SMT-LIB 2.0 support.
//! Z3 is a Tier 1 SMT solver supporting multiple theories:
//! - QF_UF: Uninterpreted functions
//! - QF_LIA/QF_NIA: Linear/nonlinear integer arithmetic
//! - QF_BV: Bitvectors
//! - Arrays, datatypes, quantifiers, etc.

use anyhow::{anyhow, bail, Context as AnyhowContext, Result};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::{Child, Command};
use tokio::time::{timeout, Duration};

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Z3 SMT solver backend
pub struct Z3Backend {
    config: ProverConfig,
}

impl Z3Backend {
    /// Create a new Z3 backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        Z3Backend { config }
    }

    /// Launch Z3 process in interactive mode
    async fn spawn_z3(&self) -> Result<Child> {
        let mut cmd = Command::new(&self.config.executable);
        cmd.arg("-in") // Read from stdin
            .arg("-smt2") // SMT-LIB 2.0 format
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Add custom arguments
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        cmd.spawn()
            .with_context(|| format!("Failed to spawn Z3 process: {:?}", self.config.executable))
    }

    /// Execute a single SMT-LIB command and get response
    async fn execute_command(&self, command: &str) -> Result<SmtResult> {
        let mut child = self.spawn_z3().await?;

        let mut stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow!("Failed to open Z3 stdin"))?;
        // NOTE: do NOT take() child.stdout — wait_with_output() needs it intact.

        // Write command and signal EOF so Z3 knows to terminate.
        stdin.write_all(command.as_bytes()).await?;
        stdin.write_all(b"\n(exit)\n").await?;
        stdin.flush().await?;
        drop(stdin);

        // Read response with timeout
        let timeout_duration = Duration::from_secs(self.config.timeout);
        let output = timeout(timeout_duration, child.wait_with_output())
            .await
            .map_err(|_| anyhow!("Z3 execution timeout after {} seconds", self.config.timeout))??;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            // Z3 sometimes reports errors in stdout
            let error_msg = if stderr.trim().is_empty() {
                stdout.to_string()
            } else {
                format!("{}\n{}", stderr, stdout)
            };
            bail!("Z3 failed: {}", error_msg.trim());
        }

        let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
        self.parse_smt_result(&stdout_str)
    }

    /// Parse SMT-LIB result from Z3 output.
    ///
    /// Z3 may emit `success` acknowledgements for each command before the final
    /// `check-sat` result. We take the **last non-empty line** as the answer;
    /// matching on the whole output with `contains()` would misclassify output
    /// containing both "success" lines and "unsat".
    fn parse_smt_result(&self, output: &str) -> Result<SmtResult> {
        // Find the last non-empty line — that is Z3's answer to (check-sat).
        let last = output
            .lines()
            .rev()
            .map(str::trim)
            .find(|l| !l.is_empty())
            .unwrap_or("");

        if last == "unsat" {
            Ok(SmtResult::Unsat)
        } else if last == "sat" {
            Ok(SmtResult::Sat)
        } else if last == "unknown" {
            Ok(SmtResult::Unknown)
        } else if last.starts_with("(error") {
            let error_msg = last
                .trim_start_matches("(error")
                .trim_end_matches(')')
                .trim()
                .trim_matches('"');
            Ok(SmtResult::Error(error_msg.to_string()))
        } else {
            // Other output (get-model, get-value, etc.) — return verbatim.
            Ok(SmtResult::Output(last.to_string()))
        }
    }

    /// Parse SMT-LIB 2.0 file into ProofState
    fn parse_smt_file(&self, content: &str) -> Result<ProofState> {
        let mut parser = SmtParser::new(content);
        parser.parse()
    }

    /// Convert SMT term to universal Term
    fn smt_to_term(&self, smt_term: &SmtTerm) -> Term {
        match smt_term {
            SmtTerm::Symbol(s) => Term::Var(s.clone()),
            SmtTerm::Numeral(n) => Term::Const(n.to_string()),
            SmtTerm::Bool(b) => Term::Const(b.to_string()),
            SmtTerm::App { func, args } => Term::App {
                func: Box::new(Term::Const(func.clone())),
                args: args.iter().map(|a| self.smt_to_term(a)).collect(),
            },
            SmtTerm::Quantified {
                quantifier,
                bindings,
                body,
            } => {
                let term_body = self.smt_to_term(body);
                bindings
                    .iter()
                    .rev()
                    .fold(term_body, |acc, (var, ty)| Term::App {
                        func: Box::new(Term::Const(quantifier.clone())),
                        args: vec![Term::Lambda {
                            param: var.clone(),
                            param_type: Some(Box::new(self.smt_to_term(ty))),
                            body: Box::new(acc),
                        }],
                    })
            },
            SmtTerm::Let { bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings
                    .iter()
                    .rev()
                    .fold(term_body, |acc, (var, val)| Term::App {
                        func: Box::new(Term::Lambda {
                            param: var.clone(),
                            param_type: None,
                            body: Box::new(acc),
                        }),
                        args: vec![self.smt_to_term(val)],
                    })
            },
        }
    }

    /// Convert universal Term to SMT-LIB format
    fn term_to_smt(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                if args.is_empty() {
                    self.term_to_smt(func)
                } else {
                    let func_str = self.term_to_smt(func);
                    let args_str: Vec<String> = args.iter().map(|a| self.term_to_smt(a)).collect();
                    format!("({} {})", func_str, args_str.join(" "))
                }
            },
            _ => {
                format!(
                    "(:echidna {})",
                    serde_json::to_string(term).unwrap_or_default()
                )
            },
        }
    }

    /// Check if assertion is satisfiable
    async fn check_sat(&self, assertions: &[String]) -> Result<SmtResult> {
        let mut commands = String::new();

        for assertion in assertions {
            commands.push_str(&format!("(assert {})\n", assertion));
        }
        commands.push_str("(check-sat)\n");

        self.execute_command(&commands).await
    }
}

#[async_trait]
impl ProverBackend for Z3Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Z3
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Z3 version")?;

        let version = String::from_utf8_lossy(&output.stdout).to_string();
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .with_context(|| format!("Failed to read file: {:?}", path))?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_smt_file(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Simplify => {
                if state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                let goal = &state.goals[0];
                let smt_goal = self.term_to_smt(&goal.target);

                let command = format!("(simplify {})", smt_goal);
                let result = self.execute_command(&command).await?;

                match result {
                    SmtResult::Output(simplified) => {
                        let mut parser = SmtParser::new(&simplified);
                        let simplified_term = parser.parse_term()?;

                        let mut new_state = state.clone();
                        if !new_state.goals.is_empty() {
                            new_state.goals[0].target = self.smt_to_term(&simplified_term);
                        }
                        new_state.proof_script.push(tactic.clone());

                        Ok(TacticResult::Success(new_state))
                    },
                    _ => Ok(TacticResult::Error("Simplification failed".to_string())),
                }
            },

            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "z3" => {
                let smt_command = if args.is_empty() {
                    command.clone()
                } else {
                    format!("({} {})", command, args.join(" "))
                };

                let result = self.execute_command(&smt_command).await?;

                match result {
                    SmtResult::Output(output) => {
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        new_state
                            .metadata
                            .insert("last_result".to_string(), serde_json::Value::String(output));
                        Ok(TacticResult::Success(new_state))
                    },
                    SmtResult::Error(e) => Ok(TacticResult::Error(e)),
                    _ => Ok(TacticResult::Error("Unexpected result".to_string())),
                }
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for Z3",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.goals.is_empty() {
            return Ok(true);
        }
        if state
            .goals
            .iter()
            .all(|g| matches!(&g.target, Term::Const(c) if c == "true"))
        {
            return Ok(true);
        }
        if state
            .goals
            .iter()
            .any(|g| matches!(&g.target, Term::Const(c) if c == "false"))
        {
            return Ok(false);
        }

        // Build complete SMT-LIB query with variable declarations
        let mut commands = String::new();
        commands.push_str("(set-logic ALL)\n");

        // Include variable declarations from context
        for var in &state.context.variables {
            let ty_smt = self.term_to_smt(&var.ty);
            commands.push_str(&format!("(declare-const {} {})\n", var.name, ty_smt));
        }

        // Assert negation of each goal (if unsat, goal is valid)
        for goal in &state.goals {
            let smt_goal = self.term_to_smt(&goal.target);
            commands.push_str(&format!("(assert (not {}))\n", smt_goal));
        }

        commands.push_str("(check-sat)\n");

        let result = self.execute_command(&commands).await?;

        match result {
            SmtResult::Unsat => Ok(true),
            SmtResult::Sat => Ok(false),
            SmtResult::Unknown => Ok(false),
            SmtResult::Error(e) => bail!("Verification error: {}", e),
            SmtResult::Output(_) => Ok(false),
        }
    }

    /// Typed verification with precise outcome classification.
    ///
    /// This override distinguishes:
    /// - `Proved` (negation of goal is UNSAT with hypotheses)
    /// - `InconsistentPremises` (hypotheses alone are UNSAT, making any proof trivial)
    /// - `NoProofFound` with `reason: Some("counterexample")` (SAT result)
    /// - `NoProofFound` with `reason: Some("SMT unknown")` (decidability limit)
    /// - `Timeout` (Z3 process timed out before producing an answer)
    /// - `InvalidInput` (Z3 reported `(error ...)` for a user input problem)
    /// - `ProverError` (Z3 reported an internal error)
    /// - `SystemError` (Z3 process could not be spawned)
    async fn check(
        &self,
        state: &ProofState,
    ) -> anyhow::Result<super::outcome::ProverOutcome> {
        use super::outcome::ProverOutcome;
        use std::time::Instant;
        let start = Instant::now();

        // Vacuous case: no goals at all → trivially proved (no outstanding obligations).
        if state.goals.is_empty() {
            return Ok(ProverOutcome::Proved { elapsed_ms: 0 });
        }

        // Step 1: Consistency pre-check — must run before any trivial-goal
        // short-circuit so that P∧¬P is never silently rubber-stamped as PROVED.
        //
        // Two sub-checks:
        //   (a) Axiom consistency: assert all axioms; if UNSAT, premises alone
        //       are contradictory — any goal follows trivially.
        //   (b) Goal consistency: assert all goals (without negation); if UNSAT,
        //       the goal set is self-contradictory (e.g. prove P and prove ¬P
        //       simultaneously). This is a weaker signal but still suspect.
        //
        // Either condition surfaces as InconsistentPremises so the caller knows
        // the result cannot be trusted.

        // Build the common preamble (variable declarations) once.
        let mut preamble = String::from("(set-logic ALL)\n");
        for var in &state.context.variables {
            preamble.push_str(&format!(
                "(declare-const {} {})\n",
                var.name,
                self.term_to_smt(&var.ty)
            ));
        }

        // (a) Axiom consistency.
        let axioms_inconsistent = if !state.context.axioms.is_empty() {
            let mut hyp_check = preamble.clone();
            for axiom in &state.context.axioms {
                hyp_check.push_str(&format!("(assert {})\n", axiom));
            }
            hyp_check.push_str("(check-sat)\n");
            matches!(self.execute_command(&hyp_check).await, Ok(SmtResult::Unsat))
        } else {
            false
        };

        // (b) Goal consistency — only worth checking when axioms are fine, to
        // avoid masking the more informative axiom-level diagnosis.
        let goals_inconsistent = if !axioms_inconsistent {
            let mut goal_check = preamble.clone();
            for axiom in &state.context.axioms {
                goal_check.push_str(&format!("(assert {})\n", axiom));
            }
            for goal in &state.goals {
                // Assert goals as-is (no negation): if UNSAT, the goals themselves
                // cannot all be true simultaneously.
                goal_check.push_str(&format!("(assert {})\n", self.term_to_smt(&goal.target)));
            }
            goal_check.push_str("(check-sat)\n");
            matches!(self.execute_command(&goal_check).await, Ok(SmtResult::Unsat))
        } else {
            false
        };

        if axioms_inconsistent {
            return Ok(ProverOutcome::InconsistentPremises {
                detail: Some(
                    "axioms are mutually unsatisfiable; any goal follows trivially".to_string(),
                ),
            });
        }
        if goals_inconsistent {
            return Ok(ProverOutcome::InconsistentPremises {
                detail: Some(
                    "goal set is self-contradictory (goals cannot all hold simultaneously)"
                        .to_string(),
                ),
            });
        }

        // Trivial-goal short-circuit: only reached when premises are consistent
        // (or there are no axioms at all).
        if state
            .goals
            .iter()
            .all(|g| matches!(&g.target, Term::Const(c) if c == "true"))
        {
            return Ok(ProverOutcome::Proved { elapsed_ms: 0 });
        }

        // Step 2: Build the main validity query.
        // Reuse the preamble (variables already declared), add axioms and the
        // negation of each goal. UNSAT → goal follows from axioms → PROVED.
        let mut commands = preamble;
        for axiom in &state.context.axioms {
            commands.push_str(&format!("(assert {})\n", axiom));
        }
        for goal in &state.goals {
            commands.push_str(&format!("(assert (not {}))\n", self.term_to_smt(&goal.target)));
        }
        commands.push_str("(check-sat)\n");

        let elapsed = || start.elapsed().as_millis() as u64;

        match self.execute_command(&commands).await {
            // `inconsistent` is always false here (we returned early above if true).
            Ok(SmtResult::Unsat) => {
                Ok(ProverOutcome::Proved { elapsed_ms: elapsed() })
            },
            Ok(SmtResult::Sat) => Ok(ProverOutcome::NoProofFound {
                elapsed_ms: elapsed(),
                reason: Some("Z3 found a counterexample (SAT)".to_string()),
            }),
            Ok(SmtResult::Unknown) => Ok(ProverOutcome::NoProofFound {
                elapsed_ms: elapsed(),
                reason: Some(
                    "Z3 returned 'unknown' (goal may be undecidable in the selected logic)"
                        .to_string(),
                ),
            }),
            Ok(SmtResult::Error(e)) => {
                // Z3 `(error ...)` is almost always a user input problem.
                if e.to_lowercase().contains("unknown")
                    || e.to_lowercase().contains("unsupported")
                    || e.to_lowercase().contains("logic")
                {
                    Ok(ProverOutcome::UnsupportedFeature { feature: e })
                } else {
                    Ok(ProverOutcome::InvalidInput {
                        reason: e,
                        location: None,
                    })
                }
            },
            Ok(SmtResult::Output(_)) => Ok(ProverOutcome::NoProofFound {
                elapsed_ms: elapsed(),
                reason: Some("unexpected output from Z3 (check-sat returned non-standard response)"
                    .to_string()),
            }),
            Err(e) => {
                let msg = e.to_string().to_lowercase();
                if msg.contains("timeout") || msg.contains("timed out") {
                    Ok(ProverOutcome::Timeout {
                        limit_secs: self.config.timeout,
                    })
                } else if msg.contains("failed to spawn")
                    || msg.contains("no such file")
                    || msg.contains("os error")
                {
                    Ok(ProverOutcome::SystemError { detail: e.to_string() })
                } else {
                    Ok(ProverOutcome::ProverError {
                        detail: e.to_string(),
                        exit_code: None,
                    })
                }
            },
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        output.push_str("; ECHIDNA Z3 Export\n");
        output.push_str("; Generated SMT-LIB 2.0 file\n\n");
        output.push_str("(set-logic ALL)\n\n");

        for var in &state.context.variables {
            let ty_smt = self.term_to_smt(&var.ty);
            output.push_str(&format!("(declare-const {} {})\n", var.name, ty_smt));
        }

        output.push('\n');

        for theorem in &state.context.theorems {
            let stmt_smt = self.term_to_smt(&theorem.statement);
            output.push_str(&format!("; Theorem: {}\n", theorem.name));
            output.push_str(&format!("(assert {})\n\n", stmt_smt));
        }

        for goal in &state.goals {
            output.push_str(&format!("; Goal: {}\n", goal.id));
            let goal_smt = self.term_to_smt(&goal.target);
            output.push_str(&format!("(assert {})\n\n", goal_smt));
        }

        output.push_str("(check-sat)\n");
        output.push_str("(get-model)\n");

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        if !self.config.neural_enabled {
            return Ok(vec![]);
        }

        let mut tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then simplify solve-eqs)".to_string()],
            },
            Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then ctx-simplify propagate-values)".to_string()],
            },
        ];

        if state.goals.iter().any(|g| {
            let term_str = format!("{:?}", g.target);
            term_str.contains('+') || term_str.contains('-') || term_str.contains('*')
        }) {
            tactics.push(Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then simplify normalize-bounds lia2pb pb2bv bit-blast)".to_string()],
            });
        }

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

/// SMT-LIB result from Z3
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
    Output(String),
}

/// SMT-LIB term representation
#[derive(Debug, Clone, PartialEq)]
pub enum SmtTerm {
    Symbol(String),
    Numeral(i64),
    Bool(bool),
    App {
        func: String,
        args: Vec<SmtTerm>,
    },
    Quantified {
        quantifier: String,
        bindings: Vec<(String, SmtTerm)>,
        body: Box<SmtTerm>,
    },
    Let {
        bindings: Vec<(String, SmtTerm)>,
        body: Box<SmtTerm>,
    },
}

/// SMT-LIB 2.0 parser
pub struct SmtParser {
    tokens: Vec<String>,
    pos: usize,
}

impl SmtParser {
    pub fn new(input: &str) -> Self {
        let tokens = Self::tokenize(input);
        SmtParser { tokens, pos: 0 }
    }

    fn tokenize(input: &str) -> Vec<String> {
        let mut tokens = Vec::new();
        let mut current = String::new();
        let mut in_string = false;
        let mut in_comment = false;

        for ch in input.chars() {
            if in_comment {
                if ch == '\n' {
                    in_comment = false;
                }
                continue;
            }

            match ch {
                ';' if !in_string => {
                    in_comment = true;
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                },
                '"' => {
                    in_string = !in_string;
                    current.push(ch);
                },
                '(' | ')' if !in_string => {
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                    tokens.push(ch.to_string());
                },
                ' ' | '\n' | '\t' if !in_string => {
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                },
                _ => {
                    current.push(ch);
                },
            }
        }

        if !current.is_empty() {
            tokens.push(current);
        }

        tokens
    }

    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(|s| s.as_str())
    }

    fn next(&mut self) -> Option<String> {
        if self.pos < self.tokens.len() {
            let token = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(token)
        } else {
            None
        }
    }

    fn expect(&mut self, expected: &str) -> Result<()> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => bail!("Expected '{}', got '{}'", expected, token),
            None => bail!("Expected '{}', got EOF", expected),
        }
    }

    pub fn parse(&mut self) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        let mut assertions = Vec::new();

        while self.peek().is_some() {
            self.expect("(")?;

            match self.peek() {
                Some("declare-const") => {
                    self.next();
                    let name = self
                        .next()
                        .ok_or_else(|| anyhow!("Expected variable name"))?;
                    let ty_term = self.parse_term()?;
                    self.expect(")")?;

                    state.context.variables.push(crate::core::Variable {
                        name: name.clone(),
                        ty: self.smt_to_term(&ty_term),
                    });
                },

                Some("declare-fun") => {
                    self.next();
                    let name = self
                        .next()
                        .ok_or_else(|| anyhow!("Expected function name"))?;
                    self.expect("(")?;

                    let mut param_types = Vec::new();
                    while self.peek() != Some(")") {
                        param_types.push(self.parse_term()?);
                    }
                    self.expect(")")?;

                    let return_type = self.parse_term()?;
                    self.expect(")")?;

                    let mut ty = self.smt_to_term(&return_type);
                    for param_ty in param_types.iter().rev() {
                        ty = Term::App {
                            func: Box::new(Term::Const("->".to_string())),
                            args: vec![self.smt_to_term(param_ty), ty],
                        };
                    }

                    state.context.variables.push(crate::core::Variable {
                        name: name.clone(),
                        ty,
                    });
                },

                Some("assert") => {
                    self.next();
                    let assertion = self.parse_term()?;
                    self.expect(")")?;

                    assertions.push(assertion);
                },

                Some("check-sat") => {
                    self.next();
                    self.expect(")")?;

                    for (idx, assertion) in assertions.iter().enumerate() {
                        state.goals.push(Goal {
                            id: format!("goal_{}", idx),
                            target: self.smt_to_term(assertion),
                            hypotheses: vec![],
                        });
                    }
                },

                Some("set-logic") | Some("set-option") | Some("set-info") => {
                    self.next();
                    let mut depth = 1;
                    while depth > 0 {
                        match self.next() {
                            Some(token) if token == "(" => depth += 1,
                            Some(token) if token == ")" => depth -= 1,
                            None => bail!("Unexpected EOF in command"),
                            _ => {},
                        }
                    }
                },

                _ => {
                    let mut depth = 1;
                    while depth > 0 {
                        match self.next() {
                            Some(token) if token == "(" => depth += 1,
                            Some(token) if token == ")" => depth -= 1,
                            None => bail!("Unexpected EOF"),
                            _ => {},
                        }
                    }
                },
            }
        }

        Ok(state)
    }

    pub fn parse_term(&mut self) -> Result<SmtTerm> {
        match self.peek() {
            Some("(") => {
                self.next();

                match self.peek() {
                    Some("forall") | Some("exists") => {
                        let quantifier = self
                            .next()
                            .ok_or_else(|| anyhow!("unexpected end of tokens"))?;
                        self.expect("(")?;

                        let mut bindings = Vec::new();
                        while self.peek() != Some(")") {
                            self.expect("(")?;
                            let var = self.next().ok_or_else(|| anyhow!("Expected variable"))?;
                            let ty = self.parse_term()?;
                            self.expect(")")?;
                            bindings.push((var, ty));
                        }
                        self.expect(")")?;

                        let body = Box::new(self.parse_term()?);
                        self.expect(")")?;

                        Ok(SmtTerm::Quantified {
                            quantifier,
                            bindings,
                            body,
                        })
                    },

                    Some("let") => {
                        self.next();
                        self.expect("(")?;

                        let mut bindings = Vec::new();
                        while self.peek() != Some(")") {
                            self.expect("(")?;
                            let var = self.next().ok_or_else(|| anyhow!("Expected variable"))?;
                            let val = self.parse_term()?;
                            self.expect(")")?;
                            bindings.push((var, val));
                        }
                        self.expect(")")?;

                        let body = Box::new(self.parse_term()?);
                        self.expect(")")?;

                        Ok(SmtTerm::Let { bindings, body })
                    },

                    Some(_) => {
                        let func = self
                            .next()
                            .ok_or_else(|| anyhow!("unexpected end of tokens"))?;
                        let mut args = Vec::new();

                        while self.peek() != Some(")") {
                            args.push(self.parse_term()?);
                        }
                        self.expect(")")?;

                        Ok(SmtTerm::App { func, args })
                    },

                    None => bail!("Unexpected EOF"),
                }
            },

            Some("true") => {
                self.next();
                Ok(SmtTerm::Bool(true))
            },

            Some("false") => {
                self.next();
                Ok(SmtTerm::Bool(false))
            },

            Some(_) => {
                let token = self
                    .next()
                    .ok_or_else(|| anyhow!("unexpected end of tokens"))?;

                if let Ok(n) = token.parse::<i64>() {
                    Ok(SmtTerm::Numeral(n))
                } else {
                    Ok(SmtTerm::Symbol(token))
                }
            },

            None => bail!("Unexpected EOF"),
        }
    }

    fn smt_to_term(&self, smt_term: &SmtTerm) -> Term {
        match smt_term {
            SmtTerm::Symbol(s) => Term::Var(s.clone()),
            SmtTerm::Numeral(n) => Term::Const(n.to_string()),
            SmtTerm::Bool(b) => Term::Const(b.to_string()),
            SmtTerm::App { func, args } => Term::App {
                func: Box::new(Term::Const(func.clone())),
                args: args.iter().map(|a| self.smt_to_term(a)).collect(),
            },
            SmtTerm::Quantified {
                quantifier,
                bindings,
                body,
            } => {
                let term_body = self.smt_to_term(body);
                bindings
                    .iter()
                    .rev()
                    .fold(term_body, |acc, (var, ty)| Term::App {
                        func: Box::new(Term::Const(quantifier.clone())),
                        args: vec![Term::Lambda {
                            param: var.clone(),
                            param_type: Some(Box::new(self.smt_to_term(ty))),
                            body: Box::new(acc),
                        }],
                    })
            },
            SmtTerm::Let { bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings
                    .iter()
                    .rev()
                    .fold(term_body, |acc, (var, val)| Term::App {
                        func: Box::new(Term::Lambda {
                            param: var.clone(),
                            param_type: None,
                            body: Box::new(acc),
                        }),
                        args: vec![self.smt_to_term(val)],
                    })
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() {
        let input = "(declare-const x Int)";
        let tokens = SmtParser::tokenize(input);
        assert_eq!(tokens, vec!["(", "declare-const", "x", "Int", ")"]);
    }

    #[test]
    fn test_parse_simple_term() -> Result<()> {
        let mut parser = SmtParser::new("42");
        let term = parser.parse_term()?;
        assert_eq!(term, SmtTerm::Numeral(42));
        Ok(())
    }

    #[test]
    fn test_parse_app() -> Result<()> {
        let mut parser = SmtParser::new("(+ x y)");
        let term = parser.parse_term()?;
        match term {
            SmtTerm::App { func, args } => {
                assert_eq!(func, "+");
                assert_eq!(args.len(), 2);
            },
            _ => panic!("Expected App"),
        }
        Ok(())
    }

    #[tokio::test]
    async fn test_z3_backend_version() {
        let config = ProverConfig {
            executable: PathBuf::from("z3"),
            ..Default::default()
        };

        let backend = Z3Backend::new(config);

        if let Ok(version) = backend.version().await {
            assert!(version.contains("Z3") || version.contains("version"));
        }
    }
}
