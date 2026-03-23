// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! dReal SMT Solver Backend
//!
//! Implements dReal integration for delta-complete decision procedures over
//! nonlinear arithmetic of the reals. dReal supports SMT-LIB 2.0 input with
//! the QF_NRA and QF_NRA_ODE logics.
//!
//! Key characteristics:
//! - **Delta-satisfiability**: dReal implements delta-complete decision procedures,
//!   meaning it is sound but may return "delta-sat" instead of "sat". A delta-sat
//!   result means the formula is satisfiable within a perturbation of delta.
//! - **Nonlinear real arithmetic**: Supports transcendental functions (sin, cos,
//!   exp, log, pow), polynomials, and ODE constraints.
//! - **No interactive tactics**: dReal is fully automated; tactic application
//!   returns an error.
//! - **Precision control**: The delta precision parameter controls the trade-off
//!   between soundness and completeness (smaller delta = tighter bounds).

use async_trait::async_trait;
use anyhow::{anyhow, bail, Context as AnyhowContext, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use tokio::time::{timeout, Duration};

use crate::core::{ProofState, Tactic, TacticResult, Term};
use super::{ProverBackend, ProverConfig, ProverKind};
use super::z3::SmtParser;

/// Default delta-precision for dReal's decision procedures.
///
/// Controls the trade-off between soundness and completeness:
/// - Smaller values yield tighter interval bounds but longer solve times.
/// - Larger values are faster but may produce coarser approximations.
const DEFAULT_PRECISION: f64 = 0.001;

/// dReal SMT solver backend for nonlinear real arithmetic
///
/// dReal is a delta-complete SMT solver that handles QF_NRA (quantifier-free
/// nonlinear real arithmetic) and QF_NRA_ODE (with ordinary differential
/// equation constraints). It uses interval constraint propagation (ICP) and
/// returns one of three verdicts:
///
/// - `unsat`: The formula is unsatisfiable (verified).
/// - `delta-sat`: The formula is satisfiable within a delta-perturbation.
/// - `unknown`: The solver could not determine satisfiability.
pub struct DRealBackend {
    /// Prover configuration (executable path, timeout, arguments, etc.)
    config: ProverConfig,

    /// Delta precision for the decision procedure.
    ///
    /// Passed to dReal via `--precision <value>`. A smaller precision means
    /// tighter interval bounds on witness values but potentially longer
    /// computation times. Default: 0.001.
    precision: f64,
}

/// Result from dReal's SMT-LIB output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DRealResult {
    /// The formula is unsatisfiable (proven valid when checking negation)
    Unsat,

    /// The formula is delta-satisfiable: satisfiable within a perturbation
    /// of the configured precision. The `f64` records the delta used.
    DeltaSat(f64),

    /// The solver could not determine satisfiability within resource limits
    Unknown,

    /// An error occurred during solving
    Error(String),

    /// Raw output from a non-check-sat command
    Output(String),
}

impl DRealBackend {
    /// Create a new dReal backend with configuration and default precision
    pub fn new(config: ProverConfig) -> Self {
        DRealBackend {
            config,
            precision: DEFAULT_PRECISION,
        }
    }

    /// Create a new dReal backend with explicit precision
    ///
    /// # Arguments
    /// * `config` - Prover configuration
    /// * `precision` - Delta precision (must be > 0.0)
    ///
    /// # Panics
    /// Panics if `precision` is not a positive finite number.
    pub fn with_precision(config: ProverConfig, precision: f64) -> Self {
        assert!(
            precision > 0.0 && precision.is_finite(),
            "dReal precision must be a positive finite number, got: {}",
            precision
        );
        DRealBackend { config, precision }
    }

    /// Get the current precision
    pub fn precision(&self) -> f64 {
        self.precision
    }

    /// Set the precision for subsequent solves
    ///
    /// # Panics
    /// Panics if `precision` is not a positive finite number.
    pub fn set_precision(&mut self, precision: f64) {
        assert!(
            precision > 0.0 && precision.is_finite(),
            "dReal precision must be a positive finite number, got: {}",
            precision
        );
        self.precision = precision;
    }

    /// Execute an SMT-LIB 2.0 command string through dReal
    ///
    /// Spawns a dReal process, pipes the command to stdin, and parses the
    /// output. The `--precision` flag is always passed to control delta.
    async fn execute_command(&self, command: &str) -> Result<DRealResult> {
        let mut cmd = Command::new(&self.config.executable);

        // dReal reads SMT-LIB from stdin when given `-` as argument
        cmd.arg("--in")
            .arg("--precision")
            .arg(format!("{}", self.precision))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Append any user-supplied arguments (e.g., --polytope, --forall)
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        let mut child = cmd.spawn()
            .with_context(|| format!(
                "Failed to spawn dReal process: {:?}",
                self.config.executable
            ))?;

        // Write SMT-LIB commands to stdin
        let mut stdin = child.stdin.take()
            .ok_or_else(|| anyhow!("Failed to open dReal stdin"))?;

        stdin.write_all(command.as_bytes()).await?;
        stdin.write_all(b"\n(exit)\n").await?;
        stdin.flush().await?;
        drop(stdin);

        // Wait for output with timeout
        let timeout_duration = Duration::from_secs(self.config.timeout);
        let output = timeout(timeout_duration, child.wait_with_output()).await
            .map_err(|_| anyhow!(
                "dReal execution timeout after {} seconds",
                self.config.timeout
            ))??;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let error_msg = if stderr.trim().is_empty() {
                stdout.to_string()
            } else {
                format!("{}\n{}", stderr, stdout)
            };
            bail!("dReal failed: {}", error_msg.trim());
        }

        let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
        self.parse_dreal_result(&stdout_str)
    }

    /// Parse dReal's output into a structured result
    ///
    /// dReal can produce:
    /// - `unsat` — the formula is unsatisfiable
    /// - `delta-sat with delta = <value>` — satisfiable within delta
    /// - `unknown` — indeterminate
    /// - `(error ...)` — solver error
    fn parse_dreal_result(&self, output: &str) -> Result<DRealResult> {
        let trimmed = output.trim();

        // Check for delta-sat first (contains "sat" but is distinct from plain sat)
        if trimmed.contains("delta-sat") {
            // Parse the delta value from "delta-sat with delta = 0.001"
            let delta = self.extract_delta_value(trimmed);
            return Ok(DRealResult::DeltaSat(delta));
        }

        if trimmed.contains("unsat") {
            return Ok(DRealResult::Unsat);
        }

        if trimmed.contains("unknown") {
            return Ok(DRealResult::Unknown);
        }

        if trimmed.starts_with("(error") {
            let error_msg = trimmed
                .trim_start_matches("(error")
                .trim_end_matches(')')
                .trim()
                .trim_matches('"')
                .to_string();
            return Ok(DRealResult::Error(error_msg));
        }

        // For other commands, return raw output
        Ok(DRealResult::Output(trimmed.to_string()))
    }

    /// Extract the delta value from dReal's "delta-sat with delta = <value>" output
    ///
    /// Falls back to the configured precision if parsing fails.
    fn extract_delta_value(&self, output: &str) -> f64 {
        // dReal typically outputs: "delta-sat with delta = 0.001"
        if let Some(pos) = output.find("delta =") {
            let after_eq = &output[pos + "delta =".len()..];
            let value_str = after_eq.trim().split_whitespace().next().unwrap_or("");
            value_str.parse::<f64>().unwrap_or(self.precision)
        } else {
            self.precision
        }
    }

    /// Convert a universal Term to SMT-LIB 2.0 format string
    fn term_to_smt(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                if args.is_empty() {
                    self.term_to_smt(func)
                } else {
                    let func_str = self.term_to_smt(func);
                    let args_str: Vec<String> = args.iter()
                        .map(|a| self.term_to_smt(a))
                        .collect();
                    format!("({} {})", func_str, args_str.join(" "))
                }
            }
            _ => {
                format!("(:echidna {})", serde_json::to_string(term).unwrap_or_default())
            }
        }
    }

    /// Build a complete SMT-LIB 2.0 query for checking validity of goals
    ///
    /// The strategy is standard for SMT-based verification: negate all goals
    /// and check satisfiability. If the negation is unsatisfiable, the original
    /// goals are valid. If delta-sat, we cannot confirm validity.
    fn build_verification_query(&self, state: &ProofState) -> String {
        let mut commands = String::new();

        // Use QF_NRA logic (quantifier-free nonlinear real arithmetic)
        commands.push_str("(set-logic QF_NRA)\n");

        // Declare all variables from the proof context
        for var in &state.context.variables {
            let ty_smt = self.term_to_smt(&var.ty);
            commands.push_str(&format!("(declare-fun {} () {})\n", var.name, ty_smt));
        }

        // Assert the negation of each goal
        for goal in &state.goals {
            let smt_goal = self.term_to_smt(&goal.target);
            commands.push_str(&format!("(assert (not {}))\n", smt_goal));
        }

        commands.push_str("(check-sat)\n");
        commands
    }
}

#[async_trait]
impl ProverBackend for DRealBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::DReal
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get dReal version")?;

        let version = String::from_utf8_lossy(&output.stdout).to_string();
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await
            .with_context(|| format!("Failed to read dReal SMT-LIB file: {:?}", path))?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        // Reuse the Z3 SMT-LIB parser since dReal accepts SMT-LIB 2.0 format
        let mut parser = SmtParser::new(content);
        parser.parse()
    }

    /// dReal is a fully automated solver — interactive tactic application is
    /// not supported. Returns an error for all tactic types.
    async fn apply_tactic(&self, _state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        Ok(TacticResult::Error(format!(
            "dReal is a fully automated delta-complete SMT solver; \
             interactive tactic {:?} is not supported. \
             Use verify_proof() for automated checking.",
            tactic
        )))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Trivial cases: no goals or all goals are true
        if state.goals.is_empty() {
            return Ok(true);
        }
        if state.goals.iter().all(|g| matches!(&g.target, Term::Const(c) if c == "true")) {
            return Ok(true);
        }
        if state.goals.iter().any(|g| matches!(&g.target, Term::Const(c) if c == "false")) {
            return Ok(false);
        }

        // Build the negation query and run dReal
        let query = self.build_verification_query(state);
        let result = self.execute_command(&query).await?;

        match result {
            // Negation is unsatisfiable → goals are valid
            DRealResult::Unsat => Ok(true),

            // Negation is delta-satisfiable → goals may be invalid
            // (delta-sat means a counterexample exists within delta-perturbation)
            DRealResult::DeltaSat(_) => Ok(false),

            // Solver could not determine → conservatively report unverified
            DRealResult::Unknown => Ok(false),

            DRealResult::Error(e) => bail!("dReal verification error: {}", e),
            DRealResult::Output(_) => Ok(false),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        output.push_str("; ECHIDNA dReal Export\n");
        output.push_str("; Generated SMT-LIB 2.0 file for delta-complete decision procedures\n");
        output.push_str(&format!("; Precision (delta): {}\n\n", self.precision));
        output.push_str("(set-logic QF_NRA)\n\n");

        // Variable declarations
        for var in &state.context.variables {
            let ty_smt = self.term_to_smt(&var.ty);
            output.push_str(&format!("(declare-fun {} () {})\n", var.name, ty_smt));
        }

        output.push('\n');

        // Theorem assertions
        for theorem in &state.context.theorems {
            let stmt_smt = self.term_to_smt(&theorem.statement);
            output.push_str(&format!("; Theorem: {}\n", theorem.name));
            output.push_str(&format!("(assert {})\n\n", stmt_smt));
        }

        // Goal assertions
        for goal in &state.goals {
            output.push_str(&format!("; Goal: {}\n", goal.id));
            let goal_smt = self.term_to_smt(&goal.target);
            output.push_str(&format!("(assert {})\n\n", goal_smt));
        }

        output.push_str("(check-sat)\n");

        Ok(output)
    }

    /// Suggest automated strategies for dReal
    ///
    /// Since dReal is fully automated, suggestions are limited to
    /// precision-adjustment custom commands rather than interactive tactics.
    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        if !self.config.neural_enabled {
            return Ok(vec![]);
        }

        // dReal does not support interactive tactics, but we can suggest
        // precision adjustments and solver options as custom commands
        let mut suggestions = vec![
            Tactic::Custom {
                prover: "dreal".to_string(),
                command: "set-precision".to_string(),
                args: vec!["0.0001".to_string()],
            },
            Tactic::Custom {
                prover: "dreal".to_string(),
                command: "set-precision".to_string(),
                args: vec!["0.01".to_string()],
            },
            Tactic::Custom {
                prover: "dreal".to_string(),
                command: "enable-polytope".to_string(),
                args: vec![],
            },
        ];

        suggestions.truncate(limit);
        Ok(suggestions)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // dReal has no theorem library; it is a decision procedure
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
    use std::collections::HashMap;
    use crate::core::{Goal, Context as ProofContext};

    /// Verify that the default precision is set correctly
    #[test]
    fn test_default_precision() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::new(config);
        assert!((backend.precision() - DEFAULT_PRECISION).abs() < f64::EPSILON);
    }

    /// Verify custom precision construction
    #[test]
    fn test_custom_precision() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::with_precision(config, 0.01);
        assert!((backend.precision() - 0.01).abs() < f64::EPSILON);
    }

    /// Verify that zero precision panics
    #[test]
    #[should_panic(expected = "positive finite number")]
    fn test_zero_precision_panics() {
        let config = ProverConfig::default();
        DRealBackend::with_precision(config, 0.0);
    }

    /// Verify that negative precision panics
    #[test]
    #[should_panic(expected = "positive finite number")]
    fn test_negative_precision_panics() {
        let config = ProverConfig::default();
        DRealBackend::with_precision(config, -0.001);
    }

    /// Verify parsing of dReal "unsat" output
    #[test]
    fn test_parse_unsat() {
        let config = ProverConfig::default();
        let backend = DRealBackend::new(config);
        let result = backend.parse_dreal_result("unsat").unwrap();
        assert!(matches!(result, DRealResult::Unsat));
    }

    /// Verify parsing of dReal "delta-sat" output with delta value
    #[test]
    fn test_parse_delta_sat() {
        let config = ProverConfig::default();
        let backend = DRealBackend::new(config);
        let result = backend
            .parse_dreal_result("delta-sat with delta = 0.001")
            .unwrap();
        match result {
            DRealResult::DeltaSat(delta) => {
                assert!((delta - 0.001).abs() < f64::EPSILON);
            }
            other => panic!("Expected DeltaSat, got {:?}", other),
        }
    }

    /// Verify parsing of dReal "unknown" output
    #[test]
    fn test_parse_unknown() {
        let config = ProverConfig::default();
        let backend = DRealBackend::new(config);
        let result = backend.parse_dreal_result("unknown").unwrap();
        assert!(matches!(result, DRealResult::Unknown));
    }

    /// Verify parsing of error output
    #[test]
    fn test_parse_error() {
        let config = ProverConfig::default();
        let backend = DRealBackend::new(config);
        let result = backend
            .parse_dreal_result("(error \"invalid logic\")")
            .unwrap();
        match result {
            DRealResult::Error(msg) => assert!(msg.contains("invalid logic")),
            other => panic!("Expected Error, got {:?}", other),
        }
    }

    /// Verify that delta extraction works with various formats
    #[test]
    fn test_extract_delta_value() {
        let config = ProverConfig::default();
        let backend = DRealBackend::new(config);

        // Standard format
        let delta = backend.extract_delta_value("delta-sat with delta = 0.005");
        assert!((delta - 0.005).abs() < f64::EPSILON);

        // Fallback when no "delta =" present
        let delta = backend.extract_delta_value("delta-sat");
        assert!((delta - DEFAULT_PRECISION).abs() < f64::EPSILON);
    }

    /// Verify the prover kind
    #[test]
    fn test_prover_kind() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::DReal);
    }

    /// Verify that apply_tactic returns an error (dReal is automated)
    #[tokio::test]
    async fn test_apply_tactic_returns_error() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::new(config);
        let state = ProofState {
            goals: vec![],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        let result = backend.apply_tactic(&state, &Tactic::Simplify).await.unwrap();
        match result {
            TacticResult::Error(msg) => {
                assert!(msg.contains("fully automated"));
                assert!(msg.contains("not supported"));
            }
            other => panic!("Expected Error, got {:?}", other),
        }
    }

    /// Verify that empty goals verify as true
    #[tokio::test]
    async fn test_verify_empty_goals() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::new(config);
        let state = ProofState {
            goals: vec![],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        let verified = backend.verify_proof(&state).await.unwrap();
        assert!(verified);
    }

    /// Verify that export produces valid SMT-LIB 2.0 with QF_NRA logic
    #[tokio::test]
    async fn test_export_format() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };
        let backend = DRealBackend::new(config);
        let state = ProofState {
            goals: vec![Goal {
                id: "g0".to_string(),
                target: Term::App {
                    func: Box::new(Term::Const(">".to_string())),
                    args: vec![
                        Term::Var("x".to_string()),
                        Term::Const("0".to_string()),
                    ],
                },
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        let exported = backend.export(&state).await.unwrap();
        assert!(exported.contains("(set-logic QF_NRA)"));
        assert!(exported.contains("ECHIDNA dReal Export"));
        assert!(exported.contains("(check-sat)"));
        assert!(exported.contains("delta"));
    }

    /// Verify dReal version detection (only runs if dReal is installed)
    #[tokio::test]
    async fn test_dreal_backend_version() {
        let config = ProverConfig {
            executable: PathBuf::from("dreal"),
            ..Default::default()
        };

        let backend = DRealBackend::new(config);

        if let Ok(version) = backend.version().await {
            assert!(!version.is_empty());
        }
        // If dReal is not installed, this test silently passes
    }
}
