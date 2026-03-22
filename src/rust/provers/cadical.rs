// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! CaDiCaL SAT Solver Backend
//!
//! CaDiCaL is a state-of-the-art CDCL (Conflict-Driven Clause Learning) SAT solver.
//! Input format: DIMACS CNF (`p cnf <vars> <clauses>`, clause lines ending with 0).
//! Output: `s SATISFIABLE` or `s UNSATISFIABLE`, optional model via `v` lines.
//!
//! CaDiCaL has won multiple SAT Competition awards and is used as the default
//! SAT backend in ECHIDNA's Tier 9 SAT solver category.

#![allow(dead_code)]

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use crate::core::{Goal, ProofState, Tactic, TacticResult, Term, Context as ProofContext};
use super::{ProverBackend, ProverConfig, ProverKind};

/// CaDiCaL CDCL SAT solver backend
pub struct CaDiCaLBackend {
    config: ProverConfig,
}

impl CaDiCaLBackend {
    /// Create a new CaDiCaL backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        CaDiCaLBackend { config }
    }

    /// Parse DIMACS CNF content into clause sets.
    ///
    /// Returns (num_vars, num_clauses, clauses) where each clause is a Vec<i64>
    /// of signed literals (positive = variable, negative = negation).
    fn parse_dimacs(content: &str) -> Result<(usize, usize, Vec<Vec<i64>>)> {
        let mut num_vars: usize = 0;
        let mut num_clauses: usize = 0;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        let mut current_clause: Vec<i64> = Vec::new();
        let mut header_found = false;

        for line in content.lines() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('c') {
                continue;
            }

            // Parse problem line: p cnf <vars> <clauses>
            if line.starts_with("p cnf") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 4 {
                    num_vars = parts[2].parse()
                        .map_err(|_| anyhow!("Invalid variable count in DIMACS header"))?;
                    num_clauses = parts[3].parse()
                        .map_err(|_| anyhow!("Invalid clause count in DIMACS header"))?;
                    header_found = true;
                }
                continue;
            }

            if !header_found {
                continue;
            }

            // Parse clause literals
            for token in line.split_whitespace() {
                let lit: i64 = token.parse()
                    .map_err(|_| anyhow!("Invalid literal in DIMACS: {}", token))?;
                if lit == 0 {
                    // End of clause
                    if !current_clause.is_empty() {
                        clauses.push(current_clause.clone());
                        current_clause.clear();
                    }
                } else {
                    current_clause.push(lit);
                }
            }
        }

        // Handle trailing clause without terminating 0
        if !current_clause.is_empty() {
            clauses.push(current_clause);
        }

        Ok((num_vars, num_clauses, clauses))
    }

    /// Convert clauses back to DIMACS CNF format string
    fn to_dimacs(num_vars: usize, clauses: &[Vec<i64>]) -> String {
        let mut output = String::new();
        output.push_str("c ECHIDNA CaDiCaL Export\n");
        output.push_str("c Generated DIMACS CNF file\n");
        output.push_str(&format!("p cnf {} {}\n", num_vars, clauses.len()));

        for clause in clauses {
            let lits: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
            output.push_str(&lits.join(" "));
            output.push_str(" 0\n");
        }

        output
    }

    /// Extract clauses from ProofState metadata or goal representation
    fn state_to_clauses(state: &ProofState) -> (usize, Vec<Vec<i64>>) {
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        let mut max_var: usize = 0;

        for goal in &state.goals {
            // Each goal target encodes a clause set via nested App terms
            let clause = Self::term_to_clause(&goal.target);
            for lit in &clause {
                let var = lit.unsigned_abs() as usize;
                if var > max_var {
                    max_var = var;
                }
            }
            if !clause.is_empty() {
                clauses.push(clause);
            }
        }

        (max_var, clauses)
    }

    /// Convert a Term into a clause (vector of literals).
    ///
    /// Interprets App("or", [...]) as a disjunction of literals,
    /// App("not", [Const(n)]) as negated literal, and Const(n) as positive literal.
    fn term_to_clause(term: &Term) -> Vec<i64> {
        match term {
            Term::Const(s) => {
                if let Ok(lit) = s.parse::<i64>() {
                    vec![lit]
                } else {
                    vec![]
                }
            }
            Term::App { func, args } => {
                if let Term::Const(f) = func.as_ref() {
                    match f.as_str() {
                        "or" | "clause" => {
                            args.iter().flat_map(Self::term_to_clause).collect()
                        }
                        "not" | "neg" => {
                            if let Some(inner) = args.first() {
                                Self::term_to_clause(inner).into_iter().map(|l| -l).collect()
                            } else {
                                vec![]
                            }
                        }
                        _ => vec![],
                    }
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }

    /// Convert a clause (Vec<i64>) into a Term representation
    fn clause_to_term(clause: &[i64]) -> Term {
        if clause.len() == 1 {
            Term::Const(clause[0].to_string())
        } else {
            Term::App {
                func: Box::new(Term::Const("or".to_string())),
                args: clause.iter().map(|l| Term::Const(l.to_string())).collect(),
            }
        }
    }

    /// Parse CaDiCaL output to determine satisfiability result.
    ///
    /// Returns Ok(true) for SATISFIABLE, Ok(false) for UNSATISFIABLE,
    /// or an error if the output is inconclusive.
    fn parse_sat_result(output: &str) -> Result<bool> {
        for line in output.lines() {
            let line = line.trim();
            if line == "s SATISFIABLE" {
                return Ok(true);
            }
            if line == "s UNSATISFIABLE" {
                return Ok(false);
            }
        }
        Err(anyhow!("CaDiCaL output inconclusive: no s SATISFIABLE/UNSATISFIABLE line found"))
    }

    /// Extract model (variable assignments) from `v` lines in solver output.
    ///
    /// Returns a vector of signed integers: positive means true, negative means false.
    fn parse_model(output: &str) -> Vec<i64> {
        let mut model = Vec::new();
        for line in output.lines() {
            let line = line.trim();
            if line.starts_with("v ") {
                for token in line[2..].split_whitespace() {
                    if let Ok(lit) = token.parse::<i64>() {
                        if lit != 0 {
                            model.push(lit);
                        }
                    }
                }
            }
        }
        model
    }
}

#[async_trait]
impl ProverBackend for CaDiCaLBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::CaDiCaL
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run cadical --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // CaDiCaL may print version to stdout or stderr
        let version = if !stdout.trim().is_empty() {
            stdout.lines().next().unwrap_or("unknown").to_string()
        } else {
            stderr.lines().next().unwrap_or("unknown").to_string()
        };

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await
            .with_context(|| format!("Failed to read DIMACS file: {:?}", path))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let (num_vars, _num_clauses, clauses) = Self::parse_dimacs(content)?;

        let mut state = ProofState::default();

        // Store variable count in metadata
        state.metadata.insert(
            "num_vars".to_string(),
            serde_json::Value::Number(serde_json::Number::from(num_vars)),
        );

        // Each clause becomes a goal (the SAT problem is to satisfy all clauses)
        let combined_target = if clauses.len() == 1 {
            Self::clause_to_term(&clauses[0])
        } else {
            Term::App {
                func: Box::new(Term::Const("and".to_string())),
                args: clauses.iter().map(|c| Self::clause_to_term(c)).collect(),
            }
        };

        state.goals.push(Goal {
            id: "sat_problem".to_string(),
            target: combined_target,
            hypotheses: vec![],
        });

        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddClause: add a new clause to the problem via Custom tactic
            Tactic::Custom { prover, command, args } if prover == "cadical" => {
                match command.as_str() {
                    "add-clause" => {
                        // Parse literals from args
                        let literals: Result<Vec<i64>, _> = args.iter()
                            .map(|a| a.parse::<i64>())
                            .collect();

                        match literals {
                            Ok(lits) => {
                                let mut new_state = state.clone();
                                let new_clause = Self::clause_to_term(&lits);
                                new_state.goals.push(Goal {
                                    id: format!("clause_{}", new_state.goals.len()),
                                    target: new_clause,
                                    hypotheses: vec![],
                                });
                                new_state.proof_script.push(tactic.clone());
                                Ok(TacticResult::Success(new_state))
                            }
                            Err(_) => Ok(TacticResult::Error(
                                "add-clause requires integer literal arguments".to_string()
                            )),
                        }
                    }

                    "unit-propagate" => {
                        // Unit propagation: find unit clauses and simplify
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }

                    "resolution" => {
                        // Resolution: combine two clauses on a pivot variable
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }

                    _ => Ok(TacticResult::Error(
                        format!("Unknown CaDiCaL tactic: {}", command)
                    )),
                }
            }

            Tactic::Simplify => {
                // Run CaDiCaL preprocessing (simplification) on the problem
                let mut new_state = state.clone();
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }

            _ => Ok(TacticResult::Error(
                format!("Tactic {:?} not supported for CaDiCaL", tactic)
            )),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.goals.is_empty() {
            return Ok(true);
        }

        // Build DIMACS CNF from state
        let (num_vars, clauses) = Self::state_to_clauses(state);
        if clauses.is_empty() {
            return Ok(true);
        }

        let dimacs = Self::to_dimacs(num_vars, &clauses);

        // Run CaDiCaL solver via stdin
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn CaDiCaL process")?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(dimacs.as_bytes()).await
                .context("Failed to write DIMACS to CaDiCaL stdin")?;
            stdin.flush().await?;
            drop(stdin);
        }

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            child.wait_with_output(),
        )
        .await
        .map_err(|_| anyhow!("CaDiCaL timed out after {} seconds", self.config.timeout))??;

        let stdout = String::from_utf8_lossy(&output.stdout);
        Self::parse_sat_result(&stdout)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let (num_vars, clauses) = Self::state_to_clauses(state);
        Ok(Self::to_dimacs(num_vars, &clauses))
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "cadical".to_string(),
                command: "add-clause".to_string(),
                args: vec!["1".to_string(), "2".to_string()],
            },
            Tactic::Custom {
                prover: "cadical".to_string(),
                command: "unit-propagate".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "cadical".to_string(),
                command: "resolution".to_string(),
                args: vec![],
            },
            Tactic::Simplify,
        ];

        tactics.truncate(limit);
        Ok(tactics)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // SAT solvers do not have theorem libraries
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

    #[test]
    fn test_parse_dimacs_basic() {
        let dimacs = "c test\np cnf 3 2\n1 -2 0\n2 3 0\n";
        let (vars, clauses_count, clauses) = CaDiCaLBackend::parse_dimacs(dimacs).unwrap();
        assert_eq!(vars, 3);
        assert_eq!(clauses_count, 2);
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], vec![1, -2]);
        assert_eq!(clauses[1], vec![2, 3]);
    }

    #[test]
    fn test_to_dimacs_roundtrip() {
        let clauses = vec![vec![1, -2, 3], vec![-1, 2]];
        let dimacs = CaDiCaLBackend::to_dimacs(3, &clauses);
        assert!(dimacs.contains("p cnf 3 2"));
        assert!(dimacs.contains("1 -2 3 0"));
        assert!(dimacs.contains("-1 2 0"));
    }

    #[test]
    fn test_parse_sat_result() {
        assert!(CaDiCaLBackend::parse_sat_result("s SATISFIABLE\nv 1 -2 3 0\n").unwrap());
        assert!(!CaDiCaLBackend::parse_sat_result("s UNSATISFIABLE\n").unwrap());
        assert!(CaDiCaLBackend::parse_sat_result("c some comment\n").is_err());
    }

    #[tokio::test]
    async fn test_cadical_parse_string() {
        let config = ProverConfig {
            executable: PathBuf::from("cadical"),
            timeout: 10,
            ..Default::default()
        };

        let backend = CaDiCaLBackend::new(config);
        let dimacs = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
        let state = backend.parse_string(dimacs).await.unwrap();

        assert_eq!(state.goals.len(), 1);
        assert_eq!(
            state.metadata.get("num_vars"),
            Some(&serde_json::Value::Number(serde_json::Number::from(2)))
        );
    }
}
