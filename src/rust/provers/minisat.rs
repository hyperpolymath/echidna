// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! MiniSat Classic DPLL SAT Solver Backend
//!
//! MiniSat is a minimalistic, open-source SAT solver based on the DPLL
//! algorithm with conflict-driven clause learning (CDCL). It is widely
//! used as a reference implementation and embedded SAT engine.
//!
//! Input format: DIMACS CNF (`p cnf <vars> <clauses>`, clause lines ending with 0).
//! Output: `SATISFIABLE` or `UNSATISFIABLE`, optional model on a second line.
//!
//! MiniSat is ECHIDNA's lightweight SAT backend in the Tier 9 SAT solver
//! category, suitable for smaller instances and rapid prototyping.

#![allow(dead_code)]

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use crate::core::{Goal, ProofState, Tactic, TacticResult, Term, Context as ProofContext};
use super::{ProverBackend, ProverConfig, ProverKind};

/// MiniSat DPLL/CDCL SAT solver backend
pub struct MiniSatBackend {
    config: ProverConfig,
}

impl MiniSatBackend {
    /// Create a new MiniSat backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        MiniSatBackend { config }
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
        output.push_str("c ECHIDNA MiniSat Export\n");
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

    /// Parse MiniSat output to determine satisfiability result.
    ///
    /// MiniSat outputs "SATISFIABLE" or "UNSATISFIABLE" (without "s " prefix,
    /// unlike CaDiCaL/Kissat). Returns Ok(true) for SAT, Ok(false) for UNSAT.
    fn parse_sat_result(output: &str) -> Result<bool> {
        for line in output.lines() {
            let line = line.trim();
            if line == "SATISFIABLE" || line == "s SATISFIABLE" {
                return Ok(true);
            }
            if line == "UNSATISFIABLE" || line == "s UNSATISFIABLE" {
                return Ok(false);
            }
        }
        Err(anyhow!("MiniSat output inconclusive: no SATISFIABLE/UNSATISFIABLE line found"))
    }

    /// Extract model (variable assignments) from MiniSat output.
    ///
    /// MiniSat outputs the model on the line following "SATISFIABLE",
    /// or via `v` lines. Returns signed integers (positive=true, negative=false).
    fn parse_model(output: &str) -> Vec<i64> {
        let mut model = Vec::new();
        let mut found_sat = false;

        for line in output.lines() {
            let line = line.trim();

            // MiniSat: model follows SATISFIABLE on the next line
            if line == "SATISFIABLE" || line == "s SATISFIABLE" {
                found_sat = true;
                continue;
            }

            // Parse model line (either v-prefixed or bare assignments)
            if found_sat || line.starts_with("v ") {
                let data = if line.starts_with("v ") { &line[2..] } else { line };
                for token in data.split_whitespace() {
                    if let Ok(lit) = token.parse::<i64>() {
                        if lit != 0 {
                            model.push(lit);
                        }
                    }
                }
                if found_sat && !line.starts_with("v ") {
                    found_sat = false; // Only parse one line after SATISFIABLE
                }
            }
        }
        model
    }
}

#[async_trait]
impl ProverBackend for MiniSatBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::MiniSat
    }

    async fn version(&self) -> Result<String> {
        // MiniSat prints version when invoked with --help or no arguments
        let output = Command::new(&self.config.executable)
            .arg("--help")
            .output()
            .await
            .context("Failed to run minisat --help")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("MiniSat") || l.contains("minisat") || l.contains("version"))
            .unwrap_or("unknown")
            .to_string();

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

        // Combine all clauses into a single conjunction goal
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
            Tactic::Custom { prover, command, args } if prover == "minisat" => {
                match command.as_str() {
                    "add-clause" => {
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
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }

                    "resolution" => {
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }

                    _ => Ok(TacticResult::Error(
                        format!("Unknown MiniSat tactic: {}", command)
                    )),
                }
            }

            Tactic::Simplify => {
                let mut new_state = state.clone();
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }

            _ => Ok(TacticResult::Error(
                format!("Tactic {:?} not supported for MiniSat", tactic)
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

        // Write to temporary file (MiniSat typically takes file arguments)
        let tmp_dir = tempfile::tempdir()
            .context("Failed to create temporary directory for MiniSat")?;
        let input_file = tmp_dir.path().join("input.cnf");
        let output_file = tmp_dir.path().join("output.txt");

        tokio::fs::write(&input_file, &dimacs)
            .await
            .context("Failed to write temporary DIMACS file")?;

        // Run MiniSat: minisat <input> <output>
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&input_file)
                .arg(&output_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("MiniSat timed out after {} seconds", self.config.timeout))?
        .context("Failed to spawn MiniSat process")?;

        // MiniSat writes result to stdout and optionally to the output file
        let stdout = String::from_utf8_lossy(&output.stdout);

        // Try output file first, then stdout
        let result_text = if let Ok(file_content) = tokio::fs::read_to_string(&output_file).await {
            file_content
        } else {
            stdout.to_string()
        };

        Self::parse_sat_result(&result_text)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let (num_vars, clauses) = Self::state_to_clauses(state);
        Ok(Self::to_dimacs(num_vars, &clauses))
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "minisat".to_string(),
                command: "add-clause".to_string(),
                args: vec!["1".to_string(), "2".to_string()],
            },
            Tactic::Custom {
                prover: "minisat".to_string(),
                command: "unit-propagate".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "minisat".to_string(),
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
        let dimacs = "c test\np cnf 3 2\n1 -3 0\n2 3 0\n";
        let (vars, clauses_count, clauses) = MiniSatBackend::parse_dimacs(dimacs).unwrap();
        assert_eq!(vars, 3);
        assert_eq!(clauses_count, 2);
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], vec![1, -3]);
        assert_eq!(clauses[1], vec![2, 3]);
    }

    #[test]
    fn test_to_dimacs_roundtrip() {
        let clauses = vec![vec![1, -2, 3], vec![-1, 2]];
        let dimacs = MiniSatBackend::to_dimacs(3, &clauses);
        assert!(dimacs.contains("p cnf 3 2"));
        assert!(dimacs.contains("1 -2 3 0"));
        assert!(dimacs.contains("-1 2 0"));
    }

    #[test]
    fn test_parse_sat_result() {
        assert!(MiniSatBackend::parse_sat_result("SATISFIABLE\n1 -2 3 0\n").unwrap());
        assert!(!MiniSatBackend::parse_sat_result("UNSATISFIABLE\n").unwrap());
        assert!(MiniSatBackend::parse_sat_result("c solving...\n").is_err());
    }

    #[test]
    fn test_parse_model() {
        let output = "SATISFIABLE\n1 -2 3 0\n";
        let model = MiniSatBackend::parse_model(output);
        assert_eq!(model, vec![1, -2, 3]);
    }

    #[tokio::test]
    async fn test_minisat_parse_string() {
        let config = ProverConfig {
            executable: PathBuf::from("minisat"),
            timeout: 10,
            ..Default::default()
        };

        let backend = MiniSatBackend::new(config);
        let dimacs = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
        let state = backend.parse_string(dimacs).await.unwrap();

        assert_eq!(state.goals.len(), 1);
        assert_eq!(
            state.metadata.get("num_vars"),
            Some(&serde_json::Value::Number(serde_json::Number::from(2)))
        );
    }
}
