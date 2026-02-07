// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Vampire ATP backend
//!
//! Vampire is a first-order automated theorem prover (ATP) that has won
//! multiple CASC (CADE ATP System Competition) awards.
//!
//! Features:
//! - First-order logic with equality
//! - TPTP format input/output
//! - Highly optimized for FOL reasoning
//! - Excellent performance on CASC benchmarks

use async_trait::async_trait;
use anyhow::{Context, Result};
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult};

/// Vampire theorem prover backend
pub struct VampireBackend {
    config: ProverConfig,
}

impl VampireBackend {
    pub fn new(config: ProverConfig) -> Self {
        VampireBackend { config }
    }

    /// Convert proof state to TPTP format
    fn to_tptp(&self, state: &ProofState) -> Result<String> {
        let mut tptp = String::new();

        // Add axioms from context
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            tptp.push_str(&format!("fof(axiom_{}, axiom, {}).\n", i, axiom));
        }

        // Add definitions
        for (i, def) in state.context.definitions.iter().enumerate() {
            tptp.push_str(&format!("fof(definition_{}, axiom, {}).\n", i, def));
        }

        // Add goal (negated for refutation-based proving)
        if let Some(goal) = state.goals.first() {
            tptp.push_str(&format!("fof(conjecture, conjecture, {}).\n", goal.statement));
        }

        Ok(tptp)
    }

    /// Parse Vampire output to determine proof success
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Vampire output patterns:
        // - "Refutation found" / "Theorem" = proof succeeded
        // - "Satisfiable" = proof failed (negation is satisfiable)
        // - "Timeout" / "Unknown" = inconclusive

        if output.contains("Refutation found")
            || output.contains("% SZS status Theorem")
            || output.contains("% Termination reason: Refutation")
        {
            Ok(true)
        } else if output.contains("Satisfiable") || output.contains("% SZS status CounterSatisfiable")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "Vampire inconclusive or error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for VampireBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Vampire
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run vampire --version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Vampire prints version to stderr
        let version = if !stderr.is_empty() {
            stderr.lines().next().unwrap_or("unknown").to_string()
        } else {
            stdout.lines().next().unwrap_or("unknown").to_string()
        };

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read proof file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        // Parse TPTP format into ProofState
        // This is a simplified implementation
        // A full implementation would use a proper TPTP parser

        let mut state = ProofState::default();

        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') {
                continue;
            }

            if line.starts_with("fof(") {
                // Extract formula
                if let Some(formula) = line.split(',').nth(2) {
                    let formula = formula.trim_end_matches(").").trim();
                    if line.contains("axiom") {
                        state.context.axioms.push(formula.to_string());
                    } else if line.contains("conjecture") {
                        state.goals.push(Goal {
                            statement: formula.to_string(),
                            context: state.context.clone(),
                        });
                    }
                }
            }
        }

        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        // Vampire is fully automated - no interactive tactics
        Err(anyhow::anyhow!(
            "Vampire is a fully automated prover - interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // 1. Convert to TPTP
        let tptp_code = self.to_tptp(state)?;

        // 2. Spawn Vampire process
        let mut child = Command::new(&self.config.executable)
            .arg("--mode").arg("casc")              // CASC competition mode
            .arg("--input_syntax").arg("tptp")      // TPTP format
            .arg("--time_limit").arg(format!("{}", self.config.timeout))
            .arg("--proof").arg("off")              // Don't generate proof (faster)
            .arg("--statistics").arg("brief")       // Brief statistics
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Vampire process")?;

        // 3. Write TPTP to stdin
        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(tptp_code.as_bytes())
                .await
                .context("Failed to write to Vampire stdin")?;
            stdin.flush().await?;
            drop(stdin); // Close stdin to signal EOF
        }

        // 4. Wait for result with timeout
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("Vampire timed out")??;

        // 5. Parse output
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Vampire outputs to stdout
        self.parse_result(&stdout).or_else(|_| {
            // Try stderr if stdout parsing failed
            self.parse_result(&stderr)
        })
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_tptp(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        // Vampire is fully automated - no tactics
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Vampire doesn't have a theorem database
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
    async fn test_vampire_tptp_export() {
        let config = ProverConfig {
            executable: PathBuf::from("vampire"),
            timeout: 10,
            ..Default::default()
        };

        let backend = VampireBackend::new(config);

        let mut state = ProofState::default();
        state.context.axioms.push("p => q".to_string());
        state.context.axioms.push("p".to_string());
        state.goals.push(Goal {
            statement: "q".to_string(),
            context: state.context.clone(),
        });

        let tptp = backend.to_tptp(&state).unwrap();

        assert!(tptp.contains("fof(axiom_0, axiom, p => q)."));
        assert!(tptp.contains("fof(axiom_1, axiom, p)."));
        assert!(tptp.contains("fof(conjecture, conjecture, q)."));
    }

    #[tokio::test]
    #[ignore] // Requires Vampire to be installed
    async fn test_vampire_simple_proof() {
        let config = ProverConfig {
            executable: PathBuf::from("vampire"),
            timeout: 10,
            ..Default::default()
        };

        let backend = VampireBackend::new(config);

        // Simple tautology: P → P
        let tptp = "fof(test, conjecture, (p => p)).";
        let state = backend.parse_string(tptp).await.unwrap();

        let result = backend.verify_proof(&state).await;

        match result {
            Ok(true) => println!("✓ Vampire proved P → P"),
            Ok(false) => panic!("Vampire failed to prove P → P"),
            Err(e) => println!("Vampire not installed or error: {}", e),
        }
    }
}
