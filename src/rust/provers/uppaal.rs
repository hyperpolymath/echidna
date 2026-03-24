// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! UPPAAL Timed Automata Model Checker Backend
//!
//! UPPAAL is a model checker for real-time systems modelled as networks
//! of timed automata. It verifies properties expressed in a subset of
//! TCTL (Timed Computation Tree Logic).
//!
//! Input format: UPPAAL XML models (.xml) with queries (.q).
//! Executable: `verifyta` (the command-line verification engine).
//!
//! Features:
//! - Timed automata modelling with clock variables
//! - TCTL property verification (A[], E<>, A<>, E[], -->)
//! - Clock guards and invariants
//! - Urgent/committed locations
//! - Integer variables and channels
//! - Broadcast and binary synchronisation

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// UPPAAL timed automata model checker backend
///
/// Integrates the UPPAAL verifyta engine for verifying real-time systems
/// modelled as networks of timed automata against TCTL properties.
pub struct UppaalBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl UppaalBackend {
    /// Create a new UPPAAL backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        UppaalBackend { config }
    }

    /// Convert proof state to UPPAAL XML model format
    ///
    /// Generates a minimal UPPAAL XML model from the ECHIDNA proof state.
    /// This produces a skeleton model; for full models, raw XML should
    /// be passed via axioms.
    fn to_uppaal_xml(&self, state: &ProofState) -> Result<String> {
        let mut xml = String::new();

        xml.push_str("<?xml version=\"1.0\" encoding=\"utf-8\"?>\n");
        xml.push_str("<!DOCTYPE nta PUBLIC '-//Uppaal Team//DTD Flat System 1.1//EN'\n");
        xml.push_str("  'http://www.it.uu.se/research/group/darts/uppaal/flat-1_2.dtd'>\n");
        xml.push_str("<!-- ECHIDNA UPPAAL Export -->\n");
        xml.push_str("<nta>\n");

        // Global declarations
        xml.push_str("  <declaration>\n");
        for def in &state.context.definitions {
            xml.push_str(&format!("    {}\n", def.name));
        }
        xml.push_str("  </declaration>\n");

        // Check if axioms contain raw XML template definitions
        let has_raw_xml = state
            .context
            .axioms
            .iter()
            .any(|a| a.contains("<template") || a.contains("<location"));

        if has_raw_xml {
            for axiom in &state.context.axioms {
                xml.push_str(axiom);
                xml.push('\n');
            }
        } else {
            // Generate a minimal template
            xml.push_str("  <template>\n");
            xml.push_str("    <name>Process</name>\n");
            xml.push_str("    <location id=\"id0\"><name>start</name></location>\n");
            xml.push_str("    <location id=\"id1\"><name>end</name></location>\n");
            xml.push_str("    <init ref=\"id0\"/>\n");

            // Add axioms as transitions
            for (i, axiom) in state.context.axioms.iter().enumerate() {
                xml.push_str(&format!(
                    "    <transition><source ref=\"id0\"/><target ref=\"id1\"/><label kind=\"guard\">{}</label></transition>\n",
                    axiom
                ));
                let _ = i; // Suppress unused warning
            }

            xml.push_str("  </template>\n");
        }

        // System declaration
        xml.push_str("  <system>system Process;</system>\n");

        // Queries (from goals)
        xml.push_str("  <queries>\n");
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            xml.push_str(&format!(
                "    <query><formula>{}</formula><comment>{}</comment></query>\n",
                target_str, goal.id
            ));
        }
        xml.push_str("  </queries>\n");

        xml.push_str("</nta>\n");

        Ok(xml)
    }

    /// Convert goals to UPPAAL query format for separate query file
    fn to_query_file(&self, state: &ProofState) -> String {
        let mut queries = String::new();
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);
            queries.push_str(&format!("{}\n", target_str));
        }
        queries
    }

    /// Parse verifyta verification output to determine success or failure
    ///
    /// verifyta outputs "-- Property is satisfied." or
    /// "-- Property is NOT satisfied." for each query.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let mut found_result = false;

        for line in output.lines() {
            let trimmed = line.trim();

            // Property satisfied
            if trimmed.contains("Property is satisfied")
                || trimmed.contains("-- Formula is satisfied")
            {
                found_result = true;
            }

            // Property not satisfied
            if trimmed.contains("Property is NOT satisfied")
                || trimmed.contains("NOT satisfied")
                || trimmed.contains("Formula is NOT satisfied")
            {
                return Ok(false);
            }

            // Syntax error or invalid model
            if trimmed.contains("syntax error") || trimmed.contains("Parse error") {
                return Err(anyhow!("UPPAAL error: {}", trimmed));
            }
        }

        if found_result {
            Ok(true)
        } else {
            Err(anyhow!(
                "UPPAAL inconclusive: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ))
        }
    }

    /// Parse UPPAAL XML model to extract templates, locations,
    /// transitions, and queries into the proof state
    fn parse_uppaal_xml(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        // Simple line-based parsing for XML elements
        // (full XML parsing would require an XML library)
        for line in content.lines() {
            let trimmed = line.trim();

            // Detect declarations
            if trimmed.starts_with("<declaration>")
                || trimmed.starts_with("clock ")
                || trimmed.starts_with("int ")
                || trimmed.starts_with("chan ")
            {
                state.context.definitions.push(Definition {
                    name: trimmed.to_string(),
                    ty: Term::Const("UPPAAL_DECL".to_string()),
                    body: Term::Const(trimmed.to_string()),
                });
            }

            // Detect template names
            if trimmed.starts_with("<name>") && trimmed.ends_with("</name>") {
                let name = trimmed
                    .trim_start_matches("<name>")
                    .trim_end_matches("</name>");
                state.context.axioms.push(format!("template: {}", name));
            }

            // Detect query formulae
            if trimmed.starts_with("<formula>") && trimmed.contains("</formula>") {
                let formula = trimmed
                    .trim_start_matches("<formula>")
                    .split("</formula>")
                    .next()
                    .unwrap_or("")
                    .trim();

                if !formula.is_empty() {
                    state.goals.push(Goal {
                        id: format!("query_{}", state.goals.len()),
                        target: Term::Const(formula.to_string()),
                        hypotheses: vec![],
                    });
                }
            }
        }

        Ok(state)
    }
}

#[async_trait]
impl ProverBackend for UppaalBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::UPPAAL
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-v")
            .output()
            .await
            .context("Failed to run verifyta -v")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("UPPAAL") || l.contains("verifyta") || l.contains("version"))
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(path)
            .await
            .context("Failed to read UPPAAL XML file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_uppaal_xml(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // AddQuery: add a TCTL query to verify
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "uppaal" && command == "add_query" => {
                let query_text = args.join(" ");
                let mut new_state = state.clone();
                new_state.goals.push(Goal {
                    id: format!("query_{}", new_state.goals.len()),
                    target: Term::Const(query_text),
                    hypotheses: vec![],
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddClock: add a clock variable declaration
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "uppaal" && command == "add_clock" => {
                let clock_name = args.first().cloned().unwrap_or_else(|| "x".to_string());
                let mut new_state = state.clone();
                new_state.context.definitions.push(Definition {
                    name: clock_name.clone(),
                    ty: Term::Const("clock".to_string()),
                    body: Term::Const(format!("clock {};", clock_name)),
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // AddChannel: add a synchronisation channel
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "uppaal" && command == "add_channel" => {
                let chan_name = args.first().cloned().unwrap_or_else(|| "sync".to_string());
                let mut new_state = state.clone();
                new_state.context.definitions.push(Definition {
                    name: chan_name.clone(),
                    ty: Term::Const("chan".to_string()),
                    body: Term::Const(format!("chan {};", chan_name)),
                });
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for UPPAAL model checker",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let xml_code = self.to_uppaal_xml(state)?;
        let query_code = self.to_query_file(state);

        // Write model and queries to temporary files
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for UPPAAL")?;
        let xml_file = tmp_dir.path().join("model.xml");
        let query_file = tmp_dir.path().join("queries.q");

        tokio::fs::write(&xml_file, &xml_code)
            .await
            .context("Failed to write temporary UPPAAL XML file")?;
        tokio::fs::write(&query_file, &query_code)
            .await
            .context("Failed to write temporary UPPAAL query file")?;

        // Run verifyta on the model with queries
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg(&xml_file)
                .arg(&query_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("UPPAAL timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute verifyta")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_uppaal_xml(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom {
                prover: "uppaal".to_string(),
                command: "add_query".to_string(),
                args: vec!["A[] not deadlock".to_string()],
            },
            Tactic::Custom {
                prover: "uppaal".to_string(),
                command: "add_clock".to_string(),
                args: vec!["timer".to_string()],
            },
            Tactic::Custom {
                prover: "uppaal".to_string(),
                command: "add_channel".to_string(),
                args: vec!["sync".to_string()],
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
    async fn test_uppaal_xml_export() {
        let config = ProverConfig {
            executable: PathBuf::from("verifyta"),
            timeout: 30,
            ..Default::default()
        };

        let backend = UppaalBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "no_deadlock".to_string(),
            target: Term::Const("A[] not deadlock".to_string()),
            hypotheses: vec![],
        });

        let xml = backend.to_uppaal_xml(&state).unwrap();

        assert!(xml.contains("ECHIDNA UPPAAL Export"));
        assert!(xml.contains("<nta>"));
        assert!(xml.contains("A[] not deadlock"));
        assert!(xml.contains("</nta>"));
    }

    #[tokio::test]
    async fn test_uppaal_parse_xml() {
        let config = ProverConfig {
            executable: PathBuf::from("verifyta"),
            timeout: 30,
            ..Default::default()
        };

        let backend = UppaalBackend::new(config);

        let xml = r#"
<nta>
  <declaration>clock x; int count = 0;</declaration>
  <template>
    <name>Process</name>
    <location id="id0"><name>idle</name></location>
  </template>
  <queries>
    <formula>A[] not deadlock</formula>
    <formula>E<> Process.idle</formula>
  </queries>
</nta>
"#;

        let state = backend.parse_string(xml).await.unwrap();

        assert!(
            !state.context.definitions.is_empty(),
            "Should have parsed declarations"
        );
        assert_eq!(state.goals.len(), 2, "Should have parsed two queries");
    }

    #[test]
    fn test_uppaal_parse_result_success() {
        let config = ProverConfig {
            executable: PathBuf::from("verifyta"),
            timeout: 30,
            ..Default::default()
        };

        let backend = UppaalBackend::new(config);

        let success = "Verifying formula 1 at line 1.\n -- Property is satisfied.\n";
        assert!(backend.parse_result(success).unwrap());
    }

    #[test]
    fn test_uppaal_parse_result_failure() {
        let config = ProverConfig {
            executable: PathBuf::from("verifyta"),
            timeout: 30,
            ..Default::default()
        };

        let backend = UppaalBackend::new(config);

        let failure = "Verifying formula 1 at line 1.\n -- Property is NOT satisfied.\n";
        assert!(!backend.parse_result(failure).unwrap());
    }

    #[test]
    fn test_uppaal_parse_result_syntax_error() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);

        let output = "syntax error at line 3\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_uppaal_parse_result_inconclusive() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);

        let output = "no property output\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[test]
    fn test_uppaal_kind() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::UPPAAL);
    }

    #[test]
    fn test_uppaal_query_file_generation() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "q1".to_string(),
            target: Term::Const("A[] not deadlock".to_string()),
            hypotheses: vec![],
        });
        state.goals.push(Goal {
            id: "q2".to_string(),
            target: Term::Const("E<> Process.done".to_string()),
            hypotheses: vec![],
        });

        let queries = backend.to_query_file(&state);
        assert!(queries.contains("A[] not deadlock"));
        assert!(queries.contains("E<> Process.done"));
    }

    #[tokio::test]
    async fn test_uppaal_suggest_tactics() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 3).await.unwrap();
        assert_eq!(tactics.len(), 3);
    }

    #[tokio::test]
    async fn test_uppaal_parse_empty_xml() {
        let config = ProverConfig::default();
        let backend = UppaalBackend::new(config);

        let state = backend.parse_string("").await.unwrap();
        assert!(state.goals.is_empty());
    }
}
