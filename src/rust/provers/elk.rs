// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ELK backend — high-performance reasoner for the OWL 2 EL profile.
//!
//! ELK is the canonical reasoner for **OWL 2 EL**, a tractable
//! description-logic profile in widespread use for biomedical
//! ontologies (SNOMED CT, GO, FMA, NCIt) where standard tableau
//! reasoners run out of memory or time.  It implements a
//! consequence-based classification algorithm and is one of the few
//! reasoners that can classify SNOMED CT in seconds.
//!
//! ## Why this backend exists
//!
//! ECHIDNA already covers SROIQ via Konclude, but biomedical-style
//! workloads (millions of EL axioms) collapse Konclude's memory
//! profile.  ELK's specialisation gives ECHIDNA an orthogonal
//! capability: ontologies sized in the millions of axioms become
//! tractable.
//!
//! ## Input format
//!
//! OWL 2 EL ontologies in OWL Functional Syntax (`.ofn`), Manchester
//! Syntax (`.omn`), or RDF/XML (`.owl`, `.rdf`, `.ttl`).  ELK ingests
//! the file directly via its CLI.
//!
//! ## CLI invocation
//!
//! `elk -i <ontology> --classify` (Java JAR or wrapper script).
//! Inconsistency check via `--check-consistency`; entailment via
//! `--entail <axiom-file>`.
//!
//! ## Output parsing
//!
//! ELK emits structured stdout with markers:
//!
//! - `OWL ontology is consistent` / `inconsistent`
//! - `Entailment: TRUE` / `FALSE`
//! - `Classification finished`
//!
//! See `parse_result` for the full classifier.
//!
//! ## Integration tier
//!
//! Tier-5h / Phase-4.  Trust tier 3 (small consequence-based kernel,
//! peer-reviewed soundness proofs).  Complexity 3.

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// ELK backend for OWL 2 EL reasoning.
pub struct ElkBackend {
    config: ProverConfig,
}

impl ElkBackend {
    pub fn new(config: ProverConfig) -> Self {
        ElkBackend { config }
    }

    /// Render a `ProofState` into an OWL Functional Syntax ontology.
    ///
    /// Each axiom is wrapped as a top-level OFN axiom; the goal is
    /// emitted as the entailment to be checked.  Callers are expected
    /// to provide axioms already in OFN line form (e.g.
    /// `SubClassOf(:A :B)`) — we do not lift Term shapes into DL.
    fn to_ofn(state: &ProofState) -> String {
        let mut ofn = String::new();
        ofn.push_str("Prefix(:=<http://echidna.example/ontology#>)\n");
        ofn.push_str("Ontology(<http://echidna.example/ontology>\n");
        for axiom in &state.context.axioms {
            ofn.push_str(&format!("  {}\n", axiom));
        }
        ofn.push_str(")\n");
        if let Some(goal) = state.goals.first() {
            ofn.push_str(&format!("\n# Entailment goal: {}\n", goal.target));
        }
        ofn
    }

    /// Parse ELK's stdout/stderr to a boolean proof verdict.
    ///
    /// `Ok(true)` when ELK reports the entailment holds or the
    /// ontology is inconsistent (which entails everything).  `Ok(false)`
    /// when ELK explicitly disproves the entailment.  `Err` when the
    /// output is uninterpretable.
    fn parse_result(output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        let positive = [
            "entailment: true",
            "entailment holds",
            "inconsistent",
            "is unsatisfiable",
            "result: entailed",
        ];
        let negative = [
            "entailment: false",
            "entailment does not hold",
            "is consistent",
            "result: not entailed",
            "no entailment",
        ];
        if positive.iter().any(|m| lower.contains(m)) {
            return Ok(true);
        }
        if negative.iter().any(|m| lower.contains(m)) {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "ELK output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for ElkBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::ELK
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run elk --version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("elk").to_string()
        } else {
            stderr.lines().next().unwrap_or("elk").to_string()
        };
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read OWL ontology file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "owl_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        // Lightweight extraction: every line of the form `SubClassOf(...)`
        // or `EquivalentClasses(...)` becomes an axiom; the file's
        // designated entailment query (if marked with `# Goal:`)
        // becomes the single goal.
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            if let Some(goal_text) = trimmed.strip_prefix("# Goal:") {
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(goal_text.trim().to_string()),
                    hypotheses: vec![],
                });
                continue;
            }
            if trimmed.starts_with("SubClassOf(")
                || trimmed.starts_with("EquivalentClasses(")
                || trimmed.starts_with("ClassAssertion(")
                || trimmed.starts_with("ObjectPropertyAssertion(")
            {
                state.context.axioms.push(trimmed.to_string());
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "ELK is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let ofn = Self::to_ofn(state);
        let mut child = Command::new(&self.config.executable)
            .arg("--classify")
            .arg("--input-format=ofn")
            .arg("-i")
            .arg("/dev/stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn elk")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open elk stdin"))?;
            stdin
                .write_all(ofn.as_bytes())
                .await
                .context("Failed to write to elk stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for elk")?;
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Self::parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(Self::to_ofn(state))
    }

    async fn suggest_tactics(
        &self,
        _state: &ProofState,
        _limit: usize,
    ) -> Result<Vec<Tactic>> {
        Ok(vec![])
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

    #[test]
    fn test_elk_kind() {
        let config = ProverConfig::default();
        let backend = ElkBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::ELK);
    }

    #[test]
    fn test_elk_to_ofn_emits_ontology_wrapper() {
        let mut state = ProofState::default();
        state.context.axioms.push("SubClassOf(:Cat :Animal)".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("SubClassOf(:Tabby :Animal)".to_string()),
            hypotheses: vec![],
        });
        let ofn = ElkBackend::to_ofn(&state);
        assert!(ofn.contains("Prefix(:="));
        assert!(ofn.contains("Ontology("));
        assert!(ofn.contains("SubClassOf(:Cat :Animal)"));
        assert!(ofn.contains("Entailment goal:"));
    }

    #[test]
    fn test_elk_parse_result_entailed() {
        assert!(ElkBackend::parse_result("Entailment: TRUE").expect("parse"));
    }

    #[test]
    fn test_elk_parse_result_inconsistent_implies_entailed() {
        assert!(ElkBackend::parse_result("Ontology is inconsistent").expect("parse"));
    }

    #[test]
    fn test_elk_parse_result_not_entailed() {
        assert!(!ElkBackend::parse_result("Entailment: FALSE").expect("parse"));
    }

    #[test]
    fn test_elk_parse_result_inconclusive_errors() {
        assert!(ElkBackend::parse_result("error: out of heap").is_err());
    }

    #[tokio::test]
    async fn test_elk_parse_string_extracts_axioms_and_goal() {
        let config = ProverConfig::default();
        let backend = ElkBackend::new(config);
        let owl = "SubClassOf(:Cat :Animal)\nClassAssertion(:Cat :tabby)\n# Goal: ClassAssertion(:Animal :tabby)\n";
        let state = backend.parse_string(owl).await.expect("parse_string");
        assert_eq!(state.context.axioms.len(), 2);
        assert_eq!(state.goals.len(), 1);
    }
}
