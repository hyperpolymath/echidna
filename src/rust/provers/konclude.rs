// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Konclude backend — high-performance reasoner for full OWL 2 DL (SROIQ).
//!
//! Konclude is a tableau-based reasoner that handles the full OWL 2
//! DL profile (the description logic SROIQ).  It is the fastest
//! tableau reasoner across the OWL Reasoner Evaluation (ORE)
//! benchmark suite for ABox-heavy ontologies and a strong second on
//! TBox classification.
//!
//! ## Why this backend exists
//!
//! ELK (also in this phase) is restricted to the EL profile.
//! Anything beyond EL — number restrictions, inverse properties,
//! nominals, complex role hierarchies — needs a SROIQ reasoner.
//! Konclude fills that slot in ECHIDNA's roster, with the speed
//! profile that competing reasoners (HermiT, Pellet, FaCT++) lack.
//!
//! ## Input format
//!
//! Same as ELK: OWL Functional Syntax, Manchester, RDF/XML, Turtle,
//! and N-Triples.  Konclude auto-detects from the file extension.
//!
//! ## CLI invocation
//!
//! `Konclude classify -i <ontology>` for classification.
//! `Konclude consistency -i <ontology>` for satisfiability.
//! `Konclude entail -i <ontology> -e <axiom-file>` for entailment.
//!
//! ## Output parsing
//!
//! Konclude emits result lines tagged with the operation:
//!
//! - `Consistent: true|false`
//! - `Entailment: true|false`
//! - `Classification successful`
//!
//! See `parse_result` for the full classifier.
//!
//! ## Integration tier
//!
//! Tier-5h / Phase-4.  Trust tier 3 (peer-reviewed tableau kernel,
//! soundness proofs in literature).  Complexity 4 (full SROIQ +
//! tableau saturation).

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Konclude backend for OWL 2 DL (SROIQ) reasoning.
pub struct KoncludeBackend {
    config: ProverConfig,
}

impl KoncludeBackend {
    pub fn new(config: ProverConfig) -> Self {
        KoncludeBackend { config }
    }

    /// Render a `ProofState` into an OWL Functional Syntax ontology.
    /// The shape is identical to ELK's emitter — both reasoners ingest
    /// the same OFN dialect — but is duplicated here rather than
    /// centralised because the two backends evolve independently.
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

    /// Parse Konclude's output to a boolean verdict.
    fn parse_result(output: &str) -> Result<bool> {
        let lower = output.to_ascii_lowercase();
        let positive = [
            "entailment: true",
            "entailed: true",
            "is entailed",
            "consistent: false",
            "is inconsistent",
        ];
        let negative = [
            "entailment: false",
            "entailed: false",
            "not entailed",
            "consistent: true",
            "is consistent",
        ];
        if positive.iter().any(|m| lower.contains(m)) {
            return Ok(true);
        }
        if negative.iter().any(|m| lower.contains(m)) {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "Konclude output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for KoncludeBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Konclude
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to run konclude --version")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("konclude").to_string()
        } else {
            stderr.lines().next().unwrap_or("konclude").to_string()
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
            // Recognise the full SROIQ axiom set, not just the EL subset.
            if trimmed.starts_with("SubClassOf(")
                || trimmed.starts_with("EquivalentClasses(")
                || trimmed.starts_with("DisjointClasses(")
                || trimmed.starts_with("ClassAssertion(")
                || trimmed.starts_with("ObjectPropertyAssertion(")
                || trimmed.starts_with("DataPropertyAssertion(")
                || trimmed.starts_with("InverseObjectProperties(")
                || trimmed.starts_with("FunctionalObjectProperty(")
                || trimmed.starts_with("TransitiveObjectProperty(")
                || trimmed.starts_with("SubObjectPropertyOf(")
            {
                state.context.axioms.push(trimmed.to_string());
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Konclude is fully automated — interactive tactics not supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let ofn = Self::to_ofn(state);
        let mut child = Command::new(&self.config.executable)
            .arg("classify")
            .arg("-i")
            .arg("/dev/stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn konclude")?;
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open konclude stdin"))?;
            stdin
                .write_all(ofn.as_bytes())
                .await
                .context("Failed to write to konclude stdin")?;
        }
        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for konclude")?;
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
    fn test_konclude_kind() {
        let config = ProverConfig::default();
        let backend = KoncludeBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Konclude);
    }

    #[test]
    fn test_konclude_to_ofn_includes_axioms() {
        let mut state = ProofState::default();
        state
            .context
            .axioms
            .push("InverseObjectProperties(:hasParent :hasChild)".to_string());
        let ofn = KoncludeBackend::to_ofn(&state);
        assert!(ofn.contains("InverseObjectProperties"));
        assert!(ofn.contains("Ontology"));
    }

    #[test]
    fn test_konclude_parse_result_entailed() {
        assert!(KoncludeBackend::parse_result("Entailment: true").expect("parse"));
    }

    #[test]
    fn test_konclude_parse_result_inconsistent_is_proof() {
        assert!(KoncludeBackend::parse_result("Consistent: false").expect("parse"));
    }

    #[test]
    fn test_konclude_parse_result_consistent_no_proof() {
        assert!(!KoncludeBackend::parse_result("Consistent: true").expect("parse"));
    }

    #[test]
    fn test_konclude_parse_result_silence_errors() {
        assert!(KoncludeBackend::parse_result("").is_err());
    }

    #[tokio::test]
    async fn test_konclude_parse_string_recognises_sroiq_axioms() {
        let config = ProverConfig::default();
        let backend = KoncludeBackend::new(config);
        let owl = "TransitiveObjectProperty(:partOf)\nDisjointClasses(:Cat :Dog)\n# Goal: ClassAssertion(:Animal :rex)\n";
        let state = backend.parse_string(owl).await.expect("parse_string");
        assert_eq!(state.context.axioms.len(), 2);
        assert_eq!(state.goals.len(), 1);
    }
}
