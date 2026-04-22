// SPDX-License-Identifier: PMPL-1.0-or-later

//! F* (F-star) backend -- dependent types with effects
//!
//! F* is a proof-oriented programming language with dependent types and
//! a sophisticated effect system. Used in Project Everest/HACL* for
//! verified cryptography.

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use crate::types::{Effect, TypeInfo};

/// F* backend
pub struct FStarBackend {
    config: ProverConfig,
}

impl FStarBackend {
    pub fn new(config: ProverConfig) -> Self {
        FStarBackend { config }
    }

    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut input = String::from("module Echidna.Export\n\n");
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            input.push_str(&format!("assume val axiom_{} : {}\n", i, axiom));
        }
        // Emit definitions with effect and refinement annotations from TypeInfo
        for def in &state.context.definitions {
            let effect_str = def
                .type_info
                .as_ref()
                .map(Self::effect_to_fstar)
                .unwrap_or_default();
            let refinement_str = def
                .type_info
                .as_ref()
                .and_then(|ti| ti.refinement.as_ref())
                .map(|pred| format!("{{v:{} | {}}}", def.ty, pred))
                .unwrap_or_else(|| format!("{}", def.ty));
            input.push_str(&format!("val {} : {}{}\n", def.name, effect_str, refinement_str));
        }
        if let Some(goal) = state.goals.first() {
            input.push_str(&format!("\nval goal : {}\n", goal.target));
        }
        Ok(input)
    }

    /// Convert effect row from [`TypeInfo`] to an F* effect annotation prefix.
    fn effect_to_fstar(ti: &TypeInfo) -> String {
        if ti.effects.is_empty() {
            return String::new();
        }
        let effect_name = ti
            .effects
            .effects
            .first()
            .map(|e| match e {
                Effect::Pure | Effect::Tot => "Tot",
                Effect::IO => "IO",
                Effect::State => "ST",
                Effect::Exception => "Exn",
                Effect::Div => "Div",
                Effect::Ghost => "GTot",
                Effect::NonDet => "ALL",
                Effect::Async => "ALL",
                Effect::Custom(s) => s.as_str(),
            })
            .unwrap_or("Tot");
        format!("{} ", effect_name)
    }

    fn parse_result(&self, output: &str) -> Result<bool> {
        let lower = output.to_lowercase();
        if lower.contains("verified") || lower.contains("all verification conditions discharged") {
            Ok(true)
        } else if lower.contains("error") || lower.contains("failed") {
            Ok(false)
        } else {
            Err(anyhow::anyhow!(
                "F* inconclusive: {}",
                output.lines().take(5).collect::<Vec<_>>().join("\n")
            ))
        }
    }
}

#[async_trait]
impl ProverBackend for FStarBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::FStar
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get F* version")?;
        Ok(String::from_utf8_lossy(&output.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .trim()
            .to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read F* file")?;
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
            "fstar_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with("//") || line.starts_with("(*") {
                continue;
            }
            if line.starts_with("val ") || line.starts_with("let ") {
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(line.to_string()),
                    hypotheses: vec![],
                });
            } else if line.starts_with("assume") {
                state.context.axioms.push(line.to_string());
            }
        }
        if state.goals.is_empty() {
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const("True".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "F*: interactive tactics not directly supported"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("F* timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let input = if let Some(src) = state.metadata.get("fstar_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn F*")?;
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("F* timed out")??;
        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
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

    #[tokio::test]
    async fn test_fstar_export() {
        let backend = FStarBackend::new(ProverConfig {
            executable: PathBuf::from("fstar.exe"),
            timeout: 10,
            ..Default::default()
        });
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("nat".to_string()),
            hypotheses: vec![],
        });
        let output = backend.to_input_format(&state).unwrap();
        assert!(output.contains("module Echidna.Export"));
    }

    #[tokio::test]
    async fn test_fstar_parse() {
        let backend = FStarBackend::new(ProverConfig {
            executable: PathBuf::from("fstar.exe"),
            timeout: 10,
            ..Default::default()
        });
        let state = backend
            .parse_string("val test : nat -> nat\nassume val ax : prop")
            .await
            .unwrap();
        assert!(!state.goals.is_empty());
    }

    #[test]
    fn test_fstar_result_parsing() {
        let backend = FStarBackend::new(ProverConfig {
            executable: PathBuf::from("fstar.exe"),
            timeout: 10,
            ..Default::default()
        });
        assert!(backend
            .parse_result("All verification conditions discharged")
            .unwrap());
        assert!(!backend.parse_result("Error in module").unwrap());
    }
}
