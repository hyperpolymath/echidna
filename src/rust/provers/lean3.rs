// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Lean 3 theorem prover backend.
//!
//! Sibling to the Lean 4 backend (`super::lean`), not a version of it —
//! Lean 3 and Lean 4 have incompatible syntax and tactic languages, and
//! mathlib3 preserves a substantial body of formal mathematics that is
//! not isomorphic to mathlib4. Both are kept for corpus variety and
//! triangulation: many mathlib3→mathlib4 port-pairs give the arbiter
//! natural cross-system evidence for the same theorem statement.
//!
//! This backend shells out to the `lean3` / `lean --version=3` binary
//! via the `leanpkg` build system (not `lake`, which is Lean 4). File
//! extension collision (`.lean` is used by both) is resolved by
//! content-aware detection — see `detect_from_file_content` for the
//! `import` / `open` / `universes` heuristic, plus the presence of
//! `leanpkg.toml` in the directory tree.
//!
//! Corpus extraction is done Julia-side via
//! `scripts/extract_lean3.jl` against leanprover-community/mathlib. The
//! backend here is deliberately thin — the heavy proof-state modelling
//! lives in the Lean 4 backend and most of it transfers directly; where
//! Lean 3 differs (tactic-block `begin … end` syntax vs Lean 4's
//! `by …`, namespace vs section semantics, different `simp` defaults)
//! the extractor handles the translation.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Lean 3 theorem prover backend.
pub struct Lean3Backend {
    config: ProverConfig,
}

impl Lean3Backend {
    pub fn new(config: ProverConfig) -> Self {
        Lean3Backend { config }
    }

    /// Resolve the binary name. Defaults to `lean3`; falls back to
    /// `lean --version=3` if the user has only the unified lean binary.
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("lean3")
        } else {
            self.config.executable.clone()
        }
    }
}

#[async_trait]
impl ProverBackend for Lean3Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Lean3
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary()).arg("--version").output().await;
        match output {
            Ok(out) if out.status.success() => {
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            },
            Ok(out) => Ok(format!(
                "lean3@unavailable (status {:?})",
                out.status.code()
            )),
            Err(_) => Ok("lean3@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Lean 3: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    /// Minimal parse: store the source on the proof state for the
    /// verification round-trip. Full syntactic parsing lives in the
    /// extractor; the backend's job is to invoke `lean3` on whole files.
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![Goal {
                id: "lean3-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "lean3_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // Lean 3 is a whole-file batch prover in the CLI sense; tactic
        // application lives inside `begin … end` blocks in the source.
        // We record the tactic for extractor provenance but don't
        // attempt to re-elaborate here.
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let source: String = state
            .metadata
            .get("lean3_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| {
                state
                    .goals
                    .first()
                    .map(|g| format!("{}", g.target))
                    .unwrap_or_default()
            });

        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-lean3-")
            .tempdir()
            .context("Lean 3: tempdir")?;
        let input = tmp_dir.path().join("check.lean");
        tokio::fs::write(&input, source.as_bytes())
            .await
            .context("Lean 3: writing input")?;

        let mut cmd = Command::new(self.binary());
        cmd.arg("--make")
            .arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                tracing::debug!(
                    status = ?out.status.code(),
                    "Lean 3: verify_proof rejected"
                );
                tracing::trace!(stderr = %stderr);
                Ok(false)
            },
            Err(e) => Err(anyhow!("Lean 3: binary not runnable: {}", e)),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        Ok(state
            .metadata
            .get("lean3_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| {
                state
                    .goals
                    .iter()
                    .map(|g| format!("{}", g.target))
                    .collect::<Vec<_>>()
                    .join("\n")
            }))
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Lean 3 uses the same core tactic set as Lean 4 but with slightly
        // different names. These cover the most commonly needed steps.
        // (The Lean 3 corpus will improve premise ranking once extracted via
        // scripts/extract_lean3.jl, but these static hints are immediately useful.)
        let tactics = vec![
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "simp".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "ring".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "linarith".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "omega".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "tauto".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "lean3".to_string(),
                command: "finish".to_string(),
                args: vec![],
            },
            Tactic::Reflexivity,
            Tactic::Assumption,
            Tactic::Simplify,
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Lean 3 #check / search_proof_tactic require a running server;
        // return empty as a safe fallback until the batch-query bridge is wired.
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
    async fn parse_string_stores_source_in_metadata() {
        let backend = Lean3Backend::new(ProverConfig::default());
        let src = "import data.nat.basic\n\ntheorem foo : 1 + 1 = 2 := rfl\n";
        let state = backend.parse_string(src).await.unwrap();
        let stored = state
            .metadata
            .get("lean3_source")
            .and_then(|v| v.as_str())
            .unwrap();
        assert_eq!(stored, src);
    }

    #[tokio::test]
    async fn export_round_trips_the_source() {
        let backend = Lean3Backend::new(ProverConfig::default());
        let src = "example : true := trivial\n";
        let state = backend.parse_string(src).await.unwrap();
        let exported = backend.export(&state).await.unwrap();
        assert_eq!(exported, src);
    }

    #[test]
    fn kind_is_lean3() {
        let backend = Lean3Backend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Lean3);
    }
}
