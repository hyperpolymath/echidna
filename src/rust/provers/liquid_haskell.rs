// SPDX-License-Identifier: PMPL-1.0-or-later
//! Liquid Haskell refinement-types verification backend.
//!
//! Liquid Haskell extends GHC with refinement types via the
//! `LiquidHaskell` plugin (or the older standalone `liquid` tool).
//! Annotations `{-@ ... @-}` carry the refinement contracts; the plugin
//! discharges them via Z3/CVC5/Yices.
//!
//! Trust tier: Tier 3 — auto-active SMT-backed verifier; the GHC
//! compilation pipeline is the TCB.
//!
//! Invocation: `liquid <file.hs>` (standalone) or `cabal v2-build` /
//! `stack build` with the plugin attached for project-shaped inputs.
//! Output reports SAFE / UNSAFE / ERROR per file.

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct LiquidHaskellBackend {
    config: ProverConfig,
}

impl LiquidHaskellBackend {
    pub fn new(config: ProverConfig) -> Self {
        LiquidHaskellBackend { config }
    }

    /// Generate a minimal Liquid-Haskell-annotated module for the goal.
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::from(
            "-- SPDX-License-Identifier: PMPL-1.0-or-later\n\
             {-# LANGUAGE NoImplicitPrelude #-}\n\
             module EchidnaGoal where\n\n\
             import Prelude hiding (Bool)\n\
             data Bool = True | False\n\n",
        );

        if let Some(g) = state.goals.first() {
            let cond = self.term_to_haskell_expr(&g.target);
            s.push_str("{-@ goal :: { v: Bool | v == True } @-}\n");
            s.push_str("goal :: Bool\n");
            s.push_str(&format!("goal = {}\n", cond));
        }

        Ok(s)
    }

    fn term_to_haskell_expr(&self, term: &Term) -> String {
        match term {
            Term::Const(name) | Term::Var(name) => match name.as_str() {
                "true" | "True" => "True".into(),
                "false" | "False" => "False".into(),
                _ => name.clone(),
            },
            Term::App { func, args } => {
                let f = self.term_to_haskell_expr(func);
                let a = args
                    .iter()
                    .map(|x| self.term_to_haskell_expr(x))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({} {})", f, a)
            }
            _ => "True".to_string(),
        }
    }

    /// Parse Liquid Haskell output.  Standalone `liquid` reports "RESULT:
    /// SAFE" on success, "RESULT: UNSAFE" on failure.  The plugin path
    /// reports the same via stdout.  Compile errors before LH runs are
    /// returned as Err (inconclusive).
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        // SAFE markers — be specific so we don't false-positive on the
        // word "safe" appearing in unrelated output.
        if l.contains("result: safe")
            || l.contains("liquid: safe")
            || l.contains("** safe **")
        {
            return Ok(true);
        }
        if l.contains("result: unsafe")
            || l.contains("liquid: unsafe")
            || l.contains("** unsafe **")
            || l.contains("counter-example")
        {
            return Ok(false);
        }
        if l.contains("error") || l.contains("ghc:") {
            return Err(anyhow::anyhow!(
                "Liquid Haskell GHC compile error before refinement check"
            ));
        }
        Err(anyhow::anyhow!("Liquid Haskell inconclusive"))
    }
}

#[async_trait]
impl ProverBackend for LiquidHaskellBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::LiquidHaskell
    }
    async fn version(&self) -> Result<String> {
        let o = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await?;
        Ok(String::from_utf8_lossy(&o.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .to_string())
    }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".into(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "haskell_source".into(),
            serde_json::Value::String(content.to_string()),
        );
        // Goal count = number of `{-@ ... @-}` annotation blocks.
        let n = content.matches("{-@").count().max(1);
        for i in 0..n {
            state.goals.push(Goal {
                id: format!("goal_{i}"),
                target: Term::Const("True".into()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Liquid Haskell: auto-active, no interactive tactics"
        ))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state
            .metadata
            .get("source_path")
            .and_then(|v| v.as_str())
        {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 30),
                Command::new(&self.config.executable)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("Liquid Haskell timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let input = if let Some(src) =
            state.metadata.get("haskell_source").and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };

        let temp = tempfile::Builder::new()
            .suffix(".hs")
            .tempfile()
            .context("temp hs")?;
        tokio::fs::write(temp.path(), input.as_bytes()).await?;

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 30),
            Command::new(&self.config.executable)
                .arg(temp.path())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .context("Liquid Haskell timed out")??;

        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(
        &self,
        _state: &ProofState,
        limit: usize,
    ) -> Result<Vec<Tactic>> {
        let suggestions = vec![
            Tactic::Custom {
                prover: "liquid-haskell".into(),
                command: "measure".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "liquid-haskell".into(),
                command: "data".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "liquid-haskell".into(),
                command: "type".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "liquid-haskell".into(),
                command: "predicate".into(),
                args: vec![],
            },
        ];
        Ok(suggestions.into_iter().take(limit).collect())
    }
    async fn search_theorems(&self, _: &str) -> Result<Vec<String>> {
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

    fn b() -> LiquidHaskellBackend {
        LiquidHaskellBackend::new(ProverConfig::default())
    }

    #[test]
    fn parse_result_safe() {
        assert!(b().parse_result("RESULT: SAFE\n").unwrap());
    }

    #[test]
    fn parse_result_unsafe() {
        assert!(!b().parse_result("RESULT: UNSAFE — counter-example: x = 0").unwrap());
    }

    #[test]
    fn parse_result_ghc_error() {
        let e = b().parse_result("ghc: error: Variable not in scope: foo");
        assert!(e.is_err());
    }

    #[test]
    fn parse_result_no_marker_returns_err() {
        let e = b().parse_result("totally unrelated noise");
        assert!(e.is_err());
    }

    #[tokio::test]
    async fn parse_string_counts_lh_annotations() {
        let src = "{-@ foo :: Int @-}\n{-@ bar :: Bool @-}\n{-@ baz :: () @-}\n";
        let state = b().parse_string(src).await.unwrap();
        assert_eq!(state.goals.len(), 3);
    }
}
