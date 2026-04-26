// SPDX-License-Identifier: PMPL-1.0-or-later
//! Stainless (Scala / Inox) refinement-types verification backend.
//!
//! Stainless verifies Scala programs against refinement-type contracts:
//! `require` (precondition), `ensuring` (postcondition), `decreases`
//! (termination measure), `@invariant` (class invariant).  Discharges
//! obligations via Inox + Z3/CVC5 backends.
//!
//! Trust tier: Tier 3 — auto-active verifier with SMT-backed proofs but
//! a much larger TCB than small-kernel ITPs.  The Scala/JVM toolchain is
//! itself a non-trivial dependency.
//!
//! Invocation: `stainless <file.scala>` (or `sbt stainlessCompile` for
//! larger projects).  Output contains "valid" / "invalid" / "unknown"
//! per verification condition.

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct StainlessBackend {
    config: ProverConfig,
}

impl StainlessBackend {
    pub fn new(config: ProverConfig) -> Self {
        StainlessBackend { config }
    }

    /// Generate a minimal Stainless-annotated Scala program for the goal.
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::from(
            "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
             import stainless.lang._\n\
             import stainless.annotation._\n\n\
             object EchidnaGoal {\n",
        );

        if let Some(g) = state.goals.first() {
            let cond = self.term_to_scala_expr(&g.target);
            s.push_str(&format!(
                "  def goal: Boolean = {{ {} }}.ensuring(_ == true)\n",
                cond
            ));
        }

        s.push_str("}\n");
        Ok(s)
    }

    /// Render a Term into a Scala Boolean expression.
    fn term_to_scala_expr(&self, term: &Term) -> String {
        match term {
            Term::Const(name) | Term::Var(name) => match name.as_str() {
                "true" | "True" => "true".into(),
                "false" | "False" => "false".into(),
                _ => name.clone(),
            },
            Term::App { func, args } => {
                let f = self.term_to_scala_expr(func);
                let a = args
                    .iter()
                    .map(|x| self.term_to_scala_expr(x))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", f, a)
            }
            _ => "true".to_string(),
        }
    }

    /// Parse Stainless output: a program is verified when every VC reports
    /// "valid"; failed when any VC reports "invalid" or "counter-example".
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        // Strong negative signals first — one invalid VC fails the lot.
        if l.contains("invalid")
            || l.contains("counter-example")
            || l.contains("counterexample")
            || l.contains("verification failed")
        {
            return Ok(false);
        }
        // Strong positive: explicit success markers.
        if l.contains("verified")
            || l.contains("all valid")
            || l.contains("verification successful")
        {
            return Ok(true);
        }
        // Weaker positive: at least one "valid" VC and no "unknown" / errors.
        if l.contains("valid") && !l.contains("unknown") && !l.contains("error") {
            return Ok(true);
        }
        Err(anyhow::anyhow!("Stainless inconclusive"))
    }
}

#[async_trait]
impl ProverBackend for StainlessBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Stainless
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
            "scala_source".into(),
            serde_json::Value::String(content.to_string()),
        );
        // Goal count = number of `def` declarations + number of explicit
        // `ensuring(` blocks (best-effort heuristic).
        let defs = content.matches("def ").count();
        let ensures = content.matches("ensuring(").count();
        let n = (defs + ensures).max(1);
        for i in 0..n {
            state.goals.push(Goal {
                id: format!("goal_{i}"),
                target: Term::Const("true".into()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Stainless: auto-active, no interactive tactics"
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
            .context("Stainless timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let input = if let Some(src) =
            state.metadata.get("scala_source").and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };

        let temp = tempfile::Builder::new()
            .suffix(".scala")
            .tempfile()
            .context("temp scala")?;
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
        .context("Stainless timed out")??;

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
                prover: "stainless".into(),
                command: "require".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "stainless".into(),
                command: "ensuring".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "stainless".into(),
                command: "decreases".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "stainless".into(),
                command: "invariant".into(),
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

    fn b() -> StainlessBackend {
        StainlessBackend::new(ProverConfig::default())
    }

    #[test]
    fn parse_result_valid() {
        assert!(b().parse_result("VC valid (Z3)\n").unwrap());
    }

    #[test]
    fn parse_result_invalid() {
        assert!(!b().parse_result("VC invalid: counter-example found\n").unwrap());
    }

    #[test]
    fn parse_result_unknown_returns_err() {
        assert!(b().parse_result("unknown — solver gave up").is_err());
    }

    #[test]
    fn input_format_includes_imports() {
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "g".into(),
            target: Term::Const("true".into()),
            hypotheses: vec![],
        });
        let s = b().to_input_format(&state).unwrap();
        assert!(s.contains("import stainless.lang._"));
        assert!(s.contains("import stainless.annotation._"));
        assert!(s.contains("ensuring"));
    }

    #[tokio::test]
    async fn parse_string_counts_defs() {
        let src = "def foo = 1\ndef bar = 2\ndef baz = 3\n";
        let state = b().parse_string(src).await.unwrap();
        assert_eq!(state.goals.len(), 3);
    }
}
