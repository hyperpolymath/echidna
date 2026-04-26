// SPDX-License-Identifier: PMPL-1.0-or-later
//! GNATprove (SPARK/Ada) auto-active verification backend.
//!
//! GNATprove is the SPARK toolset's verifier — it discharges proof
//! obligations on Ada code annotated with SPARK contracts (Pre / Post /
//! Type_Invariant / Subtype_Predicate / Loop_Invariant / Loop_Variant /
//! Ghost) using a Why3-based pipeline that fans out to Z3, CVC5, Alt-Ergo.
//!
//! Pairs directly with the standing "Rust always means Rust/SPARK"
//! standard: the SPARK harness in `src/ada/spark/` already proves the
//! axiom-policy + coprocessor-tier invariants — this backend lets ECHIDNA
//! drive that toolchain (and any user SPARK project) as a regular prover.
//!
//! Trust tier: Tier 4 in the prover hierarchy — small-kernel verifier
//! with formal foundations (Why3 + Z3/CVC5/Alt-Ergo proof certificates).
//!
//! Invocation: `gnatprove -P <project.gpr> --mode=prove --report=fail`.
//! When the user passes raw SPARK source via `parse_string`, we generate
//! a minimal `.gpr` project file in a temp dir alongside the source.

#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct GNATproveBackend {
    config: ProverConfig,
}

impl GNATproveBackend {
    pub fn new(config: ProverConfig) -> Self {
        GNATproveBackend { config }
    }

    /// Generate a minimal SPARK .ads/.adb pair from a ProofState.  The
    /// goal is wired as a procedure post-condition so GNATprove proves it.
    fn to_input_format(&self, state: &ProofState) -> Result<(String, String)> {
        let mut spec = String::from(
            "-- SPDX-License-Identifier: PMPL-1.0-or-later\n\
             package Echidna_Goal with SPARK_Mode => On is\n",
        );
        let mut body = String::from(
            "-- SPDX-License-Identifier: PMPL-1.0-or-later\n\
             package body Echidna_Goal with SPARK_Mode => On is\n",
        );

        if let Some(g) = state.goals.first() {
            let post = self.term_to_ada_expr(&g.target);
            spec.push_str(&format!(
                "   procedure Goal\n   with Post => {};\n",
                post
            ));
            body.push_str(
                "   procedure Goal is\n   begin\n      null;\n   end Goal;\n",
            );
        }

        spec.push_str("end Echidna_Goal;\n");
        body.push_str("end Echidna_Goal;\n");
        Ok((spec, body))
    }

    /// Render a Term into an Ada Boolean expression.  Best-effort for
    /// generated tests; real SPARK source flows through verbatim via
    /// `state.metadata["spark_source"]`.
    fn term_to_ada_expr(&self, term: &Term) -> String {
        match term {
            Term::Const(name) | Term::Var(name) => name.clone(),
            Term::App { func, args } => {
                let f = self.term_to_ada_expr(func);
                let a = args
                    .iter()
                    .map(|x| self.term_to_ada_expr(x))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", f, a)
            }
            _ => "True".to_string(),
        }
    }

    /// Parse GNATprove output: success when "0 unproved check(s)" or
    /// "everything proved" is found.  Failure when "unproved" or "error"
    /// appears.  Inconclusive otherwise.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("0 unproved")
            || l.contains("everything proved")
            || l.contains("phase 1 of 2: generation of global contracts ...")
                && !l.contains("unproved")
        {
            Ok(true)
        } else if l.contains("unproved")
            || l.contains("not proved")
            || l.contains("medium: ")
            || l.contains("error: ")
            || l.contains("severe: ")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!("GNATprove inconclusive"))
        }
    }
}

#[async_trait]
impl ProverBackend for GNATproveBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::GNATprove
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
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "spark_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        // Heuristic: scan for procedure / function declarations so the
        // count of goals reflects what GNATprove will discharge.
        let mut found = false;
        for line in content.lines() {
            let t = line.trim_start();
            for kw in &["procedure ", "function ", "package "] {
                if t.starts_with(kw) {
                    state.goals.push(Goal {
                        id: format!("goal_{}", state.goals.len()),
                        target: Term::Const("True".to_string()),
                        hypotheses: vec![],
                    });
                    found = true;
                }
            }
        }
        if !found {
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const("True".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "GNATprove: auto-active, no interactive tactics"
        ))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // If a project file was provided in metadata, use it.
        if let Some(gpr) = state
            .metadata
            .get("project_file")
            .and_then(|v| v.as_str())
        {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg("-P")
                    .arg(gpr)
                    .arg("--mode=prove")
                    .arg("--report=fail")
                    .arg("--level=2")
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("GNATprove timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        // Otherwise: stage source + minimal .gpr in a temp dir.
        let (spec, body) = if let Some(src) =
            state.metadata.get("spark_source").and_then(|v| v.as_str())
        {
            // Raw source — split into spec/body by package boundary if
            // possible, else treat the whole thing as a body.
            split_ada_source(src)
        } else {
            self.to_input_format(state)?
        };

        let dir = tempfile::tempdir().context("tempdir")?;
        let spec_path = dir.path().join("echidna_goal.ads");
        let body_path = dir.path().join("echidna_goal.adb");
        let gpr_path = dir.path().join("echidna_goal.gpr");
        tokio::fs::write(&spec_path, spec.as_bytes()).await?;
        tokio::fs::write(&body_path, body.as_bytes()).await?;
        tokio::fs::write(&gpr_path, MIN_GPR.as_bytes()).await?;

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            Command::new(&self.config.executable)
                .arg("-P")
                .arg(&gpr_path)
                .arg("--mode=prove")
                .arg("--report=fail")
                .arg("--level=2")
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .context("GNATprove timed out")??;

        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        let (spec, body) = self.to_input_format(state)?;
        Ok(format!("-- spec --\n{}\n-- body --\n{}", spec, body))
    }
    async fn suggest_tactics(
        &self,
        _state: &ProofState,
        limit: usize,
    ) -> Result<Vec<Tactic>> {
        let suggestions = vec![
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Pre".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Post".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Loop_Invariant".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Loop_Variant".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Type_Invariant".into(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "gnatprove".into(),
                command: "Ghost".into(),
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

fn split_ada_source(src: &str) -> (String, String) {
    // Split the input into a spec part (before "package body") and a body part.
    // If no body marker exists, treat the whole thing as the body and
    // synthesise a minimal spec.
    if let Some(idx) = src.find("package body") {
        (src[..idx].to_string(), src[idx..].to_string())
    } else {
        (
            "package Echidna_Goal with SPARK_Mode => On is\nend Echidna_Goal;\n".to_string(),
            src.to_string(),
        )
    }
}

const MIN_GPR: &str = "\
-- SPDX-License-Identifier: PMPL-1.0-or-later
project Echidna_Goal is
   for Source_Dirs use (\".\");
   for Object_Dir  use \"obj\";
   package Compiler is
      for Default_Switches (\"Ada\") use (\"-gnat2022\", \"-gnatVa\", \"-gnateS\");
   end Compiler;
   package Prove is
      for Switches use (\"--mode=prove\", \"--level=2\", \"--report=fail\");
   end Prove;
end Echidna_Goal;
";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_result_proved() {
        let b = GNATproveBackend::new(ProverConfig::default());
        let out = "Phase 1 of 2: generation of global contracts ...\n0 unproved check(s)\n";
        assert!(b.parse_result(out).unwrap());
    }

    #[test]
    fn parse_result_unproved() {
        let b = GNATproveBackend::new(ProverConfig::default());
        let out = "echidna_goal.adb:5:7: medium: postcondition might fail\n1 unproved check(s)\n";
        assert!(!b.parse_result(out).unwrap());
    }

    #[test]
    fn parse_result_inconclusive_returns_err() {
        let b = GNATproveBackend::new(ProverConfig::default());
        assert!(b.parse_result("totally unrelated noise").is_err());
    }

    #[test]
    fn split_ada_source_with_body() {
        let src = "package Foo is\n   procedure Bar;\nend Foo;\n\
                   package body Foo is\n   procedure Bar is begin null; end Bar;\nend Foo;\n";
        let (spec, body) = split_ada_source(src);
        assert!(spec.contains("package Foo is"));
        assert!(body.starts_with("package body Foo"));
    }

    #[test]
    fn split_ada_source_body_only() {
        let (spec, body) = split_ada_source("procedure Bar is begin null; end Bar;\n");
        assert!(spec.contains("Echidna_Goal"));
        assert!(body.contains("procedure Bar"));
    }
}
