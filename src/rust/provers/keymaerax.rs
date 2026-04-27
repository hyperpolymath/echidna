// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! KeYmaera X backend — differential dynamic logic for hybrid systems
//!
//! KeYmaera X is the only theorem prover designed specifically for
//! **differential dynamic logic (dL)**, the extension of dynamic logic
//! used to verify hybrid systems (mixtures of discrete and continuous
//! state).  Typical use cases: aircraft collision-avoidance, train
//! control, surgical robotics, automotive cruise control.
//!
//! ## Why this backend exists
//!
//! Differential dynamic logic is **not** expressible in plain SMT or
//! TPTP-shaped first-order ATPs.  Programs in dL combine:
//!
//! - Hybrid programs: assignment, test, sequential composition,
//!   non-deterministic choice, and crucially `{x' = f(x) & H}`
//!   (continuous evolution under a domain constraint).
//! - Modalities: `[α]φ` ("after running α, φ holds") and `<α>φ`
//!   ("there is a run of α reaching φ").
//! - Quantifier-elimination over real-closed fields (delegated to
//!   Mathematica / Z3 / Polya internally).
//!
//! No other prover in the ECHIDNA roster covers this. KeYmaera X
//! plugs the hybrid-systems gap.
//!
//! ## Input format
//!
//! KeYmaera X archive files (`.kyx`) — text-based, structured as:
//!
//! ```text
//! ArchiveEntry "<name>"
//!   ProgramVariables Real x; Real v; End.
//!   Definitions ... End.
//!   Problem
//!     <pre> -> [<hybrid_program>] <post>
//!   End.
//!   Tactic "auto"
//!     auto
//!   End.
//! End.
//! ```
//!
//! ## Output parsing
//!
//! KeYmaera X reports proof status via stdout lines.  We accept any of:
//!
//! - `PROVED`  — proof closed
//! - `Proved` / `proved`  — proof closed (older versions)
//! - `OPEN`  / `Open` — open subgoals remain
//! - `Failed` / `Untrusted`  — proof refuted or inconclusive
//!
//! See `parse_result` for the full classifier.
//!
//! ## Integration tier
//!
//! Tier-5d / Phase-3.  Trust tier 2 (KeYmaera X delegates QE to
//! external CAS — those are not part of our trust root).  Complexity
//! 4: dL semantics + hybrid programs + tactic language.

#![allow(dead_code)]

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// KeYmaera X backend for differential dynamic logic.
pub struct KeYmaeraXBackend {
    config: ProverConfig,
}

impl KeYmaeraXBackend {
    pub fn new(config: ProverConfig) -> Self {
        KeYmaeraXBackend { config }
    }

    /// Convert a `ProofState` into a KeYmaera X `.kyx` archive entry.
    ///
    /// The conversion is intentionally minimal: we wrap the goal in
    /// the canonical `Problem ... End.` block, declare every axiom as
    /// a `Definitions` entry, and append a default `auto` tactic.  This
    /// is sufficient for round-tripping problems through the prover;
    /// richer hybrid-program input is expected to come from
    /// `parse_string` of an existing `.kyx` file rather than being
    /// reconstructed from `ProofState`.
    fn to_kyx(&self, state: &ProofState) -> Result<String> {
        let mut kyx = String::new();
        kyx.push_str("ArchiveEntry \"echidna_problem\"\n");

        // Heuristic: if axioms or the goal mention `Real ` declarations,
        // skip auto-emitting ProgramVariables; otherwise emit a default
        // empty block so the parser doesn't complain.
        let mentions_real_decl = state.context.axioms.iter().any(|a| a.contains("Real "))
            || state
                .goals
                .first()
                .map(|g| g.target.to_string().contains("Real "))
                .unwrap_or(false);
        if !mentions_real_decl {
            kyx.push_str("  ProgramVariables End.\n");
        }

        if !state.context.definitions.is_empty() {
            kyx.push_str("  Definitions\n");
            for def in &state.context.definitions {
                kyx.push_str(&format!("    {} End.\n", def));
            }
            kyx.push_str("  End.\n");
        }

        kyx.push_str("  Problem\n");
        for axiom in &state.context.axioms {
            kyx.push_str(&format!("    ({}) ->\n", axiom));
        }
        if let Some(goal) = state.goals.first() {
            kyx.push_str(&format!("    {}\n", goal.target));
        } else {
            // No goal → trivially true to keep the prover from erroring.
            kyx.push_str("    true\n");
        }
        kyx.push_str("  End.\n");

        kyx.push_str("  Tactic \"echidna-auto\"\n    auto\n  End.\n");
        kyx.push_str("End.\n");
        Ok(kyx)
    }

    /// Parse KeYmaera X stdout to determine proof success.
    ///
    /// Returns `Ok(true)` when KeYmaera X confirms a closed proof,
    /// `Ok(false)` when it explicitly reports an open or refuted
    /// goal, and `Err` for inconclusive / parse-error outputs.
    fn parse_result(&self, output: &str) -> Result<bool> {
        // Closed-proof markers (case-insensitive scan via lowercase copy).
        let lower = output.to_ascii_lowercase();
        let closed_markers = [
            "proved",                // generic
            "qed",                   // tactic language final marker
            "closed",                // proof tree closed
            "result: true",          // older CLI
            "[proof] proved",
        ];
        let open_markers = [
            "open subgoals",
            "open goals",
            "result: false",
            "untrusted",
            "failed",
            "no proof",
            "not proved",
        ];

        if closed_markers.iter().any(|m| lower.contains(m)) {
            return Ok(true);
        }
        if open_markers.iter().any(|m| lower.contains(m)) {
            return Ok(false);
        }
        Err(anyhow::anyhow!(
            "KeYmaera X output inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }
}

#[async_trait]
impl ProverBackend for KeYmaeraXBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::KeYmaeraX
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-version")
            .output()
            .await
            .context("Failed to run keymaerax -version")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = if !stdout.is_empty() {
            stdout.lines().next().unwrap_or("unknown").to_string()
        } else {
            stderr.lines().next().unwrap_or("unknown").to_string()
        };
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read .kyx file")?;
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
            "keymaerax_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        // Lightweight extraction: pull the body of `Problem ... End.` and
        // hand it back as a single goal target.  Parsing dL syntax fully
        // is out of scope for the round-trip; KeYmaera X re-parses the
        // archive itself before solving.
        if let Some(start) = content.find("Problem") {
            let after = &content[start + "Problem".len()..];
            if let Some(end) = after.find("End.") {
                let body = after[..end].trim();
                if !body.is_empty() {
                    state.goals.push(Goal {
                        id: "goal_0".to_string(),
                        target: Term::Const(body.to_string()),
                        hypotheses: vec![],
                    });
                }
            }
        }
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> {
        // KeYmaera X's tactic language (Bellerophon) is rich, but
        // exposing the full surface through ECHIDNA's `Tactic` shape
        // would be a separate piece of work.  The dispatch pipeline
        // does not currently invoke `apply_tactic` on KeYmaera X
        // (verify_proof handles the full flow), so we keep this stub
        // explicit rather than silently no-op.
        Err(anyhow::anyhow!(
            "KeYmaera X interactive tactics not supported via this trait \
             — drive proofs through `verify_proof` with embedded Bellerophon"
        ))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let kyx = self.to_kyx(state)?;
        let mut child = Command::new(&self.config.executable)
            .arg("-prove")
            .arg("/dev/stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn keymaerax")?;

        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("Failed to open keymaerax stdin"))?;
            stdin
                .write_all(kyx.as_bytes())
                .await
                .context("Failed to write to keymaerax stdin")?;
        }

        let output = child
            .wait_with_output()
            .await
            .context("Failed to wait for keymaerax")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        // KeYmaera X often writes results to stderr depending on flags.
        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_kyx(state)
    }

    async fn suggest_tactics(
        &self,
        state: &ProofState,
        limit: usize,
    ) -> Result<Vec<Tactic>> {
        if state.goals.is_empty() {
            return Ok(vec![]);
        }
        // KeYmaera X Bellerophon tactics. This is a curated starter set
        // covering the tactics most visible in the KeYmaera X tutorial and
        // distributed benchmark archive. The full Bellerophon language is
        // open-ended; GNN-ranked corpus suggestions (§4.4) will extend this.
        let tactics = vec![
            Tactic::Custom { prover: "keymaerax".to_string(), command: "auto".to_string(),      args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "QE".to_string(),        args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "loop".to_string(),      args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "ODE".to_string(),       args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "solve".to_string(),     args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "dI".to_string(),        args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "dC".to_string(),        args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "dW".to_string(),        args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "diffInd".to_string(),   args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "cut".to_string(),       args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "prop".to_string(),      args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "implyR".to_string(),    args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "andL".to_string(),      args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "hideL".to_string(),     args: vec![] },
            Tactic::Custom { prover: "keymaerax".to_string(), command: "closeTrue".to_string(), args: vec![] },
        ];
        Ok(crate::provers::gnn_augment_tactics(&self.config, state, "keymaerax", tactics, limit).await)
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
    fn test_keymaerax_kind() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::KeYmaeraX);
    }

    #[test]
    fn test_keymaerax_to_kyx_basic() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);

        let mut state = ProofState::default();
        state
            .context
            .axioms
            .push("x >= 0 & v >= 0".to_string());
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("[x' = v & x >= 0] x >= 0".to_string()),
            hypotheses: vec![],
        });
        let kyx = backend.to_kyx(&state).expect("to_kyx failed");
        assert!(kyx.contains("ArchiveEntry"));
        assert!(kyx.contains("Problem"));
        assert!(kyx.contains("[x' = v & x >= 0] x >= 0"));
        assert!(kyx.contains("Tactic"));
        assert!(kyx.contains("End."));
    }

    #[test]
    fn test_keymaerax_to_kyx_no_goal_emits_true() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);

        let state = ProofState::default();
        let kyx = backend.to_kyx(&state).expect("to_kyx failed");
        assert!(kyx.contains("true"));
    }

    #[test]
    fn test_keymaerax_parse_result_proved() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        let result = backend
            .parse_result("[Proof] Proved\nQED")
            .expect("parse_result failed");
        assert!(result);
    }

    #[test]
    fn test_keymaerax_parse_result_open() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        let result = backend
            .parse_result("Open subgoals: 2")
            .expect("parse_result failed");
        assert!(!result);
    }

    #[test]
    fn test_keymaerax_parse_result_failed() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        let result = backend
            .parse_result("Tactic Failed")
            .expect("parse_result failed");
        assert!(!result);
    }

    #[test]
    fn test_keymaerax_parse_result_inconclusive() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        let result =
            backend.parse_result("internal error: out of memory");
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_keymaerax_parse_string_extracts_problem() {
        let config = ProverConfig::default();
        let backend = KeYmaeraXBackend::new(config);
        let kyx = "ArchiveEntry \"x\"\n  Problem\n  x > 0 -> [x := x + 1;] x > 0\n  End.\nEnd.\n";
        let state = backend
            .parse_string(kyx)
            .await
            .expect("parse_string failed");
        assert_eq!(state.goals.len(), 1);
        match &state.goals[0].target {
            Term::Const(s) => assert!(s.contains("[x := x + 1;]")),
            _ => panic!("expected Term::Const"),
        }
    }

    #[tokio::test]
    async fn suggest_tactics_empty_goals_returns_empty() {
        let backend = KeYmaeraXBackend::new(ProverConfig::default());
        let state = ProofState::default();
        let tactics = backend.suggest_tactics(&state, 10).await.unwrap();
        assert!(tactics.is_empty());
    }

    #[tokio::test]
    async fn suggest_tactics_returns_kyx_tactics() {
        let backend = KeYmaeraXBackend::new(ProverConfig::default());
        let kyx = "ArchiveEntry \"x\"\n  Problem\n  x > 0 -> [x := x + 1;] x > 0\n  End.\nEnd.\n";
        let state = backend.parse_string(kyx).await.expect("parse_string");
        let tactics = backend.suggest_tactics(&state, 10).await.unwrap();
        assert!(!tactics.is_empty());
        let names: Vec<_> = tactics.iter().filter_map(|t| {
            if let Tactic::Custom { command, .. } = t { Some(command.as_str()) } else { None }
        }).collect();
        assert!(names.contains(&"auto"), "expected 'auto' tactic");
        assert!(names.contains(&"QE"),   "expected 'QE' tactic");
    }
}
