// SPDX-License-Identifier: MPL-2.0
//! Chuffed lazy clause generation CP solver backend
#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
pub struct ChuffedBackend {
    config: ProverConfig,
}
impl ChuffedBackend {
    pub fn new(config: ProverConfig) -> Self {
        ChuffedBackend { config }
    }
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s = String::new();
        if let Some(g) = state.goals.first() {
            s.push_str(&format!("% goal: {}\n", g.target));
        }
        Ok(s)
    }
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("----------") || l.contains("==========") {
            Ok(true)
        } else if l.contains("unsatisfiable")
            || l.contains("=====unsatisfiable=====")
            || l.contains("error")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!("Chuffed inconclusive"))
        }
    }
}
#[async_trait]
impl ProverBackend for ChuffedBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Chuffed
    }
    async fn version(&self) -> Result<String> {
        // Upstream fzn-chuffed has no --version option. Require a successful
        // real process response instead of returning a constant without exec.
        let limit = std::time::Duration::from_secs(self.config.timeout.clamp(1, 10));
        let mut command = Command::new(&self.config.executable);
        command.arg("--help");
        command.stdin(Stdio::null());
        command.kill_on_drop(true);
        let output = tokio::time::timeout(limit, command.output())
            .await
            .with_context(|| format!("fzn-chuffed --help timed out after {}s", limit.as_secs()))?
            .context("Failed to execute fzn-chuffed --help")?;
        anyhow::ensure!(output.status.success(), "fzn-chuffed --help failed");
        let help = String::from_utf8_lossy(&output.stdout);
        let banner = help
            .lines()
            .find(|line| !line.trim().is_empty())
            .context("fzn-chuffed --help returned no output")?;
        Ok(format!("Chuffed (version unavailable; --help): {banner}"))
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
            "chuffed_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        for line in content.lines() {
            let l = line.trim();
            if !l.is_empty() && !l.starts_with("%") {
                state.goals.push(Goal {
                    id: format!("goal_{}", state.goals.len()),
                    target: Term::Const(l.to_string()),
                    hypotheses: vec![],
                });
            }
        }
        if state.goals.is_empty() {
            state.goals.push(Goal {
                id: "goal_0".to_string(),
                target: Term::Const("satisfy".to_string()),
                hypotheses: vec![],
            });
        }
        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!("Chuffed: CP solver, not interactive"))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Prefer the original FlatZinc source — reconstructing from the
        // Term IR via `to_input_format` loses all constraint structure.
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
            .context("Chuffed timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let input = if let Some(src) = state
            .metadata
            .get("chuffed_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };
        let mut child = Command::new(&self.config.executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to spawn Chuffed")?;
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(input.as_bytes()).await?;
            drop(stdin);
        }
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            child.wait_with_output(),
        )
        .await
        .context("Chuffed timed out")??;
        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Chuffed is a lazy-clause-generation CP solver. Suggestions are
        // MiniZinc solve annotations and propagation strategy hints.
        let tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "chuffed".to_string(),
                command: "solve".to_string(),
                args: vec!["satisfy".to_string()],
            },
            Tactic::Custom {
                prover: "chuffed".to_string(),
                command: "annotation".to_string(),
                args: vec!["int_search(vars, first_fail, indomain_min, complete)".to_string()],
            },
            Tactic::Custom {
                prover: "chuffed".to_string(),
                command: "annotation".to_string(),
                args: vec!["seq_search([...])".to_string()],
            },
            Tactic::Custom {
                prover: "chuffed".to_string(),
                command: "set-option".to_string(),
                args: vec!["--prop-fifo".to_string()],
            },
        ];
        Ok(
            crate::provers::gnn_augment_tactics(&self.config, state, "chuffed", tactics, limit)
                .await,
        )
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Constraint solvers do not have theorem libraries.
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
    async fn test_chuffed_export() {
        let b = ChuffedBackend::new(ProverConfig {
            executable: PathBuf::from("fzn-chuffed"),
            timeout: 10,
            ..Default::default()
        });
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("satisfy".to_string()),
            hypotheses: vec![],
        });
        assert!(b.to_input_format(&s).unwrap().contains("goal"));
    }
    #[tokio::test]
    async fn test_chuffed_parse() {
        let b = ChuffedBackend::new(ProverConfig {
            executable: PathBuf::from("fzn-chuffed"),
            timeout: 10,
            ..Default::default()
        });
        let s = b.parse_string("var int: x :: output_var;").await.unwrap();
        assert!(!s.goals.is_empty());
    }
    #[test]
    fn test_chuffed_result() {
        let b = ChuffedBackend::new(ProverConfig {
            executable: PathBuf::from("fzn-chuffed"),
            timeout: 10,
            ..Default::default()
        });
        assert!(b.parse_result("----------").unwrap());
    }

    #[cfg(unix)]
    fn version_fixture(script: &str, timeout: u64) -> (tempfile::TempDir, ChuffedBackend) {
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("version-probe");
        crate::provers::test_fixture::write_executable(
            &executable,
            &format!("#!/bin/sh\n[ \"$#\" -eq 1 ] && [ \"$1\" = '--help' ] || exit 64\n{script}\n"),
        );
        let backend = ChuffedBackend::new(ProverConfig {
            executable,
            timeout,
            ..ProverConfig::default()
        });
        (directory, backend)
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_requires_a_successful_help_response_and_closed_stdin() {
        let (_directory, backend) = version_fixture(
            "if read -r line; then exit 65; fi\nprintf '\\nfixture usage\\nmore help\\n'",
            5,
        );
        assert_eq!(
            backend.version().await.unwrap(),
            "Chuffed (version unavailable; --help): fixture usage"
        );
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_rejects_failed_empty_or_stderr_only_help() {
        for (script, expected) in [
            ("printf 'usage\\n'; exit 7", "--help failed"),
            ("exit 0", "--help returned no output"),
            ("printf ' \\n\\t'", "--help returned no output"),
            ("printf 'usage\\n' >&2", "--help returned no output"),
        ] {
            let (_directory, backend) = version_fixture(script, 5);
            let error = backend.version().await.unwrap_err();
            assert!(error.to_string().contains(expected), "{error:#}");
        }
    }

    #[tokio::test]
    async fn version_rejects_a_missing_executable() {
        let directory = tempfile::tempdir().unwrap();
        let backend = ChuffedBackend::new(ProverConfig {
            executable: directory.path().join("missing-chuffed"),
            ..ProverConfig::default()
        });
        let error = backend.version().await.unwrap_err();
        assert!(error
            .to_string()
            .contains("Failed to execute fzn-chuffed --help"));
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_rejects_a_non_executable_file() {
        use std::os::unix::fs::PermissionsExt;

        let (_directory, backend) = version_fixture("printf 'usage\\n'", 5);
        std::fs::set_permissions(
            &backend.config.executable,
            std::fs::Permissions::from_mode(0o600),
        )
        .unwrap();
        let error = backend.version().await.unwrap_err();
        assert!(error
            .to_string()
            .contains("Failed to execute fzn-chuffed --help"));
    }

    #[cfg(unix)]
    fn fixture_process_running(pid: &str) -> std::io::Result<bool> {
        let output = std::process::Command::new("/bin/ps")
            .args(["-o", "stat=", "-p", pid])
            .stdin(Stdio::null())
            .output()?;
        fixture_process_state(output.status.code(), &output.stdout, &output.stderr)
    }

    #[cfg(unix)]
    fn fixture_process_state(
        exit_code: Option<i32>,
        stdout: &[u8],
        stderr: &[u8],
    ) -> std::io::Result<bool> {
        let invalid = || {
            std::io::Error::other(format!(
                "cannot inspect fixture process: ps exit={exit_code:?}, stdout={stdout:?}, stderr={stderr:?}"
            ))
        };
        if !stderr.is_empty() {
            return Err(invalid());
        }
        if exit_code == Some(1) && stdout.iter().all(u8::is_ascii_whitespace) {
            return Ok(false);
        }
        if exit_code != Some(0) {
            return Err(invalid());
        }
        let text = std::str::from_utf8(stdout).map_err(|_| invalid())?;
        let mut fields = text.split_whitespace();
        let state = fields.next().ok_or_else(invalid)?;
        if fields.next().is_some()
            || !state.as_bytes()[1..]
                .iter()
                .all(|flag| matches!(flag, b'<' | b'N' | b'L' | b's' | b'l' | b'+'))
        {
            return Err(invalid());
        }
        match state.as_bytes()[0] {
            b'Z' | b'X' => Ok(false),
            b'R' | b'S' | b'D' | b'T' | b't' | b'I' | b'W' => Ok(true),
            _ => Err(invalid()),
        }
    }

    #[cfg(unix)]
    #[test]
    fn fixture_process_state_distinguishes_termination_from_inspection_errors() {
        for state in ["R\n", "S+\n", "D\n", "T\n", "t\n", "I\n", "W\n"] {
            assert!(fixture_process_state(Some(0), state.as_bytes(), b"").unwrap());
        }
        for state in ["Z\n", "Zs\n", "X\n"] {
            assert!(!fixture_process_state(Some(0), state.as_bytes(), b"").unwrap());
        }
        assert!(!fixture_process_state(Some(1), b"", b"").unwrap());
        for (exit_code, stdout, stderr) in [
            (Some(0), b"".as_slice(), b"".as_slice()),
            (Some(0), b"S\nZ\n".as_slice(), b"".as_slice()),
            (Some(0), b"Zgarbage\n".as_slice(), b"".as_slice()),
            (Some(0), b"?\n".as_slice(), b"".as_slice()),
            (Some(0), b"\xff".as_slice(), b"".as_slice()),
            (Some(1), b"".as_slice(), b"fatal library error".as_slice()),
            (Some(1), b"Z\n".as_slice(), b"".as_slice()),
            (Some(2), b"Z\n".as_slice(), b"".as_slice()),
            (None, b"Z\n".as_slice(), b"".as_slice()),
        ] {
            assert!(fixture_process_state(exit_code, stdout, stderr).is_err());
        }
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_times_out_and_terminates_the_process() {
        use std::time::Duration;

        let (_directory, backend) =
            version_fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 30", 1);
        // Bound the regression itself if the implementation loses its deadline.
        let result = tokio::time::timeout(Duration::from_secs(3), backend.version()).await;
        let pid_path = backend.config.executable.with_extension("pid");
        let pid = std::fs::read_to_string(pid_path)
            .unwrap()
            .parse::<u32>()
            .unwrap()
            .to_string();
        // A killed but unreaped child is terminated. Tokio owns reaping;
        // PID existence (kill -0) must not impose a second cleanup deadline.
        let mut state = fixture_process_running(&pid);
        for _ in 0..50 {
            if !matches!(&state, Ok(true)) {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
            state = fixture_process_running(&pid);
        }
        // Attempt cleanup before either a liveness or inspection assertion.
        // Do not reap a child owned by Tokio.
        let cleanup = if matches!(&state, Ok(false)) {
            None
        } else {
            Some(
                std::process::Command::new("/bin/kill")
                    .args(["-9", pid.as_str()])
                    .status(),
            )
        };
        let still_running = state.unwrap_or_else(|error| {
            panic!("inspect the fixture process: {error}; cleanup attempt: {cleanup:?}")
        });
        assert!(
            !still_running,
            "the timed-out version process survived; cleanup attempt: {cleanup:?}"
        );
        let error = result
            .expect("version must enforce its own deadline")
            .unwrap_err();
        assert!(error.to_string().contains("--help timed out"));
    }
}
