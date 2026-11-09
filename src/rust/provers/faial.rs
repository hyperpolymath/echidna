// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Faial — lightweight GPU data-race detector backend.
//!
//! Faial (from PLDI 2020, "Faial: Formalizing GPU Access Pattern Analysis")
//! checks CUDA kernels for data-race freedom via access pattern analysis. It
//! is lighter-weight than GPUVerify: rather than translating to Boogie/BPL
//! it directly analyses thread-access sets and shared-memory patterns.
//!
//! Invocation: `faial-drf <file.cu>` (data-race freedom check).
//!
//! Success signal: output contains `"no races"` or the process exits with
//! code 0 and no race-indicating phrases.
//! Failure signal: output contains `"race"` with a non-diagnostic context,
//! or the process exits non-zero.
//!
//! Corpus source: Faial's `tests/` directory and any CUDA benchmarks
//! annotated with `__shared__` declarations (GPU shared-memory is the
//! primary race surface Faial reasons about).

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Backend wrapping the `faial-drf` command-line tool.
///
/// Faial-DRF (data-race freedom) accepts a single `.cu` CUDA source file
/// and determines whether concurrent threads can produce conflicting
/// accesses to shared-memory locations.
pub struct FaialBackend {
    /// Backend configuration (executable path, timeout, extra flags).
    config: ProverConfig,
}

impl FaialBackend {
    /// Create a new Faial backend with the given configuration.
    pub fn new(config: ProverConfig) -> Self {
        FaialBackend { config }
    }

    /// Return the path to the `faial-drf` executable.
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("faial-drf")
        } else {
            self.config.executable.clone()
        }
    }

    /// Extract `__global__ void <name>` kernel names from CUDA source.
    ///
    /// These become individual goals in the proof state, one per kernel,
    /// so that training data records are per-kernel rather than per-file.
    fn extract_kernel_names(content: &str) -> Vec<String> {
        let mut names = Vec::new();
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.contains("__global__") && trimmed.contains("void") {
                if let Some(name) = Self::extract_function_name(trimmed) {
                    names.push(name);
                }
            }
        }
        names
    }

    /// Extract the identifier between `void` and `(` on a line.
    fn extract_function_name(line: &str) -> Option<String> {
        let after_void = line.find("void").map(|pos| &line[pos + 4..])?;
        let trimmed = after_void.trim_start();
        let end = trimmed.find(|c: char| !c.is_alphanumeric() && c != '_')?;
        let name = &trimmed[..end];
        if name.is_empty() {
            None
        } else {
            Some(name.to_string())
        }
    }

    /// Extract `__shared__` variable declarations as context axioms.
    ///
    /// Shared-memory declarations are the primary race surface in CUDA
    /// kernels; recording them as axioms lets the training model learn
    /// which memory spaces are relevant for a given proof goal.
    fn extract_shared_declarations(content: &str) -> Vec<String> {
        content
            .lines()
            .map(str::trim)
            .filter(|line| line.contains("__shared__"))
            .map(|line| line.to_string())
            .collect()
    }

    /// Parse Faial output and exit code to determine race freedom.
    ///
    /// - `"no races"` → true (race-free)
    /// - `"race"` in output (excluding "no races" context) → false
    /// - Exit code 0 with no race phrases → true
    /// - Non-zero exit code → false
    fn parse_output(&self, stdout: &str, stderr: &str, success: bool) -> bool {
        let combined = format!("{}\n{}", stdout, stderr).to_lowercase();
        if combined.contains("no races") || combined.contains("no data races") {
            return true;
        }
        if combined.contains("race") {
            return false;
        }
        // Fall back to exit code.
        success
    }
}

#[async_trait]
impl ProverBackend for FaialBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Faial
    }

    async fn version(&self) -> Result<String> {
        // Version discovery is a short availability probe, not a proof run.
        let limit = std::time::Duration::from_secs(self.config.timeout.min(10));
        let mut command = Command::new(self.binary());
        command
            .arg("--version")
            .stdin(Stdio::null())
            .kill_on_drop(true);
        let output = tokio::time::timeout(limit, command.output())
            .await
            .with_context(|| format!("Faial: --version timed out after {}s", limit.as_secs()))?
            .context("Faial: failed to execute --version")?;
        if !output.status.success() {
            return Err(anyhow!("Faial: --version exited with {}", output.status));
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let version = format!("{}\n{}", stdout, stderr).trim().to_string();
        if version.is_empty() {
            return Err(anyhow!("Faial: --version returned empty output"));
        }
        Ok(version)
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("Faial: reading {}", path.display()))?;
        let mut state = self.parse_string(&content).await?;
        // Store file path so verify_proof can call faial-drf directly.
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let kernel_names = Self::extract_kernel_names(content);
        let shared_decls = Self::extract_shared_declarations(content);

        // Each kernel → one Goal named "race_free(<kernel>)".
        let goals: Vec<Goal> = if kernel_names.is_empty() {
            vec![Goal {
                id: "faial-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }]
        } else {
            kernel_names
                .iter()
                .map(|name| Goal {
                    id: format!("kernel_{}", name),
                    target: Term::Const(format!("data_race_free({})", name)),
                    hypotheses: vec![],
                })
                .collect()
        };

        // Shared-memory declarations become context axioms.
        let mut ctx = ProofContext::default();
        ctx.axioms.extend(shared_decls);

        let mut state = ProofState {
            goals,
            context: ctx,
            proof_script: vec![],
            metadata: Default::default(),
        };
        state.metadata.insert(
            "faial_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // Faial is fully automated; tactics are annotation / synchronisation hints.
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let source = state
            .metadata
            .get("faial_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();

        // Prefer the original source path if available.
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let out = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 10),
                Command::new(self.binary())
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| anyhow!("Faial timed out after {} s", self.config.timeout))?
            .context("Faial: binary not runnable")?;

            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr);
            return Ok(self.parse_output(&stdout, &stderr, out.status.success()));
        }

        // Write source to a temporary .cu file.
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-faial-")
            .tempdir()
            .context("Faial: tempdir")?;
        let input_path = tmp_dir.path().join("kernel.cu");
        tokio::fs::write(&input_path, source.as_bytes())
            .await
            .context("Faial: writing temp source")?;

        let mut cmd = Command::new(self.binary());
        cmd.arg(&input_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        let out = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            cmd.output(),
        )
        .await
        .map_err(|_| anyhow!("Faial timed out after {} s", self.config.timeout))?
        .context("Faial: binary not runnable")?;

        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        Ok(self.parse_output(&stdout, &stderr, out.status.success()))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        // Export the raw CUDA source stored during parse_string.
        Ok(state
            .metadata
            .get("faial_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default())
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Synchronisation and atomics are the primary remediation vocabulary
        // for race conditions found by Faial.
        let tactics = vec![
            Tactic::Custom {
                prover: "faial".to_string(),
                command: "__syncthreads".to_string(),
                args: vec![],
            },
            Tactic::Custom {
                prover: "faial".to_string(),
                command: "atomicAdd".to_string(),
                args: vec!["&shared[idx]".to_string(), "val".to_string()],
            },
            Tactic::Custom {
                prover: "faial".to_string(),
                command: "atomicCAS".to_string(),
                args: vec![
                    "&shared[idx]".to_string(),
                    "expected".to_string(),
                    "desired".to_string(),
                ],
            },
            Tactic::Custom {
                prover: "faial".to_string(),
                command: "__shared__".to_string(),
                args: vec!["float buf[BLOCK_SIZE]".to_string()],
            },
            Tactic::Custom {
                prover: "faial".to_string(),
                command: "threadIdx".to_string(),
                args: vec!["x".to_string()],
            },
        ];
        Ok(crate::provers::gnn_augment_tactics(&self.config, state, "faial", tactics, limit).await)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Return synchronisation primitives that match the pattern.
        let pat_lower = pattern.to_lowercase();
        let candidates = vec![
            "__syncthreads".to_string(),
            "atomicAdd".to_string(),
            "atomicCAS".to_string(),
            "atomicExch".to_string(),
            "__shared__".to_string(),
        ];
        Ok(candidates
            .into_iter()
            .filter(|c| c.to_lowercase().contains(&pat_lower))
            .collect())
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
    async fn version_rejects_a_missing_executable() {
        let directory = tempfile::tempdir().unwrap();
        let backend = FaialBackend::new(ProverConfig {
            executable: directory.path().join("missing-prover"),
            timeout: 5,
            ..ProverConfig::default()
        });
        let error = backend.version().await.unwrap_err();
        assert!(error.to_string().contains("failed to execute --version"));
    }

    #[cfg(unix)]
    fn version_fixture(script: &str, timeout: u64) -> (tempfile::TempDir, FaialBackend) {
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("version-probe");
        crate::provers::test_fixture::write_executable(
            &executable,
            &format!(
                "#!/bin/sh\n[ \"$#\" -eq 1 ] && [ \"$1\" = '--version' ] || exit 64\n{script}\n"
            ),
        );
        let backend = FaialBackend::new(ProverConfig {
            executable,
            timeout,
            ..ProverConfig::default()
        });
        (directory, backend)
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_accepts_successful_stdout_or_stderr() {
        for script in [
            "printf 'fixture version 1.2\\n'",
            "printf 'fixture version 1.2\\n' >&2",
        ] {
            let (_directory, backend) = version_fixture(script, 5);
            assert_eq!(backend.version().await.unwrap(), "fixture version 1.2");
        }
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_rejects_failed_or_empty_output() {
        for (script, expected) in [
            ("printf 'fixture version 1.2\\n'; exit 7", "exited with"),
            ("exit 0", "empty output"),
            ("printf ' \\n\\t'; printf '\\n ' >&2", "empty output"),
        ] {
            let (_directory, backend) = version_fixture(script, 5);
            let error = backend.version().await.unwrap_err();
            assert!(error.to_string().contains(expected), "{error:#}");
        }
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn version_rejects_a_non_executable_file() {
        use std::os::unix::fs::PermissionsExt;

        let (_directory, backend) = version_fixture("printf 'fixture version 1.2\\n'", 5);
        std::fs::set_permissions(backend.binary(), std::fs::Permissions::from_mode(0o600)).unwrap();
        let error = backend.version().await.unwrap_err();
        assert!(error.to_string().contains("failed to execute --version"));
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
        let pid_path = backend.binary().with_extension("pid");
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
        assert!(error.to_string().contains("--version timed out"));
    }

    #[test]
    fn kind_is_faial() {
        let backend = FaialBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::Faial);
    }

    #[test]
    fn extract_kernel_names_single() {
        let src = r#"
__global__ void reduce(float* d_in, float* d_out) {
    __shared__ float sdata[256];
    sdata[threadIdx.x] = d_in[threadIdx.x];
    __syncthreads();
    d_out[0] = sdata[0];
}
"#;
        let names = FaialBackend::extract_kernel_names(src);
        assert_eq!(names, vec!["reduce"]);
    }

    #[test]
    fn extract_kernel_names_multiple() {
        let src = r#"
__global__ void kernelA(float* a) { a[threadIdx.x] = 0.0f; }
__global__ void kernelB(float* a, float* b) { b[threadIdx.x] = a[threadIdx.x]; }
"#;
        let names = FaialBackend::extract_kernel_names(src);
        assert_eq!(names, vec!["kernelA", "kernelB"]);
    }

    #[test]
    fn extract_kernel_names_none() {
        let src = "int main() { return 0; }";
        assert!(FaialBackend::extract_kernel_names(src).is_empty());
    }

    #[test]
    fn extract_shared_declarations() {
        let src = r#"
__global__ void foo(float* a) {
    __shared__ float buf[128];
    __shared__ int lock;
    buf[threadIdx.x] = a[threadIdx.x];
}
"#;
        let decls = FaialBackend::extract_shared_declarations(src);
        assert_eq!(decls.len(), 2);
        assert!(decls[0].contains("buf"));
        assert!(decls[1].contains("lock"));
    }

    #[tokio::test]
    async fn parse_string_produces_goals_and_axioms() {
        let backend = FaialBackend::new(ProverConfig::default());
        let src = r#"
__global__ void myKernel(float* a) {
    __shared__ float buf[256];
    buf[threadIdx.x] = a[threadIdx.x];
    __syncthreads();
    a[0] = buf[0];
}
"#;
        let state = backend.parse_string(src).await.unwrap();
        // One kernel → one goal.
        assert_eq!(state.goals.len(), 1);
        assert_eq!(state.goals[0].id, "kernel_myKernel");
        assert!(state.goals[0].target.to_string().contains("data_race_free"));
        // __shared__ line → one axiom.
        assert_eq!(state.context.axioms.len(), 1);
        assert!(state.context.axioms[0].contains("__shared__"));
    }

    #[tokio::test]
    async fn parse_string_no_kernels_fallback() {
        let backend = FaialBackend::new(ProverConfig::default());
        let src = "int x = 0;";
        let state = backend.parse_string(src).await.unwrap();
        assert_eq!(state.goals.len(), 1);
        assert_eq!(state.goals[0].id, "faial-file");
    }

    #[test]
    fn parse_output_no_races() {
        let backend = FaialBackend::new(ProverConfig::default());
        assert!(backend.parse_output("no races detected\n", "", true));
    }

    #[test]
    fn parse_output_race_found() {
        let backend = FaialBackend::new(ProverConfig::default());
        assert!(!backend.parse_output("race between thread 0 and thread 1\n", "", false));
    }

    #[test]
    fn parse_output_exit_code_fallback_success() {
        let backend = FaialBackend::new(ProverConfig::default());
        // Empty output + exit 0 → race-free.
        assert!(backend.parse_output("", "", true));
    }

    #[test]
    fn parse_output_exit_code_fallback_failure() {
        let backend = FaialBackend::new(ProverConfig::default());
        // Empty output + exit 1 → not race-free.
        assert!(!backend.parse_output("", "", false));
    }

    #[tokio::test]
    async fn suggest_tactics_returns_five() {
        let backend = FaialBackend::new(ProverConfig::default());
        let state = ProofState::default();
        let tactics = backend.suggest_tactics(&state, 5).await.unwrap();
        assert_eq!(tactics.len(), 5);
    }

    #[tokio::test]
    async fn search_theorems_filters() {
        let backend = FaialBackend::new(ProverConfig::default());
        let results = backend.search_theorems("atomic").await.unwrap();
        assert!(results.iter().any(|s| s.starts_with("atomic")));
        assert!(!results.iter().any(|s| s == "__syncthreads"));
    }
}
