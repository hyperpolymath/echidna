// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Container isolation for prover execution
//!
//! Wraps proof verification in Podman containers (rootless) with bubblewrap
//! (bwrap) as a fallback. Prevents arbitrary code execution from malicious
//! proof scripts.
//!
//! Security model:
//! - Read-only filesystem (except /tmp)
//! - No network access (`--network=none`)
//! - Memory limits (`--memory=512m` default, configurable)
//! - CPU limits (`--cpus=2` default, configurable)
//! - Timeout enforcement with SIGKILL
//! - Drop ALL capabilities (`--cap-drop=ALL`)
//! - No new privileges (`--security-opt=no-new-privileges`)
//!
//! Isolation backend selection:
//! 1. Podman (preferred, rootless)
//! 2. bubblewrap (bwrap) as lighter alternative
//! 3. Fail-safe: refuse to run proofs if neither is available

use crate::dispatcher::ProverKind;
use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use tracing::{debug, info, warn};

/// Available isolation backends
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IsolationBackend {
    /// Rootless Podman container (preferred)
    Podman,
    /// bubblewrap lightweight sandbox (fallback)
    Bubblewrap,
    /// No isolation available -- refuse to run proofs
    None,
}

/// Container execution result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionResult {
    /// Whether the proof verification succeeded (exit code 0)
    pub success: bool,
    /// Standard output captured from the container
    pub stdout: String,
    /// Standard error captured from the container
    pub stderr: String,
    /// Process exit code (None if killed by signal)
    pub exit_code: Option<i32>,
    /// Wall-clock duration in milliseconds
    pub duration_ms: u64,
    /// Whether the execution was terminated due to timeout
    pub timed_out: bool,
    /// Whether the process was killed due to OOM
    pub oom_killed: bool,
    /// Which isolation backend was used
    pub backend: IsolationBackend,
}

/// Podman-based container executor for secure prover execution.
///
/// Runs proof verification inside rootless Podman containers with strict
/// resource limits and security constraints. Falls back to bubblewrap if
/// Podman is unavailable, or refuses to run if neither is present.
pub struct PodmanExecutor {
    /// Container image to use (default: echidna-provers:latest)
    image: String,
    /// Execution timeout -- container is killed after this
    timeout: Duration,
    /// Memory limit string for Podman (e.g. "512m")
    memory_limit: String,
    /// CPU limit (number of cores)
    cpu_limit: f64,
    /// Whether to allow network access (should be false for proof checking)
    network: bool,
    /// Detected isolation backend
    backend: IsolationBackend,
}

impl Default for PodmanExecutor {
    fn default() -> Self {
        Self {
            image: "echidna-provers:latest".to_string(),
            timeout: Duration::from_secs(300), // 5 minutes
            memory_limit: "512m".to_string(),
            cpu_limit: 2.0,
            network: false, // No network for proof checking
            backend: IsolationBackend::None, // Detect on init
        }
    }
}

impl PodmanExecutor {
    /// Create a new executor and detect the available isolation backend.
    ///
    /// Checks for Podman first, then bubblewrap. If neither is found,
    /// the executor will refuse to run any proofs (fail-safe).
    pub async fn new() -> Self {
        let backend = Self::detect_backend().await;
        let executor = Self {
            backend,
            ..Self::default()
        };

        match executor.backend {
            IsolationBackend::Podman => {
                info!("Using Podman for container isolation (rootless)");
            }
            IsolationBackend::Bubblewrap => {
                warn!("Podman not available, using bubblewrap (bwrap) as fallback");
            }
            IsolationBackend::None => {
                warn!("Neither Podman nor bubblewrap available -- proof execution DISABLED");
            }
        }

        executor
    }

    /// Set container image
    pub fn with_image(mut self, image: impl Into<String>) -> Self {
        self.image = image.into();
        self
    }

    /// Set execution timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set memory limit (e.g. "512m", "2g")
    pub fn with_memory_limit(mut self, limit: impl Into<String>) -> Self {
        self.memory_limit = limit.into();
        self
    }

    /// Set CPU limit (number of cores)
    pub fn with_cpu_limit(mut self, cores: f64) -> Self {
        self.cpu_limit = cores;
        self
    }

    /// Set network access (should be false for proof checking)
    pub fn with_network(mut self, enabled: bool) -> Self {
        self.network = enabled;
        self
    }

    /// Override the isolation backend (for testing)
    pub fn with_backend(mut self, backend: IsolationBackend) -> Self {
        self.backend = backend;
        self
    }

    /// Detect the best available isolation backend.
    ///
    /// Checks Podman first, then bubblewrap, returns None if neither works.
    pub async fn detect_backend() -> IsolationBackend {
        if Self::check_podman().await {
            IsolationBackend::Podman
        } else if Self::check_bubblewrap().await {
            IsolationBackend::Bubblewrap
        } else {
            IsolationBackend::None
        }
    }

    /// Check if Podman is available and functional
    pub async fn check_podman() -> bool {
        let output = Command::new("podman")
            .arg("version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .await;

        output.map(|s| s.success()).unwrap_or(false)
    }

    /// Check if bubblewrap (bwrap) is available
    pub async fn check_bubblewrap() -> bool {
        let output = Command::new("bwrap")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .await;

        output.map(|s| s.success()).unwrap_or(false)
    }

    /// Get the current isolation backend
    pub fn backend(&self) -> IsolationBackend {
        self.backend
    }

    /// Execute a proof verification in an isolated environment.
    ///
    /// Routes to Podman or bubblewrap depending on the detected backend.
    /// Refuses to run if no isolation backend is available.
    ///
    /// # Arguments
    /// * `prover` - Which prover to use
    /// * `proof_content` - The proof file content
    /// * `_additional_files` - Optional additional files (reserved for future use)
    ///
    /// # Returns
    /// `ExecutionResult` with stdout/stderr and exit status
    pub async fn execute_proof(
        &self,
        prover: ProverKind,
        proof_content: &str,
        _additional_files: Option<HashMap<String, String>>,
    ) -> Result<ExecutionResult> {
        match self.backend {
            IsolationBackend::Podman => {
                self.execute_with_podman(prover, proof_content).await
            }
            IsolationBackend::Bubblewrap => {
                self.execute_with_bubblewrap(prover, proof_content).await
            }
            IsolationBackend::None => {
                Err(Error::Internal(
                    "No isolation backend available. Install podman or bubblewrap (bwrap) \
                     to enable proof execution. Refusing to run proofs without isolation \
                     (fail-safe policy)."
                        .to_string(),
                ))
            }
        }
    }

    /// Execute a proof using Podman (rootless container).
    async fn execute_with_podman(
        &self,
        prover: ProverKind,
        proof_content: &str,
    ) -> Result<ExecutionResult> {
        let start = std::time::Instant::now();

        let mut cmd = Command::new("podman");
        cmd.arg("run")
            .arg("--rm"); // Remove container after execution

        // Network isolation
        if !self.network {
            cmd.arg("--network=none");
        }

        // Resource limits
        cmd.arg(format!("--memory={}", self.memory_limit))
            .arg(format!("--cpus={}", self.cpu_limit))
            .arg("--pids-limit=100"); // Limit process count

        // Security hardening
        cmd.arg("--read-only") // Read-only root filesystem
            .arg("--tmpfs=/tmp:rw,noexec,nosuid,size=100m") // Writable /tmp
            .arg("--security-opt=no-new-privileges") // Prevent privilege escalation
            .arg("--cap-drop=ALL"); // Drop all capabilities

        // Timeout enforcement
        cmd.arg(format!("--timeout={}", self.timeout.as_secs()));

        // Working directory
        cmd.arg("-w").arg("/workspace");

        // Environment variables
        cmd.arg("-e")
            .arg(format!("PROVER={}", prover_to_env_name(prover)));

        // Write proof content via stdin
        cmd.arg("-i") // Interactive mode for stdin
            .arg(&self.image)
            .arg("sh")
            .arg("-c");

        // Command to execute inside container: save proof, run prover
        let container_cmd = format!(
            "cat > /tmp/proof{ext} && {cmd} /tmp/proof{ext}",
            ext = prover_extension(prover),
            cmd = prover_command(prover),
        );
        cmd.arg(&container_cmd);

        // Set up I/O
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        info!(
            "Executing {} proof in Podman container (timeout: {}s, memory: {}, cpus: {})",
            prover.display_name(),
            self.timeout.as_secs(),
            self.memory_limit,
            self.cpu_limit,
        );

        let mut child = cmd.spawn().map_err(|e| {
            Error::Internal(format!("Failed to spawn Podman container: {}", e))
        })?;

        // Write proof content to stdin
        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(proof_content.as_bytes())
                .await
                .map_err(|e| {
                    Error::Internal(format!("Failed to write to container stdin: {}", e))
                })?;
            stdin.shutdown().await.ok(); // Close stdin
        }

        // Wait for completion with timeout
        let wait_result =
            tokio::time::timeout(self.timeout + Duration::from_secs(5), child.wait_with_output())
                .await;

        let duration = start.elapsed();

        match wait_result {
            Ok(Ok(output)) => {
                let success = output.status.success();
                let exit_code = output.status.code();
                let stdout = String::from_utf8_lossy(&output.stdout).to_string();
                let stderr = String::from_utf8_lossy(&output.stderr).to_string();

                debug!(
                    "Podman container finished: exit={:?}, stdout={}B, stderr={}B",
                    exit_code,
                    stdout.len(),
                    stderr.len(),
                );

                Ok(ExecutionResult {
                    success,
                    stdout,
                    stderr,
                    exit_code,
                    duration_ms: duration.as_millis() as u64,
                    timed_out: false,
                    oom_killed: exit_code == Some(137), // SIGKILL (OOM)
                    backend: IsolationBackend::Podman,
                })
            }
            Ok(Err(e)) => Err(Error::Internal(format!(
                "Podman container execution failed: {}",
                e
            ))),
            Err(_) => {
                // Timeout exceeded even the grace period
                warn!(
                    "Podman container timed out after {}s",
                    self.timeout.as_secs()
                );
                // child is consumed by wait_with_output, so we cannot kill it
                // here. Podman's --timeout flag handles the kill for us.

                Ok(ExecutionResult {
                    success: false,
                    stdout: String::new(),
                    stderr: format!(
                        "Execution timed out after {}s",
                        self.timeout.as_secs()
                    ),
                    exit_code: None,
                    duration_ms: duration.as_millis() as u64,
                    timed_out: true,
                    oom_killed: false,
                    backend: IsolationBackend::Podman,
                })
            }
        }
    }

    /// Execute a proof using bubblewrap (bwrap) as a lighter alternative.
    ///
    /// Provides filesystem isolation, read-only root, and timeout enforcement
    /// but without the full container namespace isolation of Podman.
    async fn execute_with_bubblewrap(
        &self,
        prover: ProverKind,
        proof_content: &str,
    ) -> Result<ExecutionResult> {
        let start = std::time::Instant::now();

        // Create a temp directory for the proof file
        let temp_dir = tempfile::tempdir().map_err(|e| {
            Error::Internal(format!("Failed to create temp directory: {}", e))
        })?;
        let proof_path = temp_dir
            .path()
            .join(format!("proof{}", prover_extension(prover)));

        // Write proof content to temp file
        tokio::fs::write(&proof_path, proof_content).await.map_err(|e| {
            Error::Internal(format!("Failed to write proof file: {}", e))
        })?;

        // Build bwrap command
        let mut cmd = Command::new("bwrap");
        cmd.arg("--ro-bind")
            .arg("/usr")
            .arg("/usr") // Read-only /usr
            .arg("--ro-bind")
            .arg("/lib")
            .arg("/lib") // Read-only /lib
            .arg("--ro-bind")
            .arg("/lib64")
            .arg("/lib64") // Read-only /lib64 (if exists)
            .arg("--ro-bind")
            .arg("/bin")
            .arg("/bin") // Read-only /bin
            .arg("--ro-bind")
            .arg("/sbin")
            .arg("/sbin") // Read-only /sbin
            .arg("--tmpfs")
            .arg("/tmp") // Writable /tmp
            .arg("--proc")
            .arg("/proc") // proc filesystem
            .arg("--dev")
            .arg("/dev") // dev filesystem
            .arg("--ro-bind")
            .arg(temp_dir.path())
            .arg("/workspace") // Mount proof dir read-only
            .arg("--unshare-all") // Unshare all namespaces
            .arg("--die-with-parent") // Kill sandbox when parent dies
            .arg("--new-session"); // New session

        // Network isolation (unshare-net is included in unshare-all)

        // Set environment
        cmd.arg("--setenv")
            .arg("PROVER")
            .arg(prover_to_env_name(prover));

        // Command to run inside sandbox
        let prover_cmd = prover_command(prover);
        cmd.arg("sh")
            .arg("-c")
            .arg(format!(
                "cp /workspace/proof{ext} /tmp/proof{ext} && {cmd} /tmp/proof{ext}",
                ext = prover_extension(prover),
                cmd = prover_cmd,
            ));

        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

        info!(
            "Executing {} proof in bubblewrap sandbox (timeout: {}s)",
            prover.display_name(),
            self.timeout.as_secs(),
        );

        let mut child = cmd.spawn().map_err(|e| {
            Error::Internal(format!("Failed to spawn bubblewrap sandbox: {}", e))
        })?;

        // Wait with timeout. We use wait() instead of wait_with_output()
        // so we can kill the child on timeout.
        let wait_result =
            tokio::time::timeout(self.timeout, child.wait()).await;

        let duration = start.elapsed();

        match wait_result {
            Ok(Ok(status)) => {
                let success = status.success();
                let exit_code = status.code();

                debug!(
                    "Bubblewrap sandbox finished: exit={:?}",
                    exit_code,
                );

                Ok(ExecutionResult {
                    success,
                    stdout: String::new(),
                    stderr: String::new(),
                    exit_code,
                    duration_ms: duration.as_millis() as u64,
                    timed_out: false,
                    oom_killed: exit_code == Some(137),
                    backend: IsolationBackend::Bubblewrap,
                })
            }
            Ok(Err(e)) => Err(Error::Internal(format!(
                "Bubblewrap sandbox execution failed: {}",
                e
            ))),
            Err(_) => {
                warn!(
                    "Bubblewrap sandbox timed out after {}s, killing",
                    self.timeout.as_secs()
                );
                let _ = child.kill().await;

                Ok(ExecutionResult {
                    success: false,
                    stdout: String::new(),
                    stderr: format!(
                        "Execution timed out after {}s",
                        self.timeout.as_secs()
                    ),
                    exit_code: None,
                    duration_ms: duration.as_millis() as u64,
                    timed_out: true,
                    oom_killed: false,
                    backend: IsolationBackend::Bubblewrap,
                })
            }
        }
    }

    /// Pull the container image if not already present (Podman only).
    pub async fn ensure_image(&self) -> Result<()> {
        if self.backend != IsolationBackend::Podman {
            debug!("Image pull skipped: not using Podman backend");
            return Ok(());
        }

        info!("Checking for container image: {}", self.image);

        let check = Command::new("podman")
            .args(["image", "inspect", &self.image])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .await;

        match check {
            Ok(status) if status.success() => {
                debug!("Image {} already present", self.image);
                Ok(())
            }
            _ => {
                info!("Pulling container image: {}", self.image);
                let output = Command::new("podman")
                    .args(["pull", &self.image])
                    .output()
                    .await
                    .map_err(|e| {
                        Error::Internal(format!("Failed to pull container image: {}", e))
                    })?;

                if output.status.success() {
                    info!("Successfully pulled image: {}", self.image);
                    Ok(())
                } else {
                    Err(Error::Internal(format!(
                        "Failed to pull image: {}",
                        String::from_utf8_lossy(&output.stderr)
                    )))
                }
            }
        }
    }

    /// Build Podman command-line arguments for inspection/testing.
    ///
    /// Returns the full argument list that would be passed to Podman.
    pub fn build_podman_args(&self, prover: ProverKind) -> Vec<String> {
        let mut args = vec![
            "run".to_string(),
            "--rm".to_string(),
        ];

        if !self.network {
            args.push("--network=none".to_string());
        }

        args.push(format!("--memory={}", self.memory_limit));
        args.push(format!("--cpus={}", self.cpu_limit));
        args.push("--pids-limit=100".to_string());
        args.push("--read-only".to_string());
        args.push("--tmpfs=/tmp:rw,noexec,nosuid,size=100m".to_string());
        args.push("--security-opt=no-new-privileges".to_string());
        args.push("--cap-drop=ALL".to_string());
        args.push(format!("--timeout={}", self.timeout.as_secs()));
        args.push("-w".to_string());
        args.push("/workspace".to_string());
        args.push("-e".to_string());
        args.push(format!("PROVER={}", prover_to_env_name(prover)));
        args.push("-i".to_string());
        args.push(self.image.clone());
        args.push("sh".to_string());
        args.push("-c".to_string());

        let container_cmd = format!(
            "cat > /tmp/proof{ext} && {cmd} /tmp/proof{ext}",
            ext = prover_extension(prover),
            cmd = prover_command(prover),
        );
        args.push(container_cmd);

        args
    }
}

// =============================================================================
// Prover Mapping Helpers
// =============================================================================

/// Get environment variable name for a prover backend.
fn prover_to_env_name(prover: ProverKind) -> &'static str {
    match prover {
        ProverKind::Coq => "COQ",
        ProverKind::Lean => "LEAN",
        ProverKind::Isabelle => "ISABELLE",
        ProverKind::Agda => "AGDA",
        ProverKind::Z3 => "Z3",
        ProverKind::Cvc5 => "CVC5",
        ProverKind::Metamath => "METAMATH",
        ProverKind::HolLight => "HOL_LIGHT",
        ProverKind::Mizar => "MIZAR",
        ProverKind::Pvs => "PVS",
        ProverKind::Acl2 => "ACL2",
        ProverKind::Hol4 => "HOL4",
    }
}

/// Get the file extension for proof files of a given prover.
fn prover_extension(prover: ProverKind) -> &'static str {
    match prover {
        ProverKind::Coq => ".v",
        ProverKind::Lean => ".lean",
        ProverKind::Isabelle => ".thy",
        ProverKind::Agda => ".agda",
        ProverKind::Z3 => ".smt2",
        ProverKind::Cvc5 => ".smt2",
        ProverKind::Metamath => ".mm",
        ProverKind::HolLight => ".ml",
        ProverKind::Mizar => ".miz",
        ProverKind::Pvs => ".pvs",
        ProverKind::Acl2 => ".lisp",
        ProverKind::Hol4 => ".sml",
    }
}

/// Get the shell command to invoke a prover.
fn prover_command(prover: ProverKind) -> &'static str {
    match prover {
        ProverKind::Coq => "coqc",
        ProverKind::Lean => "lean",
        ProverKind::Isabelle => "isabelle build",
        ProverKind::Agda => "agda",
        ProverKind::Z3 => "z3",
        ProverKind::Cvc5 => "cvc5",
        ProverKind::Metamath => "metamath",
        ProverKind::HolLight => "ocaml",
        ProverKind::Mizar => "mizf",
        ProverKind::Pvs => "pvs",
        ProverKind::Acl2 => "acl2",
        ProverKind::Hol4 => "Holmake",
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prover_extensions() {
        assert_eq!(prover_extension(ProverKind::Coq), ".v");
        assert_eq!(prover_extension(ProverKind::Lean), ".lean");
        assert_eq!(prover_extension(ProverKind::Metamath), ".mm");
        assert_eq!(prover_extension(ProverKind::Z3), ".smt2");
        assert_eq!(prover_extension(ProverKind::Agda), ".agda");
    }

    #[test]
    fn test_prover_env_names() {
        assert_eq!(prover_to_env_name(ProverKind::Coq), "COQ");
        assert_eq!(prover_to_env_name(ProverKind::HolLight), "HOL_LIGHT");
        assert_eq!(prover_to_env_name(ProverKind::Cvc5), "CVC5");
    }

    #[test]
    fn test_prover_commands() {
        assert_eq!(prover_command(ProverKind::Coq), "coqc");
        assert_eq!(prover_command(ProverKind::Lean), "lean");
        assert_eq!(prover_command(ProverKind::Z3), "z3");
    }

    #[test]
    fn test_default_executor() {
        let executor = PodmanExecutor::default();
        assert_eq!(executor.image, "echidna-provers:latest");
        assert_eq!(executor.timeout, Duration::from_secs(300));
        assert_eq!(executor.memory_limit, "512m");
        assert_eq!(executor.cpu_limit, 2.0);
        assert!(!executor.network);
        assert_eq!(executor.backend, IsolationBackend::None);
    }

    #[test]
    fn test_builder_pattern() {
        let executor = PodmanExecutor::default()
            .with_image("custom-provers:v2")
            .with_timeout(Duration::from_secs(600))
            .with_memory_limit("2g")
            .with_cpu_limit(4.0)
            .with_network(false)
            .with_backend(IsolationBackend::Podman);

        assert_eq!(executor.image, "custom-provers:v2");
        assert_eq!(executor.timeout, Duration::from_secs(600));
        assert_eq!(executor.memory_limit, "2g");
        assert_eq!(executor.cpu_limit, 4.0);
        assert!(!executor.network);
        assert_eq!(executor.backend, IsolationBackend::Podman);
    }

    #[test]
    fn test_podman_args_contain_security_flags() {
        let executor = PodmanExecutor::default()
            .with_backend(IsolationBackend::Podman);

        let args = executor.build_podman_args(ProverKind::Coq);

        assert!(args.contains(&"--rm".to_string()));
        assert!(args.contains(&"--network=none".to_string()));
        assert!(args.contains(&"--read-only".to_string()));
        assert!(args.contains(&"--cap-drop=ALL".to_string()));
        assert!(args.contains(&"--security-opt=no-new-privileges".to_string()));
        assert!(args.contains(&"--pids-limit=100".to_string()));
        assert!(args.contains(&"--memory=512m".to_string()));
        assert!(args.contains(&"--cpus=2".to_string()));
        assert!(args.contains(&"--timeout=300".to_string()));
    }

    #[test]
    fn test_podman_args_contain_prover_env() {
        let executor = PodmanExecutor::default()
            .with_backend(IsolationBackend::Podman);

        let args = executor.build_podman_args(ProverKind::Lean);
        assert!(args.contains(&"PROVER=LEAN".to_string()));

        let args = executor.build_podman_args(ProverKind::Coq);
        assert!(args.contains(&"PROVER=COQ".to_string()));
    }

    #[test]
    fn test_podman_args_network_enabled() {
        let executor = PodmanExecutor::default()
            .with_network(true)
            .with_backend(IsolationBackend::Podman);

        let args = executor.build_podman_args(ProverKind::Z3);
        assert!(!args.contains(&"--network=none".to_string()));
    }

    #[tokio::test]
    async fn test_no_backend_fails_safe() {
        let executor = PodmanExecutor::default()
            .with_backend(IsolationBackend::None);

        let result = executor
            .execute_proof(ProverKind::Coq, "Theorem test : True.", None)
            .await;

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("No isolation backend available"),
            "Expected fail-safe error, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_execution_result_fields() {
        let result = ExecutionResult {
            success: true,
            stdout: "All proofs verified".to_string(),
            stderr: String::new(),
            exit_code: Some(0),
            duration_ms: 1234,
            timed_out: false,
            oom_killed: false,
            backend: IsolationBackend::Podman,
        };

        assert!(result.success);
        assert_eq!(result.exit_code, Some(0));
        assert!(!result.timed_out);
        assert!(!result.oom_killed);
        assert_eq!(result.backend, IsolationBackend::Podman);
    }

    #[test]
    fn test_timeout_result() {
        let result = ExecutionResult {
            success: false,
            stdout: String::new(),
            stderr: "Execution timed out after 300s".to_string(),
            exit_code: None,
            duration_ms: 300_000,
            timed_out: true,
            oom_killed: false,
            backend: IsolationBackend::Podman,
        };

        assert!(!result.success);
        assert!(result.timed_out);
        assert!(result.exit_code.is_none());
    }

    #[test]
    fn test_oom_killed_detection() {
        let result = ExecutionResult {
            success: false,
            stdout: String::new(),
            stderr: "Killed".to_string(),
            exit_code: Some(137),
            duration_ms: 5000,
            timed_out: false,
            oom_killed: true,
            backend: IsolationBackend::Bubblewrap,
        };

        assert!(!result.success);
        assert!(result.oom_killed);
        assert_eq!(result.exit_code, Some(137));
    }
}
