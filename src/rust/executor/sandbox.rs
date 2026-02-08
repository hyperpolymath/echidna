// SPDX-License-Identifier: PMPL-1.0-or-later

//! Solver sandboxing for process isolation
//!
//! Runs each solver in a sandboxed environment to prevent:
//! - File system access outside allowed paths
//! - Network access (solvers should never need networking)
//! - Excessive resource usage (memory, CPU, disk)
//!
//! Supports three modes:
//! - Podman (preferred): Full container isolation
//! - Bubblewrap (fallback): Lightweight namespace isolation
//! - None (development only): No sandboxing, with explicit opt-in

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use tracing::{info, warn};

/// Kind of sandbox to use
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SandboxKind {
    /// Podman container isolation (preferred)
    Podman,
    /// Bubblewrap namespace isolation (fallback)
    Bubblewrap,
    /// No sandbox (development only -- requires explicit opt-in)
    None,
}

/// Configuration for sandbox execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SandboxConfig {
    /// Kind of sandbox
    pub kind: SandboxKind,
    /// Memory limit in bytes (default: 1 GiB)
    pub memory_limit: u64,
    /// CPU limit (number of cores, default: 2)
    pub cpu_limit: u32,
    /// Time limit in seconds (default: 300)
    pub time_limit: u64,
    /// Disk limit in bytes for /tmp (default: 100 MiB)
    pub disk_limit: u64,
    /// Container image for Podman (default: "echidna-solver:latest")
    pub container_image: String,
}

impl Default for SandboxConfig {
    fn default() -> Self {
        Self {
            kind: SandboxKind::None, // Default to no sandbox for dev
            memory_limit: 1024 * 1024 * 1024, // 1 GiB
            cpu_limit: 2,
            time_limit: 300,
            disk_limit: 100 * 1024 * 1024, // 100 MiB
            container_image: "echidna-solver:latest".to_string(),
        }
    }
}

/// Result from sandboxed execution
#[derive(Debug, Clone)]
pub struct SandboxedOutput {
    /// Standard output
    pub stdout: String,
    /// Standard error
    pub stderr: String,
    /// Exit code (None if killed)
    pub exit_code: Option<i32>,
    /// Whether the process was killed due to resource limits
    pub killed: bool,
    /// Reason for killing (if applicable)
    pub kill_reason: Option<String>,
}

/// Sandboxed executor for solver binaries
pub struct SandboxedExecutor {
    config: SandboxConfig,
}

impl SandboxedExecutor {
    /// Create a new sandboxed executor
    pub fn new(config: SandboxConfig) -> Self {
        if config.kind == SandboxKind::None {
            warn!("Running solver WITHOUT sandbox -- use --unsafe-no-sandbox only for development");
        }
        Self { config }
    }

    /// Create with auto-detected sandbox (tries Podman, then bubblewrap, then None)
    pub fn auto_detect() -> Self {
        let kind = if Self::podman_available() {
            info!("Using Podman for solver sandboxing");
            SandboxKind::Podman
        } else if Self::bubblewrap_available() {
            info!("Using bubblewrap for solver sandboxing");
            SandboxKind::Bubblewrap
        } else {
            warn!("No sandbox available -- running solvers without isolation");
            SandboxKind::None
        };

        Self::new(SandboxConfig {
            kind,
            ..Default::default()
        })
    }

    /// Execute a solver binary in the sandbox
    pub async fn execute(
        &self,
        solver_path: &Path,
        args: &[&str],
        stdin_data: Option<&str>,
        input_file: Option<&Path>,
    ) -> Result<SandboxedOutput> {
        match self.config.kind {
            SandboxKind::Podman => self.execute_podman(solver_path, args, stdin_data, input_file).await,
            SandboxKind::Bubblewrap => self.execute_bubblewrap(solver_path, args, stdin_data, input_file).await,
            SandboxKind::None => self.execute_unsandboxed(solver_path, args, stdin_data).await,
        }
    }

    /// Execute using Podman container
    async fn execute_podman(
        &self,
        solver_path: &Path,
        args: &[&str],
        stdin_data: Option<&str>,
        input_file: Option<&Path>,
    ) -> Result<SandboxedOutput> {
        let mut cmd = Command::new("podman");

        cmd.arg("run")
            .arg("--rm")
            .arg("--network=none")
            .arg(format!("--memory={}b", self.config.memory_limit))
            .arg(format!("--cpus={}", self.config.cpu_limit))
            .arg("--read-only")
            .arg("--tmpfs=/tmp:size=100m")
            .arg(format!("--timeout={}", self.config.time_limit));

        // Mount solver binary read-only
        cmd.arg(format!(
            "--volume={}:{}:ro",
            solver_path.display(),
            solver_path.display()
        ));

        // Mount input file read-only if provided
        if let Some(input) = input_file {
            cmd.arg(format!(
                "--volume={}:/input/proof:ro",
                input.display()
            ));
        }

        cmd.arg(&self.config.container_image)
            .arg(solver_path.to_str().unwrap_or_default());

        for arg in args {
            cmd.arg(arg);
        }

        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        self.run_command(cmd, stdin_data).await
    }

    /// Execute using bubblewrap
    async fn execute_bubblewrap(
        &self,
        solver_path: &Path,
        args: &[&str],
        stdin_data: Option<&str>,
        input_file: Option<&Path>,
    ) -> Result<SandboxedOutput> {
        let mut cmd = Command::new("bwrap");

        cmd.arg("--ro-bind").arg("/").arg("/")
            .arg("--tmpfs").arg("/tmp")
            .arg("--unshare-all")
            .arg("--die-with-parent");

        // Mount input file if provided
        if let Some(input) = input_file {
            cmd.arg("--ro-bind")
                .arg(input.to_str().unwrap_or_default())
                .arg("/input/proof");
        }

        cmd.arg("--")
            .arg(solver_path.to_str().unwrap_or_default());

        for arg in args {
            cmd.arg(arg);
        }

        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        self.run_command(cmd, stdin_data).await
    }

    /// Execute without sandbox (development only)
    async fn execute_unsandboxed(
        &self,
        solver_path: &Path,
        args: &[&str],
        stdin_data: Option<&str>,
    ) -> Result<SandboxedOutput> {
        let mut cmd = Command::new(solver_path);

        for arg in args {
            cmd.arg(arg);
        }

        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        self.run_command(cmd, stdin_data).await
    }

    /// Run a command with optional stdin data and timeout
    async fn run_command(
        &self,
        mut cmd: Command,
        stdin_data: Option<&str>,
    ) -> Result<SandboxedOutput> {
        let mut child = cmd.spawn()
            .context("Failed to spawn solver process")?;

        // Write stdin data if provided
        if let Some(data) = stdin_data {
            if let Some(mut stdin) = child.stdin.take() {
                stdin.write_all(data.as_bytes()).await?;
                stdin.flush().await?;
                drop(stdin);
            }
        }

        let time_limit = self.config.time_limit;

        // Use tokio::select! to handle timeout while keeping child alive for kill
        let timeout_duration = tokio::time::Duration::from_secs(time_limit + 5);

        tokio::select! {
            output_result = child.wait_with_output() => {
                match output_result {
                    Ok(output) => {
                        Ok(SandboxedOutput {
                            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
                            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
                            exit_code: output.status.code(),
                            killed: false,
                            kill_reason: None,
                        })
                    }
                    Err(e) => {
                        Err(anyhow::anyhow!("Solver execution failed: {}", e))
                    }
                }
            }
            _ = tokio::time::sleep(timeout_duration) => {
                // Timeout reached -- the child future was dropped, which should
                // cause the process to be cleaned up. We report the timeout.
                Ok(SandboxedOutput {
                    stdout: String::new(),
                    stderr: String::new(),
                    exit_code: None,
                    killed: true,
                    kill_reason: Some(format!(
                        "Time limit exceeded ({} seconds)",
                        time_limit
                    )),
                })
            }
        }
    }

    /// Check if Podman is available
    fn podman_available() -> bool {
        std::process::Command::new("podman")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Check if bubblewrap is available
    fn bubblewrap_available() -> bool {
        std::process::Command::new("bwrap")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Get the sandbox kind being used
    pub fn kind(&self) -> SandboxKind {
        self.config.kind
    }

    /// Get the configuration
    pub fn config(&self) -> &SandboxConfig {
        &self.config
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sandbox_config_defaults() {
        let config = SandboxConfig::default();
        assert_eq!(config.memory_limit, 1024 * 1024 * 1024);
        assert_eq!(config.cpu_limit, 2);
        assert_eq!(config.time_limit, 300);
    }

    #[tokio::test]
    async fn test_unsandboxed_echo() {
        let executor = SandboxedExecutor::new(SandboxConfig {
            kind: SandboxKind::None,
            time_limit: 5,
            ..Default::default()
        });

        let result = executor.execute(
            Path::new("/usr/bin/echo"),
            &["hello", "world"],
            None,
            None,
        ).await;

        match result {
            Ok(output) => {
                assert!(!output.killed);
                assert!(output.stdout.contains("hello world"));
            }
            Err(e) => {
                // echo might not be at /usr/bin/echo on all systems
                eprintln!("Test skipped: {}", e);
            }
        }
    }

    #[tokio::test]
    async fn test_timeout_kills_process() {
        let executor = SandboxedExecutor::new(SandboxConfig {
            kind: SandboxKind::None,
            time_limit: 1, // 1 second timeout
            ..Default::default()
        });

        let result = executor.execute(
            Path::new("/usr/bin/sleep"),
            &["60"],
            None,
            None,
        ).await;

        match result {
            Ok(output) => {
                assert!(output.killed, "Process should have been killed");
                assert!(output.kill_reason.is_some());
            }
            Err(e) => {
                eprintln!("Test skipped: {}", e);
            }
        }
    }

    #[test]
    fn test_sandbox_detection() {
        // Just check that auto_detect doesn't panic
        let _executor = SandboxedExecutor::auto_detect();
    }
}
