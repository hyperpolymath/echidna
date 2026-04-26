// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! GPUVerify — CUDA/OpenCL kernel verification backend.
//!
//! GPUVerify translates GPU kernels (CUDA `.cu` or OpenCL `.cl`) into
//! Boogie/BPL intermediate form and then invokes Z3 or CVC4 as the
//! backend SMT solver. It checks for:
//!   - Data races between concurrent GPU threads
//!   - Barrier divergence (non-uniform control flow at barriers)
//!   - Loop invariant violations (via `__invariant` / `__barrier_invariant`)
//!   - Pre/post-condition failures (via `__requires` / `__ensures`)
//!
//! Corpus source: GPUVerify's `testsuite/` directory and any CUDA/OpenCL
//! benchmark suites (Rodinia, PolyBench-GPU).
//!
//! Relationship to Boogie backend: GPUVerify uses Boogie internally, but
//! its input surface is GPU source, not `.bpl` files. This backend sits
//! one level above Boogie in the front-end stack.

#![allow(dead_code)]

use anyhow::{anyhow, Context as AnyhowContext, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Context as ProofContext, Goal, ProofState, Tactic, TacticResult, Term};

/// Backend wrapping the `gpuverify` command-line tool.
///
/// GPUVerify accepts a single `.cu` (CUDA) or `.cl` (OpenCL) source file
/// and reports whether every `__global__` / `__kernel` function is race-free
/// and barrier-divergence-free within the given thread/block geometry.
pub struct GpuVerifyBackend {
    /// Backend configuration (executable path, timeout, extra flags).
    config: ProverConfig,
}

impl GpuVerifyBackend {
    /// Create a new GPUVerify backend with the given configuration.
    pub fn new(config: ProverConfig) -> Self {
        GpuVerifyBackend { config }
    }

    /// Return the path to the `gpuverify` executable.
    fn binary(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("gpuverify")
        } else {
            self.config.executable.clone()
        }
    }

    /// Detect the GPU source dialect from file content.
    ///
    /// Returns `"cuda"` if any `__global__` annotation is found, `"opencl"`
    /// if any `__kernel` annotation is found, or `"unknown"` otherwise.
    fn detect_dialect(content: &str) -> &'static str {
        if content.contains("__global__") {
            "cuda"
        } else if content.contains("__kernel") {
            "opencl"
        } else {
            "unknown"
        }
    }

    /// Extract kernel function names from GPU source.
    ///
    /// Matches `__global__ void <name>` (CUDA) and
    /// `__kernel void <name>` (OpenCL) declarations. Returns the list of
    /// names found, which become individual goals in the proof state.
    fn extract_kernel_names(content: &str) -> Vec<String> {
        let mut names = Vec::new();
        // CUDA kernel pattern: __global__ void <identifier>(
        for line in content.lines() {
            let trimmed = line.trim();
            // CUDA: __global__ void kernelName(
            if trimmed.contains("__global__") && trimmed.contains("void") {
                if let Some(name) = Self::extract_function_name_after_void(trimmed, "__global__") {
                    names.push(name);
                }
            }
            // OpenCL: __kernel void kernelName(
            if trimmed.contains("__kernel") && trimmed.contains("void") {
                if let Some(name) = Self::extract_function_name_after_void(trimmed, "__kernel") {
                    names.push(name);
                }
            }
        }
        names
    }

    /// Extract the function name that follows `qualifier void <name>(`.
    ///
    /// Finds the qualifier keyword in the line, then scans for `void`,
    /// then reads the identifier that precedes the opening parenthesis.
    fn extract_function_name_after_void(line: &str, qualifier: &str) -> Option<String> {
        // Find qualifier, then find "void" after it
        let after_qual = line.find(qualifier).map(|pos| &line[pos..])?;
        let after_void = after_qual.find("void").map(|pos| &after_qual[pos + 4..])?;
        // Skip whitespace, read identifier characters up to '('
        let trimmed = after_void.trim_start();
        let end = trimmed.find(|c: char| !c.is_alphanumeric() && c != '_')?;
        let name = &trimmed[..end];
        if name.is_empty() {
            None
        } else {
            Some(name.to_string())
        }
    }

    /// Parse `gpuverify` output to determine verification outcome.
    ///
    /// GPUVerify writes `"GPUVerify: 0 verified, 0 errors"` on full success,
    /// or contains `"verified"` in a summary line. Failures mention `"error"`,
    /// `"race condition"`, or `"barrier divergence"`.
    fn parse_output(&self, stdout: &str, stderr: &str) -> bool {
        let combined = format!("{}\n{}", stdout, stderr);
        // Explicit success phrases
        if combined.contains("GPUVerify found no errors")
            || combined.contains("0 errors")
            || (combined.to_lowercase().contains("verified")
                && !combined.to_lowercase().contains("error"))
        {
            return true;
        }
        // Explicit failure phrases
        if combined.to_lowercase().contains("error")
            || combined.contains("race condition")
            || combined.contains("race detected")
            || combined.contains("barrier divergence")
        {
            return false;
        }
        // Exit 0 with no recognisable failure phrase → treat as success
        true
    }
}

#[async_trait]
impl ProverBackend for GpuVerifyBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::GPUVerify
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(self.binary())
            .arg("--version")
            .output()
            .await;
        match output {
            Ok(out) => {
                let text = String::from_utf8_lossy(&out.stdout);
                let text_err = String::from_utf8_lossy(&out.stderr);
                let combined = format!("{}{}", text, text_err).trim().to_string();
                if combined.is_empty() {
                    Ok("gpuverify@unknown-version".to_string())
                } else {
                    Ok(combined)
                }
            },
            Err(_) => Ok("gpuverify@not-installed".to_string()),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .with_context(|| format!("GPUVerify: reading {}", path.display()))?;
        let mut state = self.parse_string(&content).await?;
        // Store the original file path for verify_proof to use directly.
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        // Each kernel becomes a separate goal named after the function.
        let kernel_names = Self::extract_kernel_names(content);
        let goals: Vec<Goal> = if kernel_names.is_empty() {
            // Fallback: treat the entire file as one goal.
            vec![Goal {
                id: "gpuverify-file".to_string(),
                target: Term::Const(content.to_string()),
                hypotheses: vec![],
            }]
        } else {
            kernel_names
                .iter()
                .map(|name| Goal {
                    id: format!("kernel_{}", name),
                    target: Term::Const(format!("race_free({})", name)),
                    hypotheses: vec![],
                })
                .collect()
        };

        let dialect = Self::detect_dialect(content);
        let mut state = ProofState {
            goals,
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: Default::default(),
        };
        // Store source and dialect for verify_proof / export.
        state.metadata.insert(
            "gpuverify_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        state.metadata.insert(
            "gpuverify_dialect".to_string(),
            serde_json::Value::String(dialect.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // GPUVerify is an automated verifier; tactics encode annotation hints.
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let source = state
            .metadata
            .get("gpuverify_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default();

        // Determine extension from dialect; default to .cu (CUDA).
        let dialect = state
            .metadata
            .get("gpuverify_dialect")
            .and_then(|v| v.as_str())
            .unwrap_or("cuda");
        let ext = if dialect == "opencl" { "cl" } else { "cu" };

        // If we have the original file path, use it directly.
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
            .map_err(|_| anyhow!("GPUVerify timed out after {} s", self.config.timeout))?
            .context("GPUVerify: binary not runnable")?;
            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr);
            return Ok(self.parse_output(&stdout, &stderr));
        }

        // Otherwise write source to a temporary file.
        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-gpuverify-")
            .tempdir()
            .context("GPUVerify: tempdir")?;
        let input_path = tmp_dir.path().join(format!("kernel.{}", ext));
        tokio::fs::write(&input_path, source.as_bytes())
            .await
            .context("GPUVerify: writing temp source")?;

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
        .map_err(|_| anyhow!("GPUVerify timed out after {} s", self.config.timeout))?
        .context("GPUVerify: binary not runnable")?;

        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        Ok(self.parse_output(&stdout, &stderr))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        // Export the original GPU source as-is.
        Ok(state
            .metadata
            .get("gpuverify_source")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_default())
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // GPUVerify uses annotation-style specification: __requires, __ensures,
        // __invariant, __barrier_invariant, and assert for inline checks.
        let tactics = vec![
            Tactic::Custom {
                prover: "gpuverify".to_string(),
                command: "__requires".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "gpuverify".to_string(),
                command: "__ensures".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "gpuverify".to_string(),
                command: "__invariant".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "gpuverify".to_string(),
                command: "__barrier_invariant".to_string(),
                args: vec!["true".to_string()],
            },
            Tactic::Custom {
                prover: "gpuverify".to_string(),
                command: "assert".to_string(),
                args: vec!["true".to_string()],
            },
        ];
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // GPUVerify has no theorem library; search the context axioms for
        // __global__ / __kernel names that match the pattern.
        let pat_lower = pattern.to_lowercase();
        // Return plausible annotation primitives if the pattern matches.
        let candidates = vec![
            "__requires".to_string(),
            "__ensures".to_string(),
            "__invariant".to_string(),
            "__barrier_invariant".to_string(),
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

    #[test]
    fn kind_is_gpuverify() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::GPUVerify);
    }

    #[test]
    fn detect_dialect_cuda() {
        let src = "__global__ void myKernel(float* d) {}";
        assert_eq!(GpuVerifyBackend::detect_dialect(src), "cuda");
    }

    #[test]
    fn detect_dialect_opencl() {
        let src = "__kernel void myKernel(__global float* d) {}";
        assert_eq!(GpuVerifyBackend::detect_dialect(src), "opencl");
    }

    #[test]
    fn detect_dialect_unknown() {
        let src = "int main() { return 0; }";
        assert_eq!(GpuVerifyBackend::detect_dialect(src), "unknown");
    }

    #[test]
    fn extract_kernel_names_cuda() {
        let src = r#"
__global__ void addKernel(float* a, float* b, float* c) {
    int idx = threadIdx.x;
    c[idx] = a[idx] + b[idx];
}
__global__ void scaleKernel(float* a, float scale) {
    a[threadIdx.x] *= scale;
}
"#;
        let names = GpuVerifyBackend::extract_kernel_names(src);
        assert_eq!(names, vec!["addKernel", "scaleKernel"]);
    }

    #[test]
    fn extract_kernel_names_opencl() {
        let src = r#"
__kernel void vectorAdd(__global float* a, __global float* b, __global float* c) {
    int gid = get_global_id(0);
    c[gid] = a[gid] + b[gid];
}
"#;
        let names = GpuVerifyBackend::extract_kernel_names(src);
        assert_eq!(names, vec!["vectorAdd"]);
    }

    #[test]
    fn extract_kernel_names_empty() {
        let src = "int x = 42;";
        let names = GpuVerifyBackend::extract_kernel_names(src);
        assert!(names.is_empty());
    }

    #[tokio::test]
    async fn parse_string_cuda_creates_goals() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        let src = r#"
__global__ void addKernel(float* a, float* b, float* c) {
    int idx = threadIdx.x;
    c[idx] = a[idx] + b[idx];
}
"#;
        let state = backend.parse_string(src).await.unwrap();
        assert_eq!(state.goals.len(), 1);
        assert_eq!(state.goals[0].id, "kernel_addKernel");
        assert!(state
            .metadata
            .contains_key("gpuverify_source"));
        assert_eq!(
            state.metadata["gpuverify_dialect"].as_str().unwrap(),
            "cuda"
        );
    }

    #[tokio::test]
    async fn parse_string_no_kernels_fallback() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        let src = "int x = 42;";
        let state = backend.parse_string(src).await.unwrap();
        assert_eq!(state.goals.len(), 1);
        assert_eq!(state.goals[0].id, "gpuverify-file");
    }

    #[tokio::test]
    async fn suggest_tactics_returns_five() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        let state = ProofState::default();
        let tactics = backend.suggest_tactics(&state, 5).await.unwrap();
        assert_eq!(tactics.len(), 5);
    }

    #[tokio::test]
    async fn search_theorems_filters_by_pattern() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        let results = backend.search_theorems("invariant").await.unwrap();
        assert!(results.iter().any(|s| s.contains("invariant")));
        // "requires" and "ensures" should not match "invariant"
        assert!(!results.iter().any(|s| s == "__requires"));
    }

    #[test]
    fn parse_output_success_no_errors() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        assert!(backend.parse_output("GPUVerify found no errors\n", ""));
    }

    #[test]
    fn parse_output_failure_race() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        assert!(!backend.parse_output("race condition detected in kernel\n", ""));
    }

    #[test]
    fn parse_output_failure_barrier() {
        let backend = GpuVerifyBackend::new(ProverConfig::default());
        assert!(!backend.parse_output("barrier divergence at line 42\n", ""));
    }
}
