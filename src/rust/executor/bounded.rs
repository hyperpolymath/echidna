// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// executor/bounded.rs — Output-capped command execution.
//
// `Command::output()` reads all stdout/stderr into memory before returning,
// which allows a misbehaving prover to exhaust heap.  This module provides
// `bounded_command_output`, which streams both pipes concurrently and stops
// reading once either buffer exceeds `max_bytes`.
//
// Callers that previously wrote:
//   let out = cmd.output().await?;
// can replace with:
//   let out = bounded_command_output(&mut cmd, MAX_PROVER_OUTPUT_BYTES).await?;
// and then use `out.stdout` / `out.stderr` as `Vec<u8>` as before.

use anyhow::{anyhow, Result};
use tokio::io::AsyncReadExt;
use tokio::process::Command;
use std::process::{ExitStatus, Stdio};

/// Default per-invocation output cap: 8 MiB.
/// Covers the largest realistic prover proof transcript while bounding heap growth.
pub const MAX_PROVER_OUTPUT_BYTES: usize = 8 * 1024 * 1024;

/// Result of a bounded command invocation — mirrors `std::process::Output`.
pub struct BoundedOutput {
    pub status: ExitStatus,
    /// Stdout bytes, capped at `max_bytes`.  Truncated with a warning suffix if exceeded.
    pub stdout: Vec<u8>,
    /// Stderr bytes, capped at `max_bytes`.  Truncated with a warning suffix if exceeded.
    pub stderr: Vec<u8>,
    /// True if either stream was truncated.
    pub truncated: bool,
}

/// Run `cmd`, capturing at most `max_bytes` of stdout and `max_bytes` of stderr.
///
/// Both streams are read concurrently.  Once a buffer reaches `max_bytes` the
/// corresponding pipe is drained and discarded (so the child process never
/// blocks on write), but no more data is appended.
pub async fn bounded_command_output(cmd: &mut Command, max_bytes: usize) -> Result<BoundedOutput> {
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

    let mut child = cmd.spawn().map_err(|e| anyhow!("spawn failed: {e}"))?;

    let mut stdout_pipe = child.stdout.take().ok_or_else(|| anyhow!("no stdout pipe"))?;
    let mut stderr_pipe = child.stderr.take().ok_or_else(|| anyhow!("no stderr pipe"))?;

    let mut stdout_buf = Vec::with_capacity(max_bytes.min(64 * 1024));
    let mut stderr_buf = Vec::with_capacity(max_bytes.min(64 * 1024));
    // Separate read buffers so each select! arm has exclusive &mut access.
    let mut out_tmp = [0u8; 8192];
    let mut err_tmp = [0u8; 8192];
    let mut stdout_done = false;
    let mut stderr_done = false;

    // Interleaved read loop — avoids spawning extra tasks while still draining both pipes.
    loop {
        tokio::select! {
            n = stdout_pipe.read(&mut out_tmp), if !stdout_done => {
                match n? {
                    0 => { stdout_done = true; }
                    n => {
                        let remaining = max_bytes.saturating_sub(stdout_buf.len());
                        if remaining == 0 {
                            stdout_done = true;
                        } else {
                            stdout_buf.extend_from_slice(&out_tmp[..n.min(remaining)]);
                            if stdout_buf.len() >= max_bytes {
                                stdout_done = true;
                            }
                        }
                    }
                }
            }
            n = stderr_pipe.read(&mut err_tmp), if !stderr_done => {
                match n? {
                    0 => { stderr_done = true; }
                    n => {
                        let remaining = max_bytes.saturating_sub(stderr_buf.len());
                        if remaining == 0 {
                            stderr_done = true;
                        } else {
                            stderr_buf.extend_from_slice(&err_tmp[..n.min(remaining)]);
                            if stderr_buf.len() >= max_bytes {
                                stderr_done = true;
                            }
                        }
                    }
                }
            }
            else => break,
        }
        if stdout_done && stderr_done {
            break;
        }
    }

    let status = child.wait().await.map_err(|e| anyhow!("wait failed: {e}"))?;

    let truncated = stdout_buf.len() >= max_bytes || stderr_buf.len() >= max_bytes;
    if truncated {
        const NOTICE: &[u8] = b"\n[echidna: output truncated -- exceeded per-invocation cap]\n";
        if stdout_buf.len() >= max_bytes {
            stdout_buf.truncate(max_bytes);
            stdout_buf.extend_from_slice(NOTICE);
        }
        if stderr_buf.len() >= max_bytes {
            stderr_buf.truncate(max_bytes);
            stderr_buf.extend_from_slice(NOTICE);
        }
    }

    Ok(BoundedOutput { status, stdout: stdout_buf, stderr: stderr_buf, truncated })
}
