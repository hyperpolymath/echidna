// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Shared IO helpers for prover backends.
//!
//! All prover backends read user-supplied proof files from disk. Bare
//! `tokio::fs::read_to_string(&path)` has no upper bound — a malicious
//! or pathological caller could pass `/dev/zero` or a multi-GB file
//! and OOM the process. This module exposes
//! [`bounded_read_proof_file`] which caps the read at
//! [`MAX_PROOF_BYTES`] and reports an error rather than truncating.
//!
//! Cap chosen at 64 MiB: large real-world proof corpora (Mizar MML
//! per-article files, Coq `.v` libraries, Isabelle theory chains)
//! all sit well below this limit with margin; anything larger is
//! almost certainly pathological input.

use anyhow::{Context, Result};
use std::path::Path;
use tokio::io::AsyncReadExt;

/// Maximum byte length for a single proof-file read (64 MiB).
pub const MAX_PROOF_BYTES: u64 = 64 * 1024 * 1024;

/// Read a UTF-8 proof file, bounded at [`MAX_PROOF_BYTES`].
///
/// Uses `AsyncReadExt::take(N+1)` so an oversized file is detected
/// in a single read pass — no TOCTOU race against `metadata().len()`.
pub async fn bounded_read_proof_file<P: AsRef<Path>>(path: P) -> Result<String> {
    let path = path.as_ref();
    let file = tokio::fs::File::open(path)
        .await
        .with_context(|| format!("opening proof file {}", path.display()))?;
    let mut buf = String::new();
    let mut limited = file.take(MAX_PROOF_BYTES + 1);
    limited
        .read_to_string(&mut buf)
        .await
        .with_context(|| format!("reading proof file {}", path.display()))?;
    if buf.len() as u64 > MAX_PROOF_BYTES {
        return Err(anyhow::anyhow!(
            "proof file {} exceeds {} byte cap",
            path.display(),
            MAX_PROOF_BYTES
        ));
    }
    Ok(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn small_file_reads_fully() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("small.proof");
        tokio::fs::write(&path, b"theorem foo : 1 + 1 = 2 := refl\n")
            .await
            .unwrap();
        let s = bounded_read_proof_file(&path).await.unwrap();
        assert!(s.contains("theorem foo"));
    }

    #[tokio::test]
    async fn oversized_file_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("big.proof");
        let big = vec![b'x'; (MAX_PROOF_BYTES + 1024) as usize];
        tokio::fs::write(&path, &big).await.unwrap();
        let err = bounded_read_proof_file(&path).await.unwrap_err();
        assert!(err.to_string().contains("exceeds"));
    }
}
