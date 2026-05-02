// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! IO coprocessor — file / stream operations via `tokio::fs`.
//!
//! Backs proof-artifact handling: read a Coq `.v` file, hash it, line-count
//! it.  All ops are async and bounded by sensible defaults so a malicious
//! input can't exhaust memory:
//! - `IoReadAll` rejects files larger than `MAX_READ_BYTES` (16 MiB).
//! - `IoLineCount` and `IoSha256OfFile` stream — no size cap needed.
//!
//! Path arguments are passed verbatim — caller is responsible for any path
//! sanitisation (the prover-side trust pipeline does this before dispatch).

use anyhow::Result;
use async_trait::async_trait;
use sha2::{Digest, Sha256};
use tokio::fs;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, BufReader};

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

const MAX_READ_BYTES: u64 = 16 * 1024 * 1024;
const STREAM_CHUNK: usize = 64 * 1024;

pub struct IoBackend {
    capabilities: CoprocessorCapabilities,
}

impl IoBackend {
    pub fn new() -> Self {
        IoBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "IoReadAll".into(),
                    "IoLineCount".into(),
                    "IoSha256OfFile".into(),
                ],
                typical_latency_us: 500,
                deterministic: true,
            },
        }
    }
}

impl Default for IoBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for IoBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Io
    }
    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }
    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }
    fn trust_tier(&self) -> CoprocessorTrustTier {
        // Reads from the local filesystem only — Tier 3.
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        match op {
            CoprocessorOp::IoReadAll { path } => Ok(read_all(&path).await),
            CoprocessorOp::IoLineCount { path } => Ok(line_count(&path).await),
            CoprocessorOp::IoSha256OfFile { path } => Ok(sha256_of_file(&path).await),
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Io backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn read_all(path: &str) -> CoprocessorOutcome {
    let meta = match fs::metadata(path).await {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return CoprocessorOutcome::Empty
        }
        Err(e) => return CoprocessorOutcome::Failure(format!("metadata({path}): {e}")),
    };
    if meta.len() > MAX_READ_BYTES {
        return CoprocessorOutcome::Failure(format!(
            "IoReadAll: file {path} ({} bytes) exceeds {} byte cap",
            meta.len(),
            MAX_READ_BYTES
        ));
    }
    match fs::read(path).await {
        Ok(bytes) => CoprocessorOutcome::Hex(hex(&bytes)),
        Err(e) => CoprocessorOutcome::Failure(format!("read({path}): {e}")),
    }
}

async fn line_count(path: &str) -> CoprocessorOutcome {
    let f = match fs::File::open(path).await {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return CoprocessorOutcome::Empty
        }
        Err(e) => return CoprocessorOutcome::Failure(format!("open({path}): {e}")),
    };
    let mut reader = BufReader::new(f);
    let mut line = String::new();
    let mut count: u64 = 0;
    loop {
        line.clear();
        match reader.read_line(&mut line).await {
            Ok(0) => break,
            Ok(_) => count += 1,
            Err(e) => {
                return CoprocessorOutcome::Failure(format!("read_line({path}): {e}"))
            }
        }
    }
    CoprocessorOutcome::BigInt(count.to_string())
}

async fn sha256_of_file(path: &str) -> CoprocessorOutcome {
    let mut f = match fs::File::open(path).await {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return CoprocessorOutcome::Empty
        }
        Err(e) => return CoprocessorOutcome::Failure(format!("open({path}): {e}")),
    };
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; STREAM_CHUNK];
    loop {
        match f.read(&mut buf).await {
            Ok(0) => break,
            Ok(n) => hasher.update(&buf[..n]),
            Err(e) => {
                return CoprocessorOutcome::Failure(format!("read({path}): {e}"))
            }
        }
    }
    CoprocessorOutcome::Hex(hex(&hasher.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    async fn dispatch(op: CoprocessorOp) -> CoprocessorOutcome {
        IoBackend::new().dispatch(op).await.unwrap()
    }

    #[tokio::test]
    async fn read_all_known_content() {
        let mut f = NamedTempFile::new().unwrap();
        write!(f, "hello echidna").unwrap();
        match dispatch(CoprocessorOp::IoReadAll {
            path: f.path().to_string_lossy().into(),
        })
        .await
        {
            CoprocessorOutcome::Hex(h) => {
                assert_eq!(h, "68656c6c6f2065636869646e61");
            }
            _ => panic!(),
        }
    }

    #[tokio::test]
    async fn read_missing_file_returns_empty() {
        match dispatch(CoprocessorOp::IoReadAll {
            path: "/nonexistent/path/echidna-test".into(),
        })
        .await
        {
            CoprocessorOutcome::Empty => {}
            _ => panic!(),
        }
    }

    #[tokio::test]
    async fn line_count_three_lines() {
        let mut f = NamedTempFile::new().unwrap();
        writeln!(f, "a").unwrap();
        writeln!(f, "b").unwrap();
        writeln!(f, "c").unwrap();
        match dispatch(CoprocessorOp::IoLineCount {
            path: f.path().to_string_lossy().into(),
        })
        .await
        {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "3"),
            _ => panic!(),
        }
    }

    #[tokio::test]
    async fn sha256_of_known_file() {
        // "abc" → ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
        let mut f = NamedTempFile::new().unwrap();
        write!(f, "abc").unwrap();
        match dispatch(CoprocessorOp::IoSha256OfFile {
            path: f.path().to_string_lossy().into(),
        })
        .await
        {
            CoprocessorOutcome::Hex(h) => assert_eq!(
                h,
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
            ),
            _ => panic!(),
        }
    }
}
