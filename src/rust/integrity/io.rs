// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Sync bounded read for operator-controlled config files.
//!
//! Solver manifest paths are operator-controlled TOML files (not user-supplied
//! proof files), so a sync read is appropriate.  The same bound principle
//! as [`crate::provers::io::bounded_read_proof_file`] applies: cap at
//! [`MAX_CONFIG_BYTES`] and error rather than truncate.

use anyhow::{Context, Result};
use std::path::Path;

/// Maximum byte length for a solver manifest config read (1 MiB).
pub const MAX_CONFIG_BYTES: u64 = 1024 * 1024;

/// Read a UTF-8 config file (e.g. solver manifest TOML), bounded at [`MAX_CONFIG_BYTES`].
///
/// Uses `File::take(N+1)` so an oversized file is detected in a single
/// read pass — no TOCTOU race against `metadata().len()`.
pub fn bounded_read_config<P: AsRef<Path>>(path: P) -> Result<String> {
    use std::io::Read;
    let path = path.as_ref();
    let file = std::fs::File::open(path)
        .with_context(|| format!("opening config {}", path.display()))?;
    let mut buf = String::new();
    let mut limited = file.take(MAX_CONFIG_BYTES + 1);
    limited
        .read_to_string(&mut buf)
        .with_context(|| format!("reading config {}", path.display()))?;
    if buf.len() as u64 > MAX_CONFIG_BYTES {
        return Err(anyhow::anyhow!(
            "config file {} exceeds {} byte cap",
            path.display(),
            MAX_CONFIG_BYTES
        ));
    }
    Ok(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_config_reads_fully() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("solvers.toml");
        std::fs::write(&path, b"[solvers]\nz3 = \"/usr/bin/z3\"\n").unwrap();
        let s = bounded_read_config(&path).unwrap();
        assert!(s.contains("solvers"));
    }

    #[test]
    fn oversized_config_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("big.toml");
        let big = vec![b'x'; (MAX_CONFIG_BYTES + 1024) as usize];
        std::fs::write(&path, &big).unwrap();
        let err = bounded_read_config(&path).unwrap_err();
        assert!(err.to_string().contains("exceeds"));
    }
}
