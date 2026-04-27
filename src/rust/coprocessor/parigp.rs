// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! PARI/GP number-theory coprocessor — subprocess to `gp`.
//!
//! Wraps PARI/GP for operations beyond the Math backend's Pollard-rho:
//! - Complete integer factorisation (ECM / GNFS for large numbers)
//! - Multiplicative order of elements in (Z/nZ)*
//! - Next prime after a given bound
//!
//! Trust tier `ExternalSubprocess` (Tier 1).  The `gp` binary runs with
//! `-q` (quiet, no banners) and a 30-second wall-clock timeout.  Inputs are
//! validated as decimal integers before the subprocess is spawned; no
//! injection is possible through the decimal-only gate.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

const TIMEOUT: Duration = Duration::from_secs(30);

pub struct PariGpBackend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl PariGpBackend {
    pub fn new() -> Self {
        let health = if which("gp") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        PariGpBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "PariGpFactor".into(),
                    "PariGpZnorder".into(),
                    "PariGpNextPrime".into(),
                ],
                typical_latency_us: 100_000,
                deterministic: true,
            },
            health,
        }
    }
}

fn which(name: &str) -> bool {
    if let Ok(path) = std::env::var("PATH") {
        for dir in path.split(':') {
            let candidate = format!("{dir}/{name}");
            if std::path::Path::new(&candidate).is_file() {
                return true;
            }
        }
    }
    false
}

/// Accept only decimal integers: optional leading `-`, then ASCII digits.
fn is_decimal_int(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    (first == '-' || first.is_ascii_digit()) && chars.all(|c| c.is_ascii_digit())
}

impl Default for PariGpBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for PariGpBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::PariGp
    }
    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }
    fn health(&self) -> CoprocessorHealth {
        self.health
    }
    fn trust_tier(&self) -> CoprocessorTrustTier {
        CoprocessorTrustTier::ExternalSubprocess
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        if self.health == CoprocessorHealth::Unhealthy {
            return Ok(CoprocessorOutcome::Failure(
                "PariGp: gp not found on PATH".into(),
            ));
        }
        match op {
            CoprocessorOp::PariGpFactor { n } => {
                if !is_decimal_int(&n) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "PariGpFactor: invalid integer '{n}'"
                    )));
                }
                // Emit one `prime exponent` pair per line, easier to parse than
                // PARI's matrix pretty-print.
                let script = format!(
                    "f=factor({n}); for(i=1,matsize(f)[1],print(f[i,1],\" \",f[i,2]))\n\\q\n"
                );
                let out = run_gp(&script).await?;
                parse_factor_lines(&out)
            }
            CoprocessorOp::PariGpZnorder { a, n } => {
                if !is_decimal_int(&a) || !is_decimal_int(&n) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "PariGpZnorder: invalid integers a='{a}', n='{n}'"
                    )));
                }
                let script = format!("print(znorder(Mod({a},{n})))\n\\q\n");
                let out = run_gp(&script).await?;
                let trimmed = out.trim();
                if trimmed.is_empty() || trimmed.starts_with("***") {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "PariGpZnorder: gp error: {trimmed}"
                    )));
                }
                Ok(CoprocessorOutcome::BigInt(trimmed.to_string()))
            }
            CoprocessorOp::PariGpNextPrime { n } => {
                if !is_decimal_int(&n) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "PariGpNextPrime: invalid integer '{n}'"
                    )));
                }
                // nextprime(n) returns n itself if n is prime; +1 ensures strictly greater.
                let script = format!("print(nextprime({n}+1))\n\\q\n");
                let out = run_gp(&script).await?;
                let trimmed = out.trim();
                if trimmed.is_empty() || trimmed.starts_with("***") {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "PariGpNextPrime: gp error: {trimmed}"
                    )));
                }
                Ok(CoprocessorOutcome::BigInt(trimmed.to_string()))
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "PariGp backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn run_gp(script: &str) -> Result<String> {
    let mut child = Command::new("gp")
        .arg("-q")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|e| anyhow!("gp spawn: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .await
            .map_err(|e| anyhow!("gp stdin write: {e}"))?;
    }

    let out = tokio::time::timeout(TIMEOUT, child.wait_with_output())
        .await
        .map_err(|_| anyhow!("gp timed out after 30s"))?
        .map_err(|e| anyhow!("gp wait: {e}"))?;

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(anyhow!(
            "gp exit {}: {}",
            out.status.code().unwrap_or(-1),
            stderr.lines().take(3).collect::<Vec<_>>().join(" | ")
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

/// Parse one-per-line `prime exponent` output from our factor script.
fn parse_factor_lines(output: &str) -> Result<CoprocessorOutcome> {
    let mut factors = Vec::new();
    for line in output.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() != 2 {
            return Err(anyhow!("unexpected gp factor line: '{line}'"));
        }
        let prime = parts[0].to_string();
        let exp: u32 = parts[1]
            .parse()
            .map_err(|_| anyhow!("bad exponent in gp output: '{}'", parts[1]))?;
        factors.push((prime, exp));
    }
    Ok(CoprocessorOutcome::Factors(factors))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_int_validation() {
        assert!(is_decimal_int("0"));
        assert!(is_decimal_int("42"));
        assert!(is_decimal_int("-7"));
        assert!(is_decimal_int("123456789012345678901234567890"));
        assert!(!is_decimal_int(""));
        assert!(!is_decimal_int("4.2"));
        assert!(!is_decimal_int("1e10"));
        assert!(!is_decimal_int("1; echo pwned"));
        assert!(!is_decimal_int("$(cmd)"));
        assert!(!is_decimal_int(" 42"));
    }

    #[tokio::test]
    async fn unhealthy_returns_failure_without_spawn() {
        let backend = PariGpBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::PariGpNextPrime { n: "10".into() })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[tokio::test]
    async fn injection_attempt_rejected_before_spawn() {
        // Backend is Healthy so the health gate passes — only the decimal
        // validator should reject this.
        let backend = PariGpBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::PariGpFactor {
                n: "12; system(\"rm -rf /\")".into(),
            })
            .await
            .unwrap();
        assert!(
            matches!(&r, CoprocessorOutcome::Failure(msg) if msg.contains("invalid integer")),
            "got {r:?}"
        );
    }

    #[test]
    fn parse_factor_twelve() {
        // 12 = 2^2 * 3^1
        let out = "2 2\n3 1\n";
        match parse_factor_lines(out).unwrap() {
            CoprocessorOutcome::Factors(f) => {
                assert_eq!(f, vec![("2".into(), 2u32), ("3".into(), 1u32)]);
            }
            other => panic!("expected Factors, got {other:?}"),
        }
    }

    #[test]
    fn parse_factor_prime() {
        // 7 = 7^1
        let out = "7 1\n";
        match parse_factor_lines(out).unwrap() {
            CoprocessorOutcome::Factors(f) => {
                assert_eq!(f, vec![("7".into(), 1u32)]);
            }
            other => panic!("expected Factors, got {other:?}"),
        }
    }

    #[test]
    fn backend_construction_probes_path() {
        let b = PariGpBackend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::PariGp);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
