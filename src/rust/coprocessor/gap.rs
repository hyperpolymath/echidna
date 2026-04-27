// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! GAP group-theory coprocessor — subprocess to `gap`.
//!
//! Provides permutation group computations: order, abelianness test, and
//! symmetric group order.  Trust tier `ExternalSubprocess` (Tier 1).
//!
//! Permutation generators are validated against cycle-notation characters
//! only: digits, `(`, `)`, `,`, and space.  No letters or shell
//! metacharacters can appear in a permutation.  GAP is invoked with `-q`
//! (quiet, no banner) and a 30-second timeout.

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

pub struct GapBackend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl GapBackend {
    pub fn new() -> Self {
        let health = if which("gap") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        GapBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "GapGroupOrder".into(),
                    "GapIsAbelian".into(),
                    "GapSymmetricGroupOrder".into(),
                ],
                typical_latency_us: 200_000,
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

/// Accept only characters that appear in cycle notation: digits, `()`, `,`,
/// and ASCII space.  No letters, no shell metacharacters.
fn is_safe_permutation(s: &str) -> bool {
    !s.is_empty()
        && s.chars().all(|c| c.is_ascii_digit() || "(,) ".contains(c))
}

/// Render a list of permutations as a comma-separated GAP argument list.
/// Each entry is already validated to contain only cycle-notation chars, so
/// direct interpolation is safe.
fn gen_list(generators: &[String]) -> String {
    generators.join(",")
}

impl Default for GapBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for GapBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Gap
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
                "Gap: gap not found on PATH".into(),
            ));
        }
        match op {
            CoprocessorOp::GapGroupOrder { generators } => {
                if generators.is_empty() {
                    return Ok(CoprocessorOutcome::Failure(
                        "GapGroupOrder: generators list is empty".into(),
                    ));
                }
                if let Some(bad) = generators.iter().find(|g| !is_safe_permutation(g)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "GapGroupOrder: unsafe permutation '{bad}'"
                    )));
                }
                let script = format!(
                    "g := Group({gens});\nPrint(Order(g), \"\\n\");\nQUIT;\n",
                    gens = gen_list(&generators)
                );
                let out = run_gap(&script).await?;
                Ok(CoprocessorOutcome::BigInt(out.trim().to_string()))
            }
            CoprocessorOp::GapIsAbelian { generators } => {
                if generators.is_empty() {
                    return Ok(CoprocessorOutcome::Failure(
                        "GapIsAbelian: generators list is empty".into(),
                    ));
                }
                if let Some(bad) = generators.iter().find(|g| !is_safe_permutation(g)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "GapIsAbelian: unsafe permutation '{bad}'"
                    )));
                }
                let script = format!(
                    "g := Group({gens});\nPrint(IsAbelian(g), \"\\n\");\nQUIT;\n",
                    gens = gen_list(&generators)
                );
                let out = run_gap(&script).await?;
                let trimmed = out.trim();
                match trimmed {
                    "true" => Ok(CoprocessorOutcome::Boolean(true)),
                    "false" => Ok(CoprocessorOutcome::Boolean(false)),
                    other => Ok(CoprocessorOutcome::Failure(format!(
                        "GapIsAbelian: unexpected output '{other}'"
                    ))),
                }
            }
            CoprocessorOp::GapSymmetricGroupOrder { n } => {
                let script = format!(
                    "Print(Order(SymmetricGroup({n})), \"\\n\");\nQUIT;\n"
                );
                let out = run_gap(&script).await?;
                Ok(CoprocessorOutcome::BigInt(out.trim().to_string()))
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Gap backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn run_gap(script: &str) -> Result<String> {
    let mut child = Command::new("gap")
        .arg("-q")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|e| anyhow!("gap spawn: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .await
            .map_err(|e| anyhow!("gap stdin write: {e}"))?;
    }

    let out = tokio::time::timeout(TIMEOUT, child.wait_with_output())
        .await
        .map_err(|_| anyhow!("gap timed out after 30s"))?
        .map_err(|e| anyhow!("gap wait: {e}"))?;

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(anyhow!(
            "gap exit {}: {}",
            out.status.code().unwrap_or(-1),
            stderr.lines().take(3).collect::<Vec<_>>().join(" | ")
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn safe_permutation_validation() {
        assert!(is_safe_permutation("(1,2,3)"));
        assert!(is_safe_permutation("(1,2)(3,4)"));
        assert!(is_safe_permutation("(12,34)"));
        assert!(!is_safe_permutation(""));
        assert!(!is_safe_permutation("(1,2); QUIT"));
        assert!(!is_safe_permutation("(a,b)"));
        assert!(!is_safe_permutation("(1,2)\n(3,4)"));
    }

    #[tokio::test]
    async fn unhealthy_returns_failure_without_spawn() {
        let backend = GapBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::GapSymmetricGroupOrder { n: 3 })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[tokio::test]
    async fn unsafe_permutation_rejected_before_spawn() {
        let backend = GapBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::GapGroupOrder {
                generators: vec!["(1,2); QUIT; Print(\"pwned\")".into()],
            })
            .await
            .unwrap();
        assert!(
            matches!(&r, CoprocessorOutcome::Failure(msg) if msg.contains("unsafe permutation")),
            "got {r:?}"
        );
    }

    #[tokio::test]
    async fn empty_generators_rejected() {
        let backend = GapBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::GapIsAbelian { generators: vec![] })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[test]
    fn gen_list_format() {
        let gens = vec!["(1,2,3)".to_string(), "(1,2)".to_string()];
        assert_eq!(gen_list(&gens), "(1,2,3),(1,2)");
    }

    #[test]
    fn backend_construction_probes_path() {
        let b = GapBackend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::Gap);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
