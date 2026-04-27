// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Maxima symbolic-algebra coprocessor — subprocess to `maxima`.
//!
//! Provides symbolic simplification, polynomial factoring, and differentiation
//! using the Maxima CAS (GPL).  Trust tier `ExternalSubprocess` (Tier 1).
//!
//! Input expressions are validated against a safe-character whitelist before
//! the subprocess is spawned: only alphanumeric characters plus the standard
//! mathematical operator set (`+ - * / ^ ( ) . , _ space`) are accepted.
//!
//! The subprocess is invoked as `maxima --quiet --batch-string=...`.  Output
//! lines starting with `(%` (Maxima input/output labels) or Maxima banner
//! fragments are stripped before the result is returned as `Text`.  The
//! `grind` function is used to get single-line, parseable output.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::time::Duration;
use tokio::process::Command;

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

const TIMEOUT: Duration = Duration::from_secs(30);

pub struct MaximaBackend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl MaximaBackend {
    pub fn new() -> Self {
        let health = if which("maxima") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        MaximaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "MaximaSimplify".into(),
                    "MaximaFactor".into(),
                    "MaximaDiff".into(),
                ],
                typical_latency_us: 500_000,
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

/// Allow only characters that can appear in a mathematical expression.
/// Blocks shell metacharacters (`;` `:` `$` `"` `'` `\` `!` `&` `|` etc.).
fn is_safe_expr(s: &str) -> bool {
    !s.is_empty()
        && s.chars().all(|c| {
            c.is_ascii_alphanumeric() || "+-*/^()., _".contains(c)
        })
}

/// Identifier: ASCII letter first, then alphanumeric or underscore.
fn is_safe_var(s: &str) -> bool {
    !s.is_empty()
        && s.chars().next().unwrap().is_ascii_alphabetic()
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Strip Maxima banner lines and `(%i...)` / `(%o...)` label lines, returning
/// the CAS result text.  `grind` output ends with `;` — that is stripped too.
fn extract_result(output: &str) -> String {
    let skip_prefixes = ["(%", "Maxima", "using Lisp", "Distributed", "Dedicated", "The function"];
    output
        .lines()
        .filter(|line| {
            let t = line.trim();
            !t.is_empty() && !skip_prefixes.iter().any(|p| t.starts_with(p))
        })
        .map(|line| line.trim().trim_end_matches(';'))
        .collect::<Vec<_>>()
        .join("\n")
}

impl Default for MaximaBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for MaximaBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Maxima
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
                "Maxima: maxima not found on PATH".into(),
            ));
        }
        match op {
            CoprocessorOp::MaximaSimplify { expr } => {
                if !is_safe_expr(&expr) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "MaximaSimplify: unsafe expression '{expr}'"
                    )));
                }
                let batch = format!("display2d:false; grind(fullratsimp({expr}))$");
                run_maxima_batch(&batch).await
            }
            CoprocessorOp::MaximaFactor { expr } => {
                if !is_safe_expr(&expr) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "MaximaFactor: unsafe expression '{expr}'"
                    )));
                }
                let batch = format!("display2d:false; grind(factor({expr}))$");
                run_maxima_batch(&batch).await
            }
            CoprocessorOp::MaximaDiff { expr, var } => {
                if !is_safe_expr(&expr) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "MaximaDiff: unsafe expression '{expr}'"
                    )));
                }
                if !is_safe_var(&var) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "MaximaDiff: unsafe variable name '{var}'"
                    )));
                }
                let batch = format!("display2d:false; grind(diff({expr},{var}))$");
                run_maxima_batch(&batch).await
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Maxima backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn run_maxima_batch(batch_string: &str) -> Result<CoprocessorOutcome> {
    let out = tokio::time::timeout(
        TIMEOUT,
        Command::new("maxima")
            .arg("--quiet")
            .arg(format!("--batch-string={batch_string}"))
            .output(),
    )
    .await
    .map_err(|_| anyhow!("maxima timed out after 30s"))?
    .map_err(|e| anyhow!("maxima spawn: {e}"))?;

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(anyhow!(
            "maxima exit {}: {}",
            out.status.code().unwrap_or(-1),
            stderr.lines().take(3).collect::<Vec<_>>().join(" | ")
        ));
    }

    let result = extract_result(&String::from_utf8_lossy(&out.stdout));
    if result.is_empty() {
        return Ok(CoprocessorOutcome::Failure(
            "maxima returned no usable output".into(),
        ));
    }
    Ok(CoprocessorOutcome::Text(result))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn safe_expr_validation() {
        assert!(is_safe_expr("x^2+2*x+1"));
        assert!(is_safe_expr("sin(x)"));
        assert!(is_safe_expr("3.14*r^2"));
        assert!(!is_safe_expr(""));
        assert!(!is_safe_expr("x; system(\"rm\")"));
        assert!(!is_safe_expr("x$quit"));
        assert!(!is_safe_expr("x\ny"));
        assert!(!is_safe_expr("$(cmd)"));
    }

    #[test]
    fn safe_var_validation() {
        assert!(is_safe_var("x"));
        assert!(is_safe_var("theta"));
        assert!(is_safe_var("x_1"));
        assert!(!is_safe_var(""));
        assert!(!is_safe_var("1x"));
        assert!(!is_safe_var("x y"));
        assert!(!is_safe_var("x;"));
    }

    #[tokio::test]
    async fn unhealthy_returns_failure_without_spawn() {
        let backend = MaximaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::MaximaSimplify { expr: "x+x".into() })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[tokio::test]
    async fn unsafe_expr_rejected_before_spawn() {
        let backend = MaximaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::MaximaFactor {
                expr: "x^2; system(\"id\")".into(),
            })
            .await
            .unwrap();
        assert!(
            matches!(&r, CoprocessorOutcome::Failure(msg) if msg.contains("unsafe expression")),
            "got {r:?}"
        );
    }

    #[test]
    fn extract_result_strips_labels() {
        let raw = "(%i1) display2d:false;\n(%o1) false\n(%i2) grind(factor(x^2-1))$\n(x-1)*(x+1);\n";
        let result = extract_result(raw);
        assert_eq!(result, "(x-1)*(x+1)");
    }

    #[test]
    fn backend_construction_probes_path() {
        let b = MaximaBackend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::Maxima);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
