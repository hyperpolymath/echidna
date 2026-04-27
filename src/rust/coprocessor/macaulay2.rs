// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Macaulay2 algebraic-geometry coprocessor — subprocess to `M2`.
//!
//! Provides Gröbner bases, Krull dimension, and degree of quotient rings
//! over QQ using the Macaulay2 CAS (GPL).  Trust tier `ExternalSubprocess`
//! (Tier 1).
//!
//! Variable names and polynomial expressions are validated against safe
//! character whitelists before the subprocess is spawned.  `M2` is invoked
//! with `--silent --no-preloads` (suppress banners and package autoloading)
//! and a 30-second timeout.  All rings are over QQ; the polynomial ring is
//! constructed as `QQ[vars]` with default grevlex ordering.
//!
//! Output is captured from `print` statements embedded in the M2 script.

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

pub struct Macaulay2Backend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl Macaulay2Backend {
    pub fn new() -> Self {
        let health = if which("M2") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        Macaulay2Backend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "Macaulay2GroebnerBasis".into(),
                    "Macaulay2Dimension".into(),
                    "Macaulay2Degree".into(),
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

/// Variable names: letter first, then alphanumeric or underscore.
fn is_safe_var(s: &str) -> bool {
    !s.is_empty()
        && s.chars().next().unwrap().is_ascii_alphabetic()
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Polynomial expressions: alphanumeric plus standard math operators.
fn is_safe_expr(s: &str) -> bool {
    !s.is_empty()
        && s.chars().all(|c| {
            c.is_ascii_alphanumeric() || "+-*/^()., _".contains(c)
        })
}

/// Build an M2 ring declaration over QQ with the given variable names.
fn m2_ring_def(vars: &[String]) -> String {
    format!("R = QQ[{vars}];\n", vars = vars.join(","))
}

/// Build an M2 ideal declaration from a list of polynomial strings.
fn m2_ideal_def(name: &str, polys: &[String]) -> String {
    format!("{name} = ideal({polys});\n", polys = polys.join(", "))
}

/// Filter M2 output: keep lines that are not blank, not `o<n> = ...` result
/// annotations, and not `o<n> : ...` type annotations.  `print` in M2 sends
/// output directly without annotations, so printed lines pass through cleanly.
fn extract_m2_output(output: &str) -> String {
    output
        .lines()
        .filter(|line| {
            let t = line.trim();
            !t.is_empty()
                && !t.starts_with("o")  // o1 = ..., o1 : ... result annotations
                && !t.starts_with("--") // M2 comment output
                && !t.starts_with("Macaulay")
                && !t.starts_with("version")
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n")
}

impl Default for Macaulay2Backend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for Macaulay2Backend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Macaulay2
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
                "Macaulay2: M2 not found on PATH".into(),
            ));
        }
        match op {
            CoprocessorOp::Macaulay2GroebnerBasis { vars, polys } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2GroebnerBasis: unsafe variable '{bad}'"
                    )));
                }
                if let Some(bad) = polys.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2GroebnerBasis: unsafe polynomial '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}{ideal}\
                     G = gens gb I;\n\
                     scan(numColumns G, i -> print(toString G_(0,i)));\n\
                     exit 0\n",
                    ring = m2_ring_def(&vars),
                    ideal = m2_ideal_def("I", &polys),
                );
                let out = run_m2(&script).await?;
                let result = extract_m2_output(&out);
                Ok(CoprocessorOutcome::Text(result))
            }
            CoprocessorOp::Macaulay2Dimension { vars, polys } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2Dimension: unsafe variable '{bad}'"
                    )));
                }
                if let Some(bad) = polys.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2Dimension: unsafe polynomial '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}{ideal}\
                     print(dim(R/I));\n\
                     exit 0\n",
                    ring = m2_ring_def(&vars),
                    ideal = m2_ideal_def("I", &polys),
                );
                let out = run_m2(&script).await?;
                let result = extract_m2_output(&out);
                let trimmed = result.trim();
                Ok(CoprocessorOutcome::BigInt(trimmed.to_string()))
            }
            CoprocessorOp::Macaulay2Degree { vars, polys } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2Degree: unsafe variable '{bad}'"
                    )));
                }
                if let Some(bad) = polys.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "Macaulay2Degree: unsafe polynomial '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}{ideal}\
                     print(degree(R/I));\n\
                     exit 0\n",
                    ring = m2_ring_def(&vars),
                    ideal = m2_ideal_def("I", &polys),
                );
                let out = run_m2(&script).await?;
                let result = extract_m2_output(&out);
                let trimmed = result.trim();
                Ok(CoprocessorOutcome::BigInt(trimmed.to_string()))
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Macaulay2 backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn run_m2(script: &str) -> Result<String> {
    let mut child = Command::new("M2")
        .arg("--silent")
        .arg("--no-preloads")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|e| anyhow!("M2 spawn: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .await
            .map_err(|e| anyhow!("M2 stdin write: {e}"))?;
    }

    let out = tokio::time::timeout(TIMEOUT, child.wait_with_output())
        .await
        .map_err(|_| anyhow!("M2 timed out after 30s"))?
        .map_err(|e| anyhow!("M2 wait: {e}"))?;

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(anyhow!(
            "M2 exit {}: {}",
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
    fn safe_var_validation() {
        assert!(is_safe_var("x"));
        assert!(is_safe_var("x1"));
        assert!(is_safe_var("alpha_1"));
        assert!(!is_safe_var(""));
        assert!(!is_safe_var("1x"));
        assert!(!is_safe_var("x,y"));
        assert!(!is_safe_var("x y"));
    }

    #[test]
    fn safe_expr_validation() {
        assert!(is_safe_expr("x^2-y^2"));
        assert!(is_safe_expr("3*x+2*y-1"));
        assert!(!is_safe_expr(""));
        assert!(!is_safe_expr("x; exit"));
        assert!(!is_safe_expr("x\ny"));
    }

    #[tokio::test]
    async fn unhealthy_returns_failure_without_spawn() {
        let backend = Macaulay2Backend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::Macaulay2Dimension {
                vars: vec!["x".into()],
                polys: vec!["x".into()],
            })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[tokio::test]
    async fn unsafe_var_rejected_before_spawn() {
        let backend = Macaulay2Backend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::Macaulay2GroebnerBasis {
                vars: vec!["x; exit".into()],
                polys: vec!["x".into()],
            })
            .await
            .unwrap();
        assert!(
            matches!(&r, CoprocessorOutcome::Failure(msg) if msg.contains("unsafe variable")),
            "got {r:?}"
        );
    }

    #[test]
    fn m2_ring_def_format() {
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        assert_eq!(m2_ring_def(&vars), "R = QQ[x,y,z];\n");
    }

    #[test]
    fn m2_ideal_def_format() {
        let polys = vec!["x^2-1".to_string(), "y-x".to_string()];
        assert_eq!(m2_ideal_def("I", &polys), "I = ideal(x^2-1, y-x);\n");
    }

    #[test]
    fn extract_m2_output_strips_annotations() {
        // M2 result annotations start with 'o'; print output does not.
        let raw = "o1 = QQ[x,y]\no2 : Ring\n1\n";
        let result = extract_m2_output(raw);
        assert_eq!(result, "1");
    }

    #[test]
    fn backend_construction_probes_path() {
        let b = Macaulay2Backend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::Macaulay2);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
