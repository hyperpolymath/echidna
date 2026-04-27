// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Singular polynomial-algebra coprocessor — subprocess to `Singular`.
//!
//! Provides Gröbner basis computation, ideal membership testing, and Krull
//! dimension over polynomial rings k[vars] with arbitrary characteristic.
//! Trust tier `ExternalSubprocess` (Tier 1).
//!
//! Input variable names and polynomial expressions are validated against safe
//! character whitelists.  The Singular script is piped to stdin of the
//! `Singular --quiet` subprocess with a 30-second timeout.
//!
//! Ring ordering is `dp` (graded reverse lex — standard for Gröbner bases).
//! `ring_char = 0` selects the rational field Q; a positive prime selects GF(p).

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

pub struct SingularBackend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl SingularBackend {
    pub fn new() -> Self {
        let health = if which("Singular") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        SingularBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "SingularGroebner".into(),
                    "SingularIdealMembership".into(),
                    "SingularDimension".into(),
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

/// Variable names: ASCII letter first, then alphanumeric or underscore.
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

/// Build a Singular ring declaration line.
fn ring_def(char: u32, vars: &[String]) -> String {
    format!("ring r = {char},({vars}),dp;", vars = vars.join(","))
}

/// Build a Singular ideal declaration from a list of polynomial strings.
fn ideal_def(name: &str, polys: &[String]) -> String {
    format!("ideal {name} = {polys};", polys = polys.join(", "))
}

/// Extract generator values from Singular's `g;` output lines.
/// Singular prints `g[1]=expr\ng[2]=expr\n...` for `ideal g`.
fn extract_generators(output: &str, ideal_name: &str) -> Vec<String> {
    let prefix = format!("{ideal_name}[");
    output
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            if line.starts_with(&prefix) {
                line.splitn(2, '=').nth(1).map(|s| s.to_string())
            } else {
                None
            }
        })
        .collect()
}

impl Default for SingularBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for SingularBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Singular
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
                "Singular: Singular not found on PATH".into(),
            ));
        }
        match op {
            CoprocessorOp::SingularGroebner { ring_char, vars, polys } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularGroebner: unsafe variable name '{bad}'"
                    )));
                }
                if let Some(bad) = polys.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularGroebner: unsafe polynomial '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}\n{ideal}\nideal g = std(I);\ng;\nexit;\n",
                    ring = ring_def(ring_char, &vars),
                    ideal = ideal_def("I", &polys),
                );
                let out = run_singular(&script).await?;
                let gens = extract_generators(&out, "g");
                Ok(CoprocessorOutcome::Text(gens.join("\n")))
            }
            CoprocessorOp::SingularIdealMembership { ring_char, vars, poly, ideal } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularIdealMembership: unsafe variable '{bad}'"
                    )));
                }
                if !is_safe_expr(&poly) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularIdealMembership: unsafe polynomial '{poly}'"
                    )));
                }
                if let Some(bad) = ideal.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularIdealMembership: unsafe ideal generator '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}\n{ideal_decl}\npoly f = {poly};\nprint(reduce(f, std(I)) == 0);\nexit;\n",
                    ring = ring_def(ring_char, &vars),
                    ideal_decl = ideal_def("I", &ideal),
                );
                let out = run_singular(&script).await?;
                // Singular prints "1" for true, "0" for false.
                let result = out.trim();
                match result {
                    "1" => Ok(CoprocessorOutcome::Boolean(true)),
                    "0" => Ok(CoprocessorOutcome::Boolean(false)),
                    other => Ok(CoprocessorOutcome::Failure(format!(
                        "SingularIdealMembership: unexpected output '{other}'"
                    ))),
                }
            }
            CoprocessorOp::SingularDimension { ring_char, vars, polys } => {
                if let Some(bad) = vars.iter().find(|v| !is_safe_var(v)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularDimension: unsafe variable '{bad}'"
                    )));
                }
                if let Some(bad) = polys.iter().find(|p| !is_safe_expr(p)) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "SingularDimension: unsafe polynomial '{bad}'"
                    )));
                }
                let script = format!(
                    "{ring}\n{ideal}\nprint(dim(std(I)));\nexit;\n",
                    ring = ring_def(ring_char, &vars),
                    ideal = ideal_def("I", &polys),
                );
                let out = run_singular(&script).await?;
                let trimmed = out.trim();
                Ok(CoprocessorOutcome::BigInt(trimmed.to_string()))
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Singular backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

async fn run_singular(script: &str) -> Result<String> {
    let mut child = Command::new("Singular")
        .arg("--quiet")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|e| anyhow!("Singular spawn: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .await
            .map_err(|e| anyhow!("Singular stdin write: {e}"))?;
    }

    let out = tokio::time::timeout(TIMEOUT, child.wait_with_output())
        .await
        .map_err(|_| anyhow!("Singular timed out after 30s"))?
        .map_err(|e| anyhow!("Singular wait: {e}"))?;

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(anyhow!(
            "Singular exit {}: {}",
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
        assert!(is_safe_var("my_var"));
        assert!(!is_safe_var(""));
        assert!(!is_safe_var("1x"));
        assert!(!is_safe_var("x;y"));
        assert!(!is_safe_var("x y"));
    }

    #[test]
    fn safe_expr_validation() {
        assert!(is_safe_expr("x^2-y^2"));
        assert!(is_safe_expr("x^2+2*x*y+y^2"));
        assert!(!is_safe_expr(""));
        assert!(!is_safe_expr("x; system(\"id\")"));
        assert!(!is_safe_expr("x$"));
    }

    #[tokio::test]
    async fn unhealthy_returns_failure_without_spawn() {
        let backend = SingularBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::SingularDimension {
                ring_char: 0,
                vars: vec!["x".into()],
                polys: vec!["x".into()],
            })
            .await
            .unwrap();
        assert!(matches!(r, CoprocessorOutcome::Failure(_)));
    }

    #[tokio::test]
    async fn unsafe_variable_rejected_before_spawn() {
        let backend = SingularBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Healthy,
        };
        let r = backend
            .dispatch(CoprocessorOp::SingularGroebner {
                ring_char: 0,
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
    fn extract_generators_parses_output() {
        let output = "g[1]=x-y\ng[2]=y^2-1\n";
        let gens = extract_generators(output, "g");
        assert_eq!(gens, vec!["x-y", "y^2-1"]);
    }

    #[test]
    fn ring_def_format() {
        let vars = vec!["x".to_string(), "y".to_string()];
        assert_eq!(ring_def(0, &vars), "ring r = 0,(x,y),dp;");
        assert_eq!(ring_def(32003, &vars), "ring r = 32003,(x,y),dp;");
    }

    #[test]
    fn backend_construction_probes_path() {
        let b = SingularBackend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::Singular);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
