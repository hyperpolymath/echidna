// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! FPGA / hardware-synthesis coprocessor — subprocess to yosys.
//!
//! Backs proof obligations about Verilog / SystemVerilog hardware modules.
//! Trust tier `ExternalSubprocess` (Tier 1) — yosys is a witness-emitting
//! tool, not a certifying prover; the prover-side trust pipeline must
//! cross-check or re-verify any claim that depends on it.
//!
//! The op writes the supplied Verilog to a temp file, runs
//! `yosys -p "synth -top <top_module>" <file>`, and returns the netlist
//! output.  Fail with a clear diagnostic if yosys is not on PATH.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::io::Write;
use std::process::Stdio;
use tempfile::NamedTempFile;
use tokio::process::Command;

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

pub struct FpgaBackend {
    capabilities: CoprocessorCapabilities,
    health: CoprocessorHealth,
}

impl FpgaBackend {
    pub fn new() -> Self {
        // Probe for yosys at construction time — Health flips Unhealthy
        // immediately if it's not on PATH so MetaController can route around.
        let health = if which("yosys") {
            CoprocessorHealth::Healthy
        } else {
            CoprocessorHealth::Unhealthy
        };
        FpgaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec!["FpgaYosysSynth".into()],
                typical_latency_us: 500_000, // half-second-ish for tiny modules
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

impl Default for FpgaBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for FpgaBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Fpga
    }
    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }
    fn health(&self) -> CoprocessorHealth {
        self.health
    }
    fn trust_tier(&self) -> CoprocessorTrustTier {
        // External subprocess oracle — Tier 1.
        CoprocessorTrustTier::ExternalSubprocess
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        match op {
            CoprocessorOp::FpgaYosysSynth { verilog, top_module } => {
                if self.health == CoprocessorHealth::Unhealthy {
                    return Ok(CoprocessorOutcome::Failure(
                        "FpgaYosysSynth: yosys not found on PATH".into(),
                    ));
                }
                if !is_safe_module_name(&top_module) {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "FpgaYosysSynth: unsafe top_module name '{top_module}' — must be alphanum + underscore"
                    )));
                }
                Ok(yosys_synth(&verilog, &top_module).await)
            }
            other => Ok(CoprocessorOutcome::Failure(format!(
                "Fpga backend does not support {:?}",
                std::mem::discriminant(&other)
            ))),
        }
    }
}

/// Restrict top-module name to a conservative shape so we don't have to
/// quote-escape it through yosys's `-p` script.  Verilog identifiers are
/// already this shape; this is just a defence-in-depth boundary check.
fn is_safe_module_name(s: &str) -> bool {
    !s.is_empty()
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && s.chars().next().map(|c| !c.is_ascii_digit()).unwrap_or(false)
}

async fn yosys_synth(verilog: &str, top_module: &str) -> CoprocessorOutcome {
    // Stage the verilog to a temp file (yosys reads from disk).
    let mut tmp = match NamedTempFile::new() {
        Ok(t) => t,
        Err(e) => return CoprocessorOutcome::Failure(format!("tempfile: {e}")),
    };
    if let Err(e) = tmp.write_all(verilog.as_bytes()) {
        return CoprocessorOutcome::Failure(format!("write verilog: {e}"));
    }
    let path = tmp.path().to_path_buf();

    // Run yosys with the synth flow.  -q for quiet (status messages
    // suppressed), -p for inline script.
    let script = format!("synth -top {top_module}; write_verilog");
    let out = match Command::new("yosys")
        .arg("-q")
        .arg("-p")
        .arg(&script)
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .await
    {
        Ok(o) => o,
        Err(e) => return CoprocessorOutcome::Failure(format!("yosys spawn: {e}")),
    };

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return CoprocessorOutcome::Failure(format!(
            "yosys exit {}: {}",
            out.status.code().unwrap_or(-1),
            stderr.lines().take(5).collect::<Vec<_>>().join(" | ")
        ));
    }

    let netlist = String::from_utf8_lossy(&out.stdout).to_string();
    CoprocessorOutcome::Hex(hex(netlist.as_bytes()))
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

    #[tokio::test]
    async fn unsafe_module_name_rejected_without_invoking_yosys() {
        let backend = FpgaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec!["FpgaYosysSynth".into()],
                typical_latency_us: 0,
                deterministic: true,
            },
            // Force Healthy so the unsafe-name check is the gate (not the missing-yosys path).
            health: CoprocessorHealth::Healthy,
        };
        match backend
            .dispatch(CoprocessorOp::FpgaYosysSynth {
                verilog: "module m; endmodule".into(),
                top_module: "bad name; rm -rf /".into(),
            })
            .await
            .unwrap()
        {
            CoprocessorOutcome::Failure(msg) => assert!(msg.contains("unsafe")),
            _ => panic!("expected Failure on unsafe module name"),
        }
    }

    #[tokio::test]
    async fn unhealthy_backend_returns_failure_without_spawn() {
        let backend = FpgaBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec!["FpgaYosysSynth".into()],
                typical_latency_us: 0,
                deterministic: true,
            },
            health: CoprocessorHealth::Unhealthy,
        };
        match backend
            .dispatch(CoprocessorOp::FpgaYosysSynth {
                verilog: "module m; endmodule".into(),
                top_module: "m".into(),
            })
            .await
            .unwrap()
        {
            CoprocessorOutcome::Failure(msg) => {
                assert!(msg.contains("yosys not found"));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn module_name_safety_rules() {
        assert!(is_safe_module_name("foo"));
        assert!(is_safe_module_name("foo_bar"));
        assert!(is_safe_module_name("foo_42"));
        assert!(!is_safe_module_name(""));
        assert!(!is_safe_module_name("42foo"));
        assert!(!is_safe_module_name("foo bar"));
        assert!(!is_safe_module_name("foo;bar"));
        assert!(!is_safe_module_name("foo-bar"));
    }

    #[test]
    fn backend_construction_probes_path() {
        // Just check that construction doesn't panic — health depends on
        // whether yosys is installed in the test env.
        let b = FpgaBackend::new();
        assert!(matches!(
            b.health(),
            CoprocessorHealth::Healthy | CoprocessorHealth::Unhealthy
        ));
        assert_eq!(b.kind(), CoprocessorKind::Fpga);
        assert_eq!(b.trust_tier(), CoprocessorTrustTier::ExternalSubprocess);
    }
}
