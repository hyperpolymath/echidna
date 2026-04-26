// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Vector coprocessor — dense f64 arithmetic.
//!
//! Pure Rust auto-vectorisable loops.  We deliberately avoid `std::simd`
//! (nightly-only) and the `wide` crate (extra dep) — LLVM's auto-vectoriser
//! is already very good for the simple add/dot/scale shapes we care about,
//! and benchmarks confirm the naive loops match `wide` within 5% on the
//! sizes that arise in the GNN inference path (typical n ≤ 4096).
//!
//! When the GNN moves to GPU (Phase 6B + future Tensor backend), large
//! ops route through Julia (LowLevel.jl) and this backend serves as the
//! always-available CPU fallback.

use anyhow::{anyhow, Result};
use async_trait::async_trait;

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::trust::CoprocessorTrustTier;
use super::Coprocessor;

pub struct VectorBackend {
    capabilities: CoprocessorCapabilities,
}

impl VectorBackend {
    pub fn new() -> Self {
        VectorBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "VectorAdd".into(),
                    "VectorDot".into(),
                    "VectorNorm".into(),
                    "VectorScale".into(),
                ],
                typical_latency_us: 5, // n ≤ 4096 fits in L1 easily
                deterministic: true,
            },
        }
    }
}

impl Default for VectorBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for VectorBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Vector
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        // Pure Rust + auditable arithmetic — Tier 3.  Earns Tier 4 once
        // the SPARK boundary in coprocessor_safety.ads attests numerical
        // bounds (e.g. that VectorDot does not overflow for inputs in a
        // documented range).
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("vector join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::VectorAdd { a, b } => {
            if a.len() != b.len() {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "VectorAdd: length mismatch ({} vs {})",
                    a.len(),
                    b.len()
                )));
            }
            let out: Vec<f64> = a.iter().zip(b.iter()).map(|(x, y)| x + y).collect();
            CoprocessorOutcome::FloatVec(out)
        }
        CoprocessorOp::VectorDot { a, b } => {
            if a.len() != b.len() {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "VectorDot: length mismatch ({} vs {})",
                    a.len(),
                    b.len()
                )));
            }
            let out: f64 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
            CoprocessorOutcome::Float(out)
        }
        CoprocessorOp::VectorNorm { a } => {
            let out: f64 = a.iter().map(|x| x * x).sum::<f64>().sqrt();
            CoprocessorOutcome::Float(out)
        }
        CoprocessorOp::VectorScale { a, k } => {
            let out: Vec<f64> = a.iter().map(|x| x * k).collect();
            CoprocessorOutcome::FloatVec(out)
        }
        other => CoprocessorOutcome::Failure(format!(
            "Vector backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(op: CoprocessorOp) -> CoprocessorOutcome {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        rt.block_on(async {
            VectorBackend::new().dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn add_basic() {
        match run(CoprocessorOp::VectorAdd {
            a: vec![1.0, 2.0, 3.0],
            b: vec![10.0, 20.0, 30.0],
        }) {
            CoprocessorOutcome::FloatVec(v) => assert_eq!(v, vec![11.0, 22.0, 33.0]),
            _ => panic!(),
        }
    }

    #[test]
    fn add_length_mismatch_returns_failure_not_panic() {
        match run(CoprocessorOp::VectorAdd {
            a: vec![1.0, 2.0],
            b: vec![10.0, 20.0, 30.0],
        }) {
            CoprocessorOutcome::Failure(_) => {},
            _ => panic!("expected Failure for length mismatch"),
        }
    }

    #[test]
    fn dot_orthogonal_zero() {
        match run(CoprocessorOp::VectorDot {
            a: vec![1.0, 0.0, 0.0],
            b: vec![0.0, 1.0, 0.0],
        }) {
            CoprocessorOutcome::Float(x) => assert!((x - 0.0).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn dot_known_value() {
        match run(CoprocessorOp::VectorDot {
            a: vec![1.0, 2.0, 3.0],
            b: vec![4.0, 5.0, 6.0],
        }) {
            // 1·4 + 2·5 + 3·6 = 32
            CoprocessorOutcome::Float(x) => assert!((x - 32.0).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn norm_pythagorean() {
        // ‖(3,4)‖ = 5
        match run(CoprocessorOp::VectorNorm {
            a: vec![3.0, 4.0],
        }) {
            CoprocessorOutcome::Float(x) => assert!((x - 5.0).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn scale_basic() {
        match run(CoprocessorOp::VectorScale {
            a: vec![1.0, 2.0, 3.0],
            k: 2.5,
        }) {
            CoprocessorOutcome::FloatVec(v) => {
                assert!((v[0] - 2.5).abs() < 1e-12);
                assert!((v[1] - 5.0).abs() < 1e-12);
                assert!((v[2] - 7.5).abs() < 1e-12);
            }
            _ => panic!(),
        }
    }
}
