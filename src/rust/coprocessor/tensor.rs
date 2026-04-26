// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Tensor coprocessor — dense linear algebra via `nalgebra`.
//!
//! Supports matrix multiply, transpose, trace, determinant.  Backs the
//! GNN node-embedding aggregation pipeline (where ≤ 256-d vectors are
//! batched into matrices), and the Pareto-frontier dominance kernels in
//! the prover-trust pipeline.
//!
//! Larger ops (n > 4096, batched > 64) should route through the Julia
//! bridge to LowLevel.jl + CUDA — Phase 6B will add the routing.  This
//! backend is the always-available CPU baseline.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use nalgebra::DMatrix;

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::trust::CoprocessorTrustTier;
use super::Coprocessor;

pub struct TensorBackend {
    capabilities: CoprocessorCapabilities,
}

impl TensorBackend {
    pub fn new() -> Self {
        TensorBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "TensorMatMul".into(),
                    "TensorTranspose".into(),
                    "TensorTrace".into(),
                    "TensorDeterminant".into(),
                ],
                typical_latency_us: 50,
                deterministic: true,
            },
        }
    }
}

impl Default for TensorBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for TensorBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Tensor
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        // nalgebra is well-audited (BSD-3) — Tier 3.
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("tensor join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::TensorMatMul { a, b } => match (rows_to_dmat(&a), rows_to_dmat(&b)) {
            (Some(am), Some(bm)) if am.ncols() == bm.nrows() => {
                let prod = am * bm;
                CoprocessorOutcome::FloatMatrix(dmat_to_rows(&prod))
            }
            (Some(am), Some(bm)) => CoprocessorOutcome::Failure(format!(
                "TensorMatMul: dimension mismatch ({}x{} · {}x{})",
                am.nrows(), am.ncols(), bm.nrows(), bm.ncols()
            )),
            _ => CoprocessorOutcome::Failure(
                "TensorMatMul: ragged input — every row must have equal length".into(),
            ),
        },
        CoprocessorOp::TensorTranspose { a } => match rows_to_dmat(&a) {
            Some(am) => CoprocessorOutcome::FloatMatrix(dmat_to_rows(&am.transpose())),
            None => CoprocessorOutcome::Failure("TensorTranspose: ragged input".into()),
        },
        CoprocessorOp::TensorTrace { a } => match rows_to_dmat(&a) {
            Some(am) if am.is_square() => CoprocessorOutcome::Float(am.trace()),
            Some(_) => {
                CoprocessorOutcome::Failure("TensorTrace: matrix must be square".into())
            }
            None => CoprocessorOutcome::Failure("TensorTrace: ragged input".into()),
        },
        CoprocessorOp::TensorDeterminant { a } => match rows_to_dmat(&a) {
            Some(am) if am.is_square() => CoprocessorOutcome::Float(am.determinant()),
            Some(_) => CoprocessorOutcome::Failure(
                "TensorDeterminant: matrix must be square".into(),
            ),
            None => CoprocessorOutcome::Failure("TensorDeterminant: ragged input".into()),
        },
        other => CoprocessorOutcome::Failure(format!(
            "Tensor backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

fn rows_to_dmat(rows: &[Vec<f64>]) -> Option<DMatrix<f64>> {
    if rows.is_empty() {
        return Some(DMatrix::zeros(0, 0));
    }
    let cols = rows[0].len();
    if !rows.iter().all(|r| r.len() == cols) {
        return None;
    }
    let mut m = DMatrix::zeros(rows.len(), cols);
    for (i, row) in rows.iter().enumerate() {
        for (j, &v) in row.iter().enumerate() {
            m[(i, j)] = v;
        }
    }
    Some(m)
}

fn dmat_to_rows(m: &DMatrix<f64>) -> Vec<Vec<f64>> {
    (0..m.nrows())
        .map(|i| (0..m.ncols()).map(|j| m[(i, j)]).collect())
        .collect()
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
            TensorBackend::new().dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn matmul_2x2_identity() {
        // I·M = M
        match run(CoprocessorOp::TensorMatMul {
            a: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            b: vec![vec![3.0, 4.0], vec![5.0, 6.0]],
        }) {
            CoprocessorOutcome::FloatMatrix(m) => {
                assert_eq!(m, vec![vec![3.0, 4.0], vec![5.0, 6.0]]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn matmul_dimension_mismatch_returns_failure() {
        match run(CoprocessorOp::TensorMatMul {
            a: vec![vec![1.0, 2.0]],            // 1×2
            b: vec![vec![1.0], vec![2.0], vec![3.0]], // 3×1
        }) {
            CoprocessorOutcome::Failure(_) => {},
            _ => panic!("expected Failure on dim mismatch"),
        }
    }

    #[test]
    fn transpose_known() {
        match run(CoprocessorOp::TensorTranspose {
            a: vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]],
        }) {
            CoprocessorOutcome::FloatMatrix(m) => {
                assert_eq!(m, vec![vec![1.0, 4.0], vec![2.0, 5.0], vec![3.0, 6.0]]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn trace_diagonal_sum() {
        match run(CoprocessorOp::TensorTrace {
            a: vec![vec![1.0, 9.0], vec![9.0, 4.0]],
        }) {
            CoprocessorOutcome::Float(t) => assert!((t - 5.0).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn determinant_2x2() {
        // |1 2|
        // |3 4| = 1·4 - 2·3 = -2
        match run(CoprocessorOp::TensorDeterminant {
            a: vec![vec![1.0, 2.0], vec![3.0, 4.0]],
        }) {
            CoprocessorOutcome::Float(d) => assert!((d - (-2.0)).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn determinant_non_square_returns_failure() {
        match run(CoprocessorOp::TensorDeterminant {
            a: vec![vec![1.0, 2.0, 3.0]],
        }) {
            CoprocessorOutcome::Failure(_) => {},
            _ => panic!(),
        }
    }
}
