// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Physics coprocessor — numerical ODE integration + invariant oracles.
//!
//! Pairs with the future KeYmaera X backend.  KeYmaera X proves that a
//! continuous trajectory satisfies a differential dynamic logic formula;
//! this backend independently integrates the same trajectory numerically
//! so the prover-side trust pipeline can cross-check the symbolic claim
//! against a concrete witness.  A symbolic proof of `∀t. E(x(t),p(t)) = E₀`
//! is much more credible when the numerical integrator confirms that
//! `|E(x_n,p_n) - E₀| < 10⁻⁸` over 10⁴ RK4 steps.
//!
//! Pure Rust — no external deps.  ODE kernels are encoded by name +
//! parameters (closures don't cross the Serde wire), with the supported
//! kernels documented in `types.rs`.  Phase 6B + 7 add richer kernels and
//! the Julia bridge to InvestigativeJournalist.jl numerics.

use anyhow::{anyhow, Result};
use async_trait::async_trait;

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::trust::CoprocessorTrustTier;
use super::Coprocessor;

pub struct PhysicsBackend {
    capabilities: CoprocessorCapabilities,
}

impl PhysicsBackend {
    pub fn new() -> Self {
        PhysicsBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "PhysicsRk4Step".into(),
                    "PhysicsHarmonicEnergy".into(),
                ],
                typical_latency_us: 5,
                deterministic: true,
            },
        }
    }
}

impl Default for PhysicsBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for PhysicsBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Physics
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("physics join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::PhysicsRk4Step {
            kernel,
            params,
            x,
            dt,
        } => match rk4_step(&kernel, &params, &x, dt) {
            Ok(next) => CoprocessorOutcome::FloatVec(next),
            Err(msg) => CoprocessorOutcome::Failure(msg),
        },
        CoprocessorOp::PhysicsHarmonicEnergy { x, p, omega } => {
            CoprocessorOutcome::Float(0.5 * p * p + 0.5 * omega * omega * x * x)
        }
        other => CoprocessorOutcome::Failure(format!(
            "Physics backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

/// Classical fourth-order Runge-Kutta step.
///
/// `f(x)` is a kernel selected by name with a parameter vector:
/// - `"harmonic-oscillator"` — params = [omega]; x = [position, momentum];
///   ẋ₀ = x₁,  ẋ₁ = -ω²·x₀.
/// - `"exponential-decay"`   — params = [lambda]; ẋᵢ = -λ·xᵢ.
/// - `"linear"`              — params = [a, b]; ẋᵢ = a·xᵢ + b.
fn rk4_step(kernel: &str, params: &[f64], x: &[f64], dt: f64) -> std::result::Result<Vec<f64>, String> {
    let f = build_kernel(kernel, params)?;
    let n = x.len();

    let k1 = f(x);
    if k1.len() != n {
        return Err(format!("rk4: kernel returned {} components, expected {n}", k1.len()));
    }

    let x2: Vec<f64> = x.iter().zip(&k1).map(|(xi, ki)| xi + 0.5 * dt * ki).collect();
    let k2 = f(&x2);

    let x3: Vec<f64> = x.iter().zip(&k2).map(|(xi, ki)| xi + 0.5 * dt * ki).collect();
    let k3 = f(&x3);

    let x4: Vec<f64> = x.iter().zip(&k3).map(|(xi, ki)| xi + dt * ki).collect();
    let k4 = f(&x4);

    let next: Vec<f64> = (0..n)
        .map(|i| x[i] + dt / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]))
        .collect();
    Ok(next)
}

type KernelFn = Box<dyn Fn(&[f64]) -> Vec<f64>>;

fn build_kernel(name: &str, params: &[f64]) -> std::result::Result<KernelFn, String> {
    match name {
        "harmonic-oscillator" => {
            if params.len() != 1 {
                return Err(format!(
                    "harmonic-oscillator: expected 1 param (omega), got {}",
                    params.len()
                ));
            }
            let omega = params[0];
            Ok(Box::new(move |x: &[f64]| {
                if x.len() != 2 {
                    return vec![]; // signals length error to caller
                }
                vec![x[1], -omega * omega * x[0]]
            }))
        }
        "exponential-decay" => {
            if params.len() != 1 {
                return Err(format!(
                    "exponential-decay: expected 1 param (lambda), got {}",
                    params.len()
                ));
            }
            let lambda = params[0];
            Ok(Box::new(move |x: &[f64]| x.iter().map(|xi| -lambda * xi).collect()))
        }
        "linear" => {
            if params.len() != 2 {
                return Err(format!(
                    "linear: expected 2 params (a, b), got {}",
                    params.len()
                ));
            }
            let (a, b) = (params[0], params[1]);
            Ok(Box::new(move |x: &[f64]| x.iter().map(|xi| a * xi + b).collect()))
        }
        other => Err(format!("unknown kernel: {other}")),
    }
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
            PhysicsBackend::new().dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn harmonic_energy_known() {
        // E(x=1, p=0, ω=1) = ½·0² + ½·1²·1² = 0.5
        match run(CoprocessorOp::PhysicsHarmonicEnergy {
            x: 1.0,
            p: 0.0,
            omega: 1.0,
        }) {
            CoprocessorOutcome::Float(e) => assert!((e - 0.5).abs() < 1e-12),
            _ => panic!(),
        }
    }

    #[test]
    fn rk4_harmonic_one_period_returns_to_origin() {
        // Harmonic oscillator with ω = 1 has period 2π.  Integrate for
        // 2π / dt steps; final state should match the initial state to
        // RK4 accuracy (error ~ dt⁴ ≈ 10⁻⁹ for dt = 0.001).
        let omega = 1.0;
        let dt = 0.001;
        let n_steps = (2.0 * std::f64::consts::PI / dt) as usize;
        let mut x = vec![1.0, 0.0]; // start at (x=1, p=0)
        for _ in 0..n_steps {
            let next = match run(CoprocessorOp::PhysicsRk4Step {
                kernel: "harmonic-oscillator".into(),
                params: vec![omega],
                x: x.clone(),
                dt,
            }) {
                CoprocessorOutcome::FloatVec(v) => v,
                _ => panic!(),
            };
            x = next;
        }
        // After one full period we should be near the start.  Tolerance
        // generous because we accumulate over ~6283 RK4 steps.
        assert!(
            (x[0] - 1.0).abs() < 1e-3,
            "x[0] = {}",
            x[0]
        );
        assert!((x[1] - 0.0).abs() < 1e-3, "x[1] = {}", x[1]);
    }

    #[test]
    fn rk4_exponential_decay_halflife() {
        // ẋ = -λx with λ = ln 2 / T_half.  After T_half, x should halve.
        let half_life = 1.0;
        let lambda = std::f64::consts::LN_2 / half_life;
        let dt = 0.001;
        let n_steps = (half_life / dt) as usize;
        let mut x = vec![1.0];
        for _ in 0..n_steps {
            x = match run(CoprocessorOp::PhysicsRk4Step {
                kernel: "exponential-decay".into(),
                params: vec![lambda],
                x: x.clone(),
                dt,
            }) {
                CoprocessorOutcome::FloatVec(v) => v,
                _ => panic!(),
            };
        }
        assert!((x[0] - 0.5).abs() < 1e-6, "x[0] = {}", x[0]);
    }

    #[test]
    fn unknown_kernel_returns_failure() {
        match run(CoprocessorOp::PhysicsRk4Step {
            kernel: "non-existent-kernel".into(),
            params: vec![],
            x: vec![1.0],
            dt: 0.1,
        }) {
            CoprocessorOutcome::Failure(_) => {},
            _ => panic!(),
        }
    }
}
