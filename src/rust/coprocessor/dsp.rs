// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! DSP coprocessor — FFT / IFFT / window functions via `rustfft`.
//!
//! Pairs with the symbolic-protocol provers (Tamarin, ProVerif) for proof
//! obligations that involve communication channels and signal-bearing
//! protocols.  The FFT is the canonical computational oracle for
//! frequency-domain claims in such proofs.
//!
//! Wire format choices:
//! - FFT input/output: `Vec<f64>` (samples) → `FloatVec` of length 2N
//!   with real/imag interleaved.  Avoids inventing a new `Complex` outcome.
//! - Window functions: in-place modification returned as a fresh `FloatVec`.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use rustfft::{num_complex::Complex, FftPlanner};

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

pub struct DspBackend {
    capabilities: CoprocessorCapabilities,
}

impl DspBackend {
    pub fn new() -> Self {
        DspBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "DspFft".into(),
                    "DspIfft".into(),
                    "DspHannWindow".into(),
                    "DspHammingWindow".into(),
                ],
                typical_latency_us: 100,
                deterministic: true,
            },
        }
    }
}

impl Default for DspBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for DspBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Dsp
    }
    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }
    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }
    fn trust_tier(&self) -> CoprocessorTrustTier {
        // rustfft is widely audited (Apache-2.0/MIT) — Tier 3.
        CoprocessorTrustTier::LibraryWrapped
    }
    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("dsp join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::DspFft { samples } => {
            if samples.is_empty() {
                return Ok(CoprocessorOutcome::FloatVec(vec![]));
            }
            let mut buf: Vec<Complex<f64>> =
                samples.iter().map(|&s| Complex::new(s, 0.0)).collect();
            let mut planner = FftPlanner::<f64>::new();
            let fft = planner.plan_fft_forward(buf.len());
            fft.process(&mut buf);
            let interleaved: Vec<f64> =
                buf.into_iter().flat_map(|c| [c.re, c.im]).collect();
            CoprocessorOutcome::FloatVec(interleaved)
        }
        CoprocessorOp::DspIfft { spectrum } => {
            if spectrum.is_empty() {
                return Ok(CoprocessorOutcome::FloatVec(vec![]));
            }
            if spectrum.len() % 2 != 0 {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "DspIfft: spectrum length must be even (re/im interleaved); got {}",
                    spectrum.len()
                )));
            }
            let n = spectrum.len() / 2;
            let mut buf: Vec<Complex<f64>> = (0..n)
                .map(|i| Complex::new(spectrum[2 * i], spectrum[2 * i + 1]))
                .collect();
            let mut planner = FftPlanner::<f64>::new();
            let fft = planner.plan_fft_inverse(n);
            fft.process(&mut buf);
            // rustfft inverse is unscaled; divide by N for round-trip identity.
            let scale = 1.0 / (n as f64);
            let real: Vec<f64> = buf.into_iter().map(|c| c.re * scale).collect();
            CoprocessorOutcome::FloatVec(real)
        }
        CoprocessorOp::DspHannWindow { samples } => {
            CoprocessorOutcome::FloatVec(apply_window(&samples, hann))
        }
        CoprocessorOp::DspHammingWindow { samples } => {
            CoprocessorOutcome::FloatVec(apply_window(&samples, hamming))
        }
        other => CoprocessorOutcome::Failure(format!(
            "Dsp backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

fn apply_window(samples: &[f64], w: fn(usize, usize) -> f64) -> Vec<f64> {
    let n = samples.len();
    if n < 2 {
        return samples.to_vec();
    }
    samples.iter().enumerate().map(|(i, &s)| s * w(i, n)).collect()
}

fn hann(i: usize, n: usize) -> f64 {
    let two_pi = 2.0 * std::f64::consts::PI;
    0.5 * (1.0 - (two_pi * i as f64 / (n - 1) as f64).cos())
}

fn hamming(i: usize, n: usize) -> f64 {
    let two_pi = 2.0 * std::f64::consts::PI;
    0.54 - 0.46 * (two_pi * i as f64 / (n - 1) as f64).cos()
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
            DspBackend::new().dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn fft_dc_signal_concentrates_in_bin_0() {
        // FFT of a constant signal: all energy in DC bin.
        let n = 8;
        let samples = vec![1.0; n];
        match run(CoprocessorOp::DspFft { samples }) {
            CoprocessorOutcome::FloatVec(v) => {
                assert_eq!(v.len(), 2 * n);
                // Bin 0 real should be ~N (sum of samples), all others ~0.
                assert!((v[0] - n as f64).abs() < 1e-9, "bin 0 re = {}", v[0]);
                for i in 1..n {
                    assert!(v[2 * i].abs() < 1e-9, "bin {i} re = {}", v[2 * i]);
                    assert!(v[2 * i + 1].abs() < 1e-9, "bin {i} im = {}", v[2 * i + 1]);
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn fft_then_ifft_round_trip_to_input() {
        let samples: Vec<f64> = (0..8).map(|i| (i as f64).sin()).collect();
        let spec = match run(CoprocessorOp::DspFft { samples: samples.clone() }) {
            CoprocessorOutcome::FloatVec(v) => v,
            _ => panic!(),
        };
        match run(CoprocessorOp::DspIfft { spectrum: spec }) {
            CoprocessorOutcome::FloatVec(reconstructed) => {
                assert_eq!(reconstructed.len(), samples.len());
                for (a, b) in samples.iter().zip(reconstructed.iter()) {
                    assert!((a - b).abs() < 1e-9, "{a} vs {b}");
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn ifft_odd_length_returns_failure() {
        match run(CoprocessorOp::DspIfft { spectrum: vec![1.0, 2.0, 3.0] }) {
            CoprocessorOutcome::Failure(_) => {}
            _ => panic!("expected Failure on odd-length spectrum"),
        }
    }

    #[test]
    fn hann_window_zero_at_endpoints() {
        let n = 16;
        let samples = vec![1.0; n];
        match run(CoprocessorOp::DspHannWindow { samples }) {
            CoprocessorOutcome::FloatVec(v) => {
                assert!(v[0].abs() < 1e-12);
                assert!(v[n - 1].abs() < 1e-12);
                // Mid-point is 1.0 only for odd N; for even N, near 1.
                assert!(v[n / 2] > 0.9);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn hamming_window_nonzero_at_endpoints() {
        // Hamming differs from Hann: w[0] = 0.08 (not 0).
        let n = 16;
        let samples = vec![1.0; n];
        match run(CoprocessorOp::DspHammingWindow { samples }) {
            CoprocessorOutcome::FloatVec(v) => {
                assert!((v[0] - 0.08).abs() < 1e-9, "v[0] = {}", v[0]);
            }
            _ => panic!(),
        }
    }
}
