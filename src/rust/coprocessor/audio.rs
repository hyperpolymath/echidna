// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Audio coprocessor — synthesis (sine wave + completion chime).
//!
//! Generates 16-bit PCM in a WAV container, returned Hex-encoded so the
//! result travels through `CoprocessorOutcome::Hex` cleanly.  Pure Rust;
//! no audio-library dependency.
//!
//! Use cases:
//! - The Stop hook variant emits a completion chime via `paplay` — but we
//!   also want a programmable oracle for proofs about audio-bearing
//!   protocols (rare but real for KeYmaera X cyber-physical targets).
//! - Tests that need a deterministic audio buffer can request a fixed
//!   sine wave and compare hashes.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::fmt::Write;

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

pub struct AudioBackend {
    capabilities: CoprocessorCapabilities,
}

impl AudioBackend {
    pub fn new() -> Self {
        AudioBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "AudioSineWave".into(),
                    "AudioCompletionChime".into(),
                ],
                typical_latency_us: 200,
                deterministic: true,
            },
        }
    }
}

impl Default for AudioBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for AudioBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Audio
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
            .map_err(|e| anyhow!("audio join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::AudioSineWave {
            frequency_hz,
            duration_ms,
            sample_rate,
        } => {
            if !(8_000..=192_000).contains(&sample_rate) {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "AudioSineWave: sample_rate {} outside [8000, 192000]",
                    sample_rate
                )));
            }
            if frequency_hz <= 0.0 || frequency_hz > sample_rate as f64 / 2.0 {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "AudioSineWave: frequency_hz {} outside (0, Nyquist={}]",
                    frequency_hz,
                    sample_rate as f64 / 2.0
                )));
            }
            let pcm = sine_pcm16(frequency_hz, duration_ms, sample_rate, 0.5);
            CoprocessorOutcome::Hex(hex(&wav_pack(&pcm, sample_rate)))
        }
        CoprocessorOp::AudioCompletionChime { sample_rate } => {
            if !(8_000..=192_000).contains(&sample_rate) {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "AudioCompletionChime: sample_rate {} outside [8000, 192000]",
                    sample_rate
                )));
            }
            // Three ascending notes: C5 (523.25), E5 (659.26), G5 (783.99),
            // 100 ms each, 0.4 amplitude.
            let mut buf: Vec<i16> = Vec::new();
            for f in [523.25, 659.26, 783.99] {
                buf.extend(sine_pcm16(f, 100, sample_rate, 0.4));
            }
            CoprocessorOutcome::Hex(hex(&wav_pack(&buf, sample_rate)))
        }
        other => CoprocessorOutcome::Failure(format!(
            "Audio backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

fn sine_pcm16(freq: f64, duration_ms: u32, sample_rate: u32, amplitude: f64) -> Vec<i16> {
    let n = (duration_ms as u64 * sample_rate as u64 / 1000) as usize;
    let two_pi = 2.0 * std::f64::consts::PI;
    let scale = (i16::MAX as f64 - 1.0) * amplitude.clamp(0.0, 1.0);
    (0..n)
        .map(|i| {
            let t = i as f64 / sample_rate as f64;
            (scale * (two_pi * freq * t).sin()) as i16
        })
        .collect()
}

/// Pack 16-bit PCM samples into a minimal WAV (RIFF) container.
/// Format: PCM, mono, 16-bit, little-endian.
fn wav_pack(pcm: &[i16], sample_rate: u32) -> Vec<u8> {
    let data_len = (pcm.len() * 2) as u32;
    let chunk_size = 36 + data_len;
    let byte_rate = sample_rate * 2; // mono × 16-bit
    let mut out = Vec::with_capacity(44 + data_len as usize);
    // RIFF header
    out.extend_from_slice(b"RIFF");
    out.extend_from_slice(&chunk_size.to_le_bytes());
    out.extend_from_slice(b"WAVE");
    // fmt subchunk
    out.extend_from_slice(b"fmt ");
    out.extend_from_slice(&16u32.to_le_bytes()); // subchunk size
    out.extend_from_slice(&1u16.to_le_bytes()); // PCM format code
    out.extend_from_slice(&1u16.to_le_bytes()); // mono
    out.extend_from_slice(&sample_rate.to_le_bytes());
    out.extend_from_slice(&byte_rate.to_le_bytes());
    out.extend_from_slice(&2u16.to_le_bytes()); // block align (mono × 2)
    out.extend_from_slice(&16u16.to_le_bytes()); // bits per sample
    // data subchunk
    out.extend_from_slice(b"data");
    out.extend_from_slice(&data_len.to_le_bytes());
    for s in pcm {
        out.extend_from_slice(&s.to_le_bytes());
    }
    out
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        write!(s, "{:02x}", b).unwrap();
    }
    s
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
            AudioBackend::new().dispatch(op).await.unwrap()
        })
    }

    fn decode_hex(h: &str) -> Vec<u8> {
        (0..h.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn sine_wave_has_riff_header_and_correct_length() {
        match run(CoprocessorOp::AudioSineWave {
            frequency_hz: 440.0,
            duration_ms: 100,
            sample_rate: 44_100,
        }) {
            CoprocessorOutcome::Hex(h) => {
                let bytes = decode_hex(&h);
                assert_eq!(&bytes[0..4], b"RIFF");
                assert_eq!(&bytes[8..12], b"WAVE");
                assert_eq!(&bytes[12..16], b"fmt ");
                assert_eq!(&bytes[36..40], b"data");
                // 100ms × 44.1kHz × 2 bytes = 8820 sample bytes.
                let expected_data = 100u32 * 44_100 / 1000 * 2;
                assert_eq!(
                    u32::from_le_bytes(bytes[40..44].try_into().unwrap()),
                    expected_data
                );
            }
            _ => panic!(),
        }
    }

    #[test]
    fn frequency_above_nyquist_returns_failure() {
        match run(CoprocessorOp::AudioSineWave {
            frequency_hz: 30_000.0,
            duration_ms: 50,
            sample_rate: 44_100,
        }) {
            CoprocessorOutcome::Failure(_) => {}
            _ => panic!("expected Failure for f > Nyquist"),
        }
    }

    #[test]
    fn invalid_sample_rate_returns_failure() {
        match run(CoprocessorOp::AudioSineWave {
            frequency_hz: 1000.0,
            duration_ms: 50,
            sample_rate: 1_000,
        }) {
            CoprocessorOutcome::Failure(_) => {}
            _ => panic!(),
        }
    }

    #[test]
    fn completion_chime_wav_size_matches_three_100ms_notes() {
        match run(CoprocessorOp::AudioCompletionChime { sample_rate: 44_100 }) {
            CoprocessorOutcome::Hex(h) => {
                let bytes = decode_hex(&h);
                assert_eq!(&bytes[0..4], b"RIFF");
                // 3 × 100ms × 44.1kHz × 2 bytes = 26460 sample bytes
                let expected_data = 3u32 * 100 * 44_100 / 1000 * 2;
                assert_eq!(
                    u32::from_le_bytes(bytes[40..44].try_into().unwrap()),
                    expected_data
                );
            }
            _ => panic!(),
        }
    }
}
