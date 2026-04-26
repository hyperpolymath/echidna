// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Rust ↔ Julia coprocessor bridge.
//!
//! Routes ops the in-process backends cannot serve to Julia-side coprocessor
//! implementations — `LowLevel.jl` (CPU/GPU/NPU/TPU/QPU/PPU/DSP/FPGA/IOPU
//! dispatch), `ProvenCrypto.jl`, `KnotTheory.jl`, etc.
//!
//! Transport is HTTP+JSON to `http://127.0.0.1:8090/coprocessor/dispatch`,
//! consistent with the GNN endpoint convention.  The Cap'n Proto IPC path
//! described in `src/julia/ipc.jl` is the future home; gating is the same
//! L3 Tier-1 green for ≥ 7 days.
//!
//! This module only carries the *transport*; the Julia endpoint is in
//! `src/julia/coprocessor.jl`.  Bridge probe is non-throwing — callers
//! check `health()` before routing.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;
use super::trust::CoprocessorTrustTier;

/// Default Julia coprocessor endpoint.  Overridable via `ECHIDNA_JULIA_COPROC_URL`.
const DEFAULT_URL: &str = "http://127.0.0.1:8090/coprocessor/dispatch";

/// Default request timeout (matches GNN endpoint convention).
const DEFAULT_TIMEOUT_SECS: u64 = 30;

/// HTTP client to the Julia coprocessor router.
///
/// Holds a `reqwest::Client` with sensible timeouts.  The bridge does NOT
/// claim a `CoprocessorKind` of its own — it is a *transport* that wraps
/// a Julia-side backend whose kind is reported by the endpoint at construction.
pub struct JuliaCoprocessorBridge {
    /// The kind of the Julia-side coprocessor this bridge fronts.
    /// Echoed by the Julia endpoint at registration so capabilities query
    /// once at startup; refreshed if the endpoint reports a change.
    kind: CoprocessorKind,

    /// Capabilities reported by the Julia side at startup.
    capabilities: CoprocessorCapabilities,

    /// Current liveness — updated by `probe()`.
    health: CoprocessorHealth,

    /// Endpoint URL.
    url: String,

    /// HTTP client.
    client: reqwest::Client,
}

impl JuliaCoprocessorBridge {
    /// Construct a bridge with reported `kind` and assumed capabilities.
    /// Call `probe()` afterwards to refresh `health` and `capabilities`
    /// from the live endpoint.
    pub fn new(kind: CoprocessorKind, capabilities: CoprocessorCapabilities) -> Self {
        let url = std::env::var("ECHIDNA_JULIA_COPROC_URL")
            .unwrap_or_else(|_| DEFAULT_URL.to_string());
        let client = reqwest::Client::builder()
            .timeout(Duration::from_secs(DEFAULT_TIMEOUT_SECS))
            .build()
            .expect("reqwest client builds with static config");
        JuliaCoprocessorBridge {
            kind,
            capabilities,
            health: CoprocessorHealth::Unhealthy, // until probed
            url,
            client,
        }
    }

    /// Non-throwing reachability probe — updates `self.health`.
    /// Returns the new health value.
    pub async fn probe(&mut self) -> CoprocessorHealth {
        let probe_url = self
            .url
            .trim_end_matches("/dispatch")
            .to_string()
            + "/health";
        match self
            .client
            .get(&probe_url)
            .timeout(Duration::from_millis(200))
            .send()
            .await
        {
            Ok(r) if r.status().is_success() => {
                self.health = CoprocessorHealth::Healthy;
            },
            Ok(_) => self.health = CoprocessorHealth::Degraded,
            Err(_) => self.health = CoprocessorHealth::Unhealthy,
        }
        self.health
    }
}

/// Wire envelope for `/coprocessor/dispatch`.
#[derive(Debug, Serialize)]
struct DispatchRequest<'a> {
    /// Backend kind, e.g. "Math".  The Julia router uses this to select
    /// a specific Julia backend (LowLevel.jl, ProvenCrypto.jl, …).
    kind: &'a str,
    /// The op variant name + payload, serialised as the existing
    /// `CoprocessorOp` enum tag (Serde external tagging).
    op: &'a CoprocessorOp,
}

/// Wire response for `/coprocessor/dispatch`.
///
/// The Julia endpoint either returns a `CoprocessorOutcome`-shaped JSON
/// object on success, or an error string in `error` for transport / Julia
/// runtime failures.  Failure-from-the-op (well-formed input, op refused)
/// comes back as `CoprocessorOutcome::Failure`, not as `error`.
#[derive(Debug, Deserialize)]
struct DispatchResponse {
    outcome: Option<CoprocessorOutcome>,
    error: Option<String>,
}

#[async_trait]
impl Coprocessor for JuliaCoprocessorBridge {
    fn kind(&self) -> CoprocessorKind {
        self.kind
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        self.health
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        CoprocessorTrustTier::JuliaBridged
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        let body = DispatchRequest {
            kind: kind_name(self.kind),
            op: &op,
        };
        let resp = self
            .client
            .post(&self.url)
            .json(&body)
            .send()
            .await
            .map_err(|e| anyhow!("julia bridge transport error: {e}"))?;

        if !resp.status().is_success() {
            let status = resp.status();
            let text = resp.text().await.unwrap_or_default();
            return Err(anyhow!(
                "julia bridge HTTP {status}: {text}"
            ));
        }

        let parsed: DispatchResponse = resp
            .json()
            .await
            .map_err(|e| anyhow!("julia bridge response parse error: {e}"))?;

        if let Some(err) = parsed.error {
            return Ok(CoprocessorOutcome::Failure(err));
        }
        parsed
            .outcome
            .ok_or_else(|| anyhow!("julia bridge response missing both outcome and error"))
    }
}

fn kind_name(k: CoprocessorKind) -> &'static str {
    match k {
        CoprocessorKind::Math => "Math",
        CoprocessorKind::Vector => "Vector",
        CoprocessorKind::Tensor => "Tensor",
        CoprocessorKind::Crypto => "Crypto",
        CoprocessorKind::Physics => "Physics",
        // FlintMath is an in-process Rust backend; it would not normally be
        // fronted by the Julia bridge.  The name is present for completeness
        // so that this match remains exhaustive as the enum grows.
        CoprocessorKind::FlintMath => "FlintMath",
    }
}
