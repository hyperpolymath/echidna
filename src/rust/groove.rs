// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Gossamer Groove endpoint for ECHIDNA.
//!
//! Exposes ECHIDNA's formal proof verification capabilities via the Groove
//! discovery protocol. Any groove-aware system (Gossamer, PanLL, Hypatia,
//! etc.) can discover ECHIDNA by probing `GET /.well-known/groove` on port
//! 9000.
//!
//! ECHIDNA is a neurosymbolic theorem proving platform supporting 48 prover
//! backends with a comprehensive verification pipeline, LLM integration,
//! dodeca-API, and Prover Wars.
//!
//! The groove connector types are formally verified in Gossamer's Groove.idr:
//! - `IsSubset` proves consumers can only connect if ECHIDNA satisfies their
//!   needs
//! - `GrooveHandle` is linear: consumers MUST disconnect (no dangling grooves)
//!
//! ## Groove Protocol
//!
//! - `GET  /.well-known/groove` — Capability manifest (JSON)
//! - `GET  /health`             — Simple health check
//!
//! ## Capabilities Offered
//!
//! - `proof-verification` — Formal proof verification engine with LLM
//!   integration, dodeca-API, and Prover Wars
//!
//! ## Capabilities Consumed (enhanced when available)
//!
//! - `octad-storage` (from VeriSimDB) — Persist proof artifacts as octad
//!   entities

use axum::{routing::get, Json, Router};
use serde_json::json;

/// Default port for the ECHIDNA groove endpoint.
pub const GROOVE_PORT: u16 = 9000;

/// Build the groove manifest JSON for ECHIDNA.
///
/// Returns a `serde_json::Value` containing the standard Groove capability
/// manifest. The manifest advertises ECHIDNA's `proof-verification`
/// capability and declares that it can consume `octad-storage` from
/// VeriSimDB when available.
fn manifest() -> serde_json::Value {
    json!({
        "groove_version": "1",
        "service_id": "echidna",
        "service_version": env!("CARGO_PKG_VERSION"),
        "capabilities": {
            "proof_verification": {
                "type": "proof-verification",
                "description": "Formal proof verification engine with LLM integration, dodeca-API, and Prover Wars",
                "protocol": "http",
                "endpoint": "/api/v1/prove",
                "requires_auth": false,
                "panel_compatible": true
            }
        },
        "consumes": ["octad-storage"],
        "endpoints": {
            "api": format!("http://localhost:{}/api", GROOVE_PORT),
            "health": format!("http://localhost:{}/health", GROOVE_PORT)
        },
        "health": "/health",
        "applicability": ["individual", "team"]
    })
}

/// Axum handler for `GET /.well-known/groove`.
///
/// Returns the Groove capability manifest as JSON so that groove-aware
/// systems (Gossamer, PanLL, Hypatia, etc.) can discover ECHIDNA via
/// standard port probing.
async fn groove_manifest() -> Json<serde_json::Value> {
    Json(manifest())
}

/// Axum handler for `GET /health`.
///
/// Returns a minimal JSON health check response. Groove consumers use
/// this to verify the service is responsive before attempting capability
/// negotiation.
async fn health_check() -> Json<serde_json::Value> {
    Json(json!({
        "status": "ok",
        "service": "echidna",
        "version": env!("CARGO_PKG_VERSION")
    }))
}

/// Build an axum `Router` containing the groove discovery endpoints.
///
/// The router exposes two routes:
/// - `GET /.well-known/groove` — Capability manifest
/// - `GET /health` — Health check
///
/// Callers can merge this router into a larger application or serve it
/// standalone via [`run`].
pub fn router() -> Router {
    Router::new()
        .route("/.well-known/groove", get(groove_manifest))
        .route("/health", get(health_check))
}

/// Run the standalone groove discovery server on `GROOVE_PORT`.
///
/// Binds to `127.0.0.1:9000` and serves the groove manifest and health
/// check endpoints. This function blocks until the server is shut down.
///
/// # Errors
///
/// Returns an error if the TCP listener cannot bind to the port (e.g.
/// the port is already in use).
pub async fn run() -> anyhow::Result<()> {
    run_on_port(GROOVE_PORT).await
}

/// Run the groove discovery server on a caller-specified port.
///
/// This variant is useful for tests or when the default port is
/// unavailable.
///
/// # Errors
///
/// Returns an error if the TCP listener cannot bind to the given port.
pub async fn run_on_port(port: u16) -> anyhow::Result<()> {
    let addr = format!("127.0.0.1:{}", port);
    tracing::info!("[groove] echidna groove endpoint listening on {}", addr);
    tracing::info!(
        "[groove] Probe: curl http://localhost:{}/.well-known/groove",
        port
    );

    let listener = tokio::net::TcpListener::bind(&addr).await?;
    axum::serve(listener, router()).await?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The manifest must contain the required top-level fields.
    #[test]
    fn manifest_has_required_fields() {
        let m = manifest();
        assert_eq!(m["groove_version"], "1");
        assert_eq!(m["service_id"], "echidna");
        assert!(m["service_version"].is_string());
        assert!(m["capabilities"]["proof_verification"].is_object());
        assert_eq!(
            m["capabilities"]["proof_verification"]["type"],
            "proof-verification"
        );
        assert!(m["consumes"].is_array());
        assert_eq!(m["consumes"][0], "octad-storage");
        assert_eq!(m["health"], "/health");
    }

    /// The GROOVE_PORT constant must match the assigned echidna port.
    #[test]
    fn groove_port_is_9000() {
        assert_eq!(GROOVE_PORT, 9000);
    }
}
