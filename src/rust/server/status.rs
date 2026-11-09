// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Discovery and status routes: Groove manifest, health, diagnostics, prover list.

use super::{AppError, AppState};
use axum::{extract::State, Json};
use echidna::diagnostics::HealthStatus;
use echidna::ProverKind;
use serde::Serialize;
use serde_json::json;

// ========== Groove Discovery ==========

/// Groove capability manifest for ECHIDNA.
///
/// Returns the service's capabilities in the standard Groove format so that
/// Gossamer, PanLL, and other groove-aware systems can discover ECHIDNA by
/// probing GET /.well-known/groove. See Groove.idr echidnaManifest for the
/// canonical ABI definition.
///
/// Capabilities offered:
///   - theorem-proving: Multi-backend theorem proving (48 provers)
///
/// Capabilities consumed:
///   - octad-storage (VeriSimDB): Persist proof artifacts as octad entities
///   - scanning (Hypatia): Trigger re-verification after codebase changes
pub(super) async fn groove_manifest() -> Json<serde_json::Value> {
    let core_count = echidna::ProverKind::all_core().len();
    let advertised_count = echidna::ProverKind::all().len();
    Json(json!({
        "groove_version": "1",
        "service_id": "echidna",
        "service_version": env!("CARGO_PKG_VERSION"),
        "capabilities": {
            "theorem_proving": {
                "type": "theorem-proving",
                "description": format!(
                    "Neurosymbolic theorem proving — {} core / {} advertised prover backends",
                    core_count, advertised_count
                ),
                "protocol": "http",
                "endpoint": "/api/prove",
                "requires_auth": false,
                "panel_compatible": true
            }
        },
        "consumes": ["octad-storage", "scanning"],
        "endpoints": {
            "provers": "/api/provers",
            "prove":   "/api/prove",
            "verify":  "/api/verify",
            "health":  "/api/health"
        },
        "health": "/api/health",
        "applicability": ["individual", "team"]
    }))
}

// ========== REST API Handlers ==========

/// Health check endpoint
pub(super) async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// Detailed diagnostics health endpoint
/// Returns full HealthStatus snapshot from dispatcher with prover metrics and degradation mode
pub(super) async fn diagnostics_health_handler(
    State(app_state): State<AppState>,
) -> Result<Json<HealthStatus>, AppError> {
    let health = app_state
        .dispatcher
        .health_status()
        .map_err(|error| AppError::InternalError(error.to_string()))?;
    Ok(Json(health))
}

/// List available provers
pub(super) async fn list_provers() -> Json<ProversResponse> {
    let provers = ProverKind::all_core()
        .into_iter()
        .map(|prover| ProverInfo {
            name: format!("{:?}", prover),
            tier: prover.tier(),
            complexity: prover.complexity(),
        })
        .collect();

    Json(ProversResponse { provers })
}

// ========== Request/Response Types ==========

#[derive(Serialize)]
pub(super) struct HealthResponse {
    status: String,
    version: String,
}

#[derive(Serialize)]
pub(super) struct ProversResponse {
    provers: Vec<ProverInfo>,
}

#[derive(Serialize)]
struct ProverInfo {
    name: String,
    tier: u8,
    complexity: u8,
}
