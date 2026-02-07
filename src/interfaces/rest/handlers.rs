// SPDX-License-Identifier: PMPL-1.0-or-later
// REST API request handlers

use axum::{
    extract::{Json, Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use std::sync::Arc;

use crate::{models::*, AppState};

/// List all available provers
#[utoipa::path(
    get,
    path = "/api/v1/provers",
    responses(
        (status = 200, description = "List of available provers", body = [ProverInfo])
    ),
    tag = "provers"
)]
pub async fn list_provers(State(_state): State<Arc<AppState>>) -> impl IntoResponse {
    // TODO: Query ECHIDNA core
    let provers = vec![
        ProverInfo {
            kind: ProverKind::Vampire,
            version: "4.8".to_string(),
            tier: 5,
            complexity: 2,
            available: true,
        },
        ProverInfo {
            kind: ProverKind::EProver,
            version: "3.1".to_string(),
            tier: 5,
            complexity: 2,
            available: true,
        },
    ];
    Json(provers)
}

/// Get information about a specific prover
#[utoipa::path(
    get,
    path = "/api/v1/provers/{kind}",
    responses(
        (status = 200, description = "Prover information", body = ProverInfo),
        (status = 404, description = "Prover not found")
    ),
    params(
        ("kind" = ProverKind, Path, description = "Prover kind")
    ),
    tag = "provers"
)]
pub async fn get_prover(
    State(_state): State<Arc<AppState>>,
    Path(_kind): Path<String>,
) -> impl IntoResponse {
    // TODO: Query ECHIDNA core
    StatusCode::NOT_IMPLEMENTED
}

/// Submit a new proof goal
#[utoipa::path(
    post,
    path = "/api/v1/proofs",
    request_body = ProofRequest,
    responses(
        (status = 201, description = "Proof submitted", body = ProofResponse),
        (status = 400, description = "Invalid request")
    ),
    tag = "proofs"
)]
pub async fn submit_proof(
    State(_state): State<Arc<AppState>>,
    Json(req): Json<ProofRequest>,
) -> impl IntoResponse {
    // TODO: Submit to ECHIDNA core
    let response = ProofResponse {
        id: uuid::Uuid::new_v4().to_string(),
        prover: req.prover,
        goal: req.goal,
        status: ProofStatus::Pending,
        proof_script: vec![],
        time_elapsed: None,
        error_message: None,
    };
    (StatusCode::CREATED, Json(response))
}

/// List proof attempts
#[utoipa::path(
    get,
    path = "/api/v1/proofs",
    responses(
        (status = 200, description = "List of proofs", body = [ProofResponse])
    ),
    params(
        ("status" = Option<ProofStatus>, Query, description = "Filter by status"),
        ("limit" = Option<usize>, Query, description = "Limit results")
    ),
    tag = "proofs"
)]
pub async fn list_proofs(
    State(_state): State<Arc<AppState>>,
    Query(_query): Query<ListProofsQuery>,
) -> impl IntoResponse {
    // TODO: Query ECHIDNA core
    Json(vec![] as Vec<ProofResponse>)
}

/// Get proof status
#[utoipa::path(
    get,
    path = "/api/v1/proofs/{id}",
    responses(
        (status = 200, description = "Proof status", body = ProofResponse),
        (status = 404, description = "Proof not found")
    ),
    params(
        ("id" = String, Path, description = "Proof ID")
    ),
    tag = "proofs"
)]
pub async fn get_proof(
    State(_state): State<Arc<AppState>>,
    Path(_id): Path<String>,
) -> impl IntoResponse {
    // TODO: Query ECHIDNA core
    StatusCode::NOT_FOUND
}

/// Cancel a proof attempt
#[utoipa::path(
    delete,
    path = "/api/v1/proofs/{id}",
    responses(
        (status = 204, description = "Proof cancelled"),
        (status = 404, description = "Proof not found")
    ),
    params(
        ("id" = String, Path, description = "Proof ID")
    ),
    tag = "proofs"
)]
pub async fn cancel_proof(
    State(_state): State<Arc<AppState>>,
    Path(_id): Path<String>,
) -> impl IntoResponse {
    // TODO: Cancel in ECHIDNA core
    StatusCode::NO_CONTENT
}

/// Apply a tactic to a proof
#[utoipa::path(
    post,
    path = "/api/v1/proofs/{id}/tactics",
    request_body = TacticRequest,
    responses(
        (status = 200, description = "Tactic applied", body = TacticResponse),
        (status = 404, description = "Proof not found")
    ),
    params(
        ("id" = String, Path, description = "Proof ID")
    ),
    tag = "tactics"
)]
pub async fn apply_tactic(
    State(_state): State<Arc<AppState>>,
    Path(_id): Path<String>,
    Json(_req): Json<TacticRequest>,
) -> impl IntoResponse {
    // TODO: Apply to ECHIDNA core
    StatusCode::NOT_IMPLEMENTED
}

/// Get suggested tactics for a proof
#[utoipa::path(
    get,
    path = "/api/v1/proofs/{id}/tactics/suggest",
    responses(
        (status = 200, description = "Suggested tactics", body = [Tactic]),
        (status = 404, description = "Proof not found")
    ),
    params(
        ("id" = String, Path, description = "Proof ID"),
        ("limit" = Option<usize>, Query, description = "Limit results")
    ),
    tag = "tactics"
)]
pub async fn suggest_tactics(
    State(_state): State<Arc<AppState>>,
    Path(_id): Path<String>,
    Query(_query): Query<ListProofsQuery>,
) -> impl IntoResponse {
    // TODO: Call ECHIDNA neural premise selection
    Json(vec![] as Vec<Tactic>)
}
