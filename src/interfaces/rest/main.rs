// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA REST API Server

use axum::{
    extract::{Json, Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{delete, get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tower_http::cors::CorsLayer;
use utoipa::{OpenApi, ToSchema};
use utoipa_swagger_ui::SwaggerUi;

mod handlers;
mod models;

use models::*;

#[derive(Clone)]
struct AppState {
    // TODO: Connection to ECHIDNA core
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    let state = Arc::new(AppState {});

    let app = Router::new()
        // Health check
        .route("/health", get(health_check))

        // Prover endpoints
        .route("/api/v1/provers", get(handlers::list_provers))
        .route("/api/v1/provers/:kind", get(handlers::get_prover))

        // Proof endpoints
        .route("/api/v1/proofs", post(handlers::submit_proof))
        .route("/api/v1/proofs", get(handlers::list_proofs))
        .route("/api/v1/proofs/:id", get(handlers::get_proof))
        .route("/api/v1/proofs/:id", delete(handlers::cancel_proof))

        // Tactic endpoints
        .route("/api/v1/proofs/:id/tactics", post(handlers::apply_tactic))
        .route("/api/v1/proofs/:id/tactics/suggest", get(handlers::suggest_tactics))

        // OpenAPI documentation
        .merge(SwaggerUi::new("/swagger-ui").url("/api-docs/openapi.json", ApiDoc::openapi()))

        .layer(CorsLayer::permissive())
        .with_state(state);

    let addr = "127.0.0.1:8000";
    tracing::info!("REST API listening on http://{}", addr);
    tracing::info!("Swagger UI available at http://{}/swagger-ui", addr);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn health_check() -> &'static str {
    "OK"
}

#[derive(OpenApi)]
#[openapi(
    paths(
        handlers::list_provers,
        handlers::get_prover,
        handlers::submit_proof,
        handlers::list_proofs,
        handlers::get_proof,
        handlers::cancel_proof,
        handlers::apply_tactic,
        handlers::suggest_tactics,
    ),
    components(
        schemas(ProverKind, ProverInfo, ProofStatus, ProofRequest, ProofResponse, TacticRequest, TacticResponse)
    ),
    tags(
        (name = "provers", description = "Theorem prover management"),
        (name = "proofs", description = "Proof submission and management"),
        (name = "tactics", description = "Tactic application and suggestions")
    )
)]
struct ApiDoc;
