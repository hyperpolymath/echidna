// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA REST API Server

use axum::{
    extract::{Json, Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{delete, get, post},
    Router,
};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use echidna::core::{ProofState, Tactic, TacticResult};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock};
use tower_http::cors::CorsLayer;
use utoipa::{OpenApi, ToSchema};
use utoipa_swagger_ui::SwaggerUi;

mod handlers;
mod models;

use models::*;

/// Application state shared across handlers
#[derive(Clone)]
pub struct AppState {
    /// Active proof sessions (proof_id -> ProofSession)
    pub sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    /// HTTP client for Julia ML API
    pub ml_client: reqwest::Client,
    /// Julia ML API base URL
    pub ml_api_url: String,
}

/// A proof session
pub struct ProofSession {
    pub id: String,
    pub prover_kind: echidna::ProverKind,
    pub prover: Box<dyn ProverBackend>,
    pub state: Option<ProofState>,
    pub goal: String,
    pub status: ProofStatus,
    pub history: Vec<String>,
    pub start_time: std::time::Instant,
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    let ml_client = reqwest::Client::builder()
        .timeout(Duration::from_secs(10))
        .build()
        .expect("Failed to create HTTP client");

    let ml_api_url = "http://127.0.0.1:8090".to_string();

    // Test Julia ML connection
    match ml_client.get(format!("{}/health", ml_api_url)).send().await {
        Ok(resp) if resp.status().is_success() => {
            tracing::info!("Connected to Julia ML API at {}", ml_api_url);
        }
        _ => {
            tracing::info!("Julia ML API not available at {} (will use fallback)", ml_api_url);
        }
    }

    let state = AppState {
        sessions: Arc::new(RwLock::new(HashMap::new())),
        ml_client,
        ml_api_url,
    };

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
