// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! HTTP API server for ECHIDNA
//!
//! Provides REST API and WebSocket endpoints for theorem proving

use anyhow::Result;
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use colored::Colorize;
use echidna::agent::meta_controller::MetaController;
use echidna::core::{ProofState, Tactic};
use echidna::dispatch::ProverDispatcher;
use echidna::verification::StatisticsTracker;
use echidna::{ProverBackend, ProverKind};
use reqwest::Client;
use serde_json::json;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock};
use tower_http::cors::CorsLayer;
use tracing::{debug, info};

mod agent;
mod prove;
mod search;
mod session;
mod status;
mod ui;
mod verify;

use agent::agent_plan_handler;
use prove::prove_handler;
use search::{search_handler, suggest_handler};
use session::{apply_tactic_handler, create_session, get_proof_tree, get_session_state};
use status::{diagnostics_health_handler, groove_manifest, health_check, list_provers};
use ui::{get_aspect_tags, search_theorems_ui, suggest_tactics_ui};
use verify::{verify_handler, verify_parallel_handler, verify_raw_handler};

/// Application state shared across handlers
#[derive(Clone)]
struct AppState {
    /// Active proof sessions (session_id -> ProofSession)
    sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    /// HTTP client for Julia ML API
    ml_client: Client,
    /// Julia ML API base URL
    ml_api_url: String,
    /// MetaController — shared (prover × coprocessor) planner with persistent
    /// StatisticsTracker.  Survives request boundaries so the Bayesian routing
    /// state accumulates across the server's lifetime.  All handlers that
    /// perform goal-aware dispatch share this single instance.
    meta_controller: Arc<MetaController>,
    /// Shared proof-outcome statistics used by MetaController for Bayesian
    /// routing and exported to Julia for GNN online learning.
    stats: Arc<RwLock<StatisticsTracker>>,
    /// Prover dispatcher for trust-hardening pipeline and health monitoring
    dispatcher: Arc<ProverDispatcher>,
}

/// A proof session
struct ProofSession {
    prover: Box<dyn ProverBackend>,
    state: Option<ProofState>,
    history: Vec<String>,
}

const DEFAULT_ML_API_URL: &str = "http://127.0.0.1:8090";

/// Start the HTTP server
pub async fn start_server(port: u16, host: String, enable_cors: bool) -> Result<()> {
    // Create HTTP client for Julia ML API
    let ml_client = Client::builder().timeout(Duration::from_secs(10)).build()?;

    let ml_api_url =
        std::env::var("ECHIDNA_ML_API_URL").unwrap_or_else(|_| DEFAULT_ML_API_URL.to_string());

    // Security: Validate that the ML API URL is either local or explicitly allowed
    if !ml_api_url.starts_with("http://127.0.0.1") && !ml_api_url.starts_with("http://localhost") {
        info!("⚠ Untrusted ML API URL detected: {}. Baseline security policy requires local or trusted endpoint.", ml_api_url);
    }

    // Test Julia ML connection
    match ml_client.get(format!("{}/health", ml_api_url)).send().await {
        Ok(resp) if resp.status().is_success() => {
            info!("✓ Connected to Julia ML API at {}", ml_api_url);
        },
        _ => {
            info!(
                "⚠ Julia ML API not available at {} (will use fallback)",
                ml_api_url
            );
        },
    }

    // Shared stats tracker — MetaController uses it for Bayesian routing;
    // the background GNN sync task pushes snapshots to Julia for online learning.
    let stats = Arc::new(RwLock::new(StatisticsTracker::new()));
    let meta_controller = Arc::new(MetaController::new().with_stats(stats.clone()));

    // Create prover dispatcher with default configuration.
    // When compiled with --features verisim, attach the VeriSimDB writer so
    // every HTTP proof attempt (including parse failures) feeds the S4 learning
    // loop.  The writer runs fire-and-forget; a VeriSimDB outage never blocks
    // or alters a dispatch result.
    let dispatcher = {
        let d = ProverDispatcher::new();
        #[cfg(feature = "verisim")]
        let d = {
            let url = std::env::var("VERISIM_URL")
                .unwrap_or_else(|_| "http://localhost:8080".to_string());
            info!("✓ VeriSim writer attached at {}", url);
            d.with_verisim_writer(&url)
        };
        Arc::new(d)
    };
    info!("✓ Initialized prover dispatcher for trust-hardening pipeline");

    let state = AppState {
        sessions: Arc::new(RwLock::new(HashMap::new())),
        ml_client,
        ml_api_url,
        meta_controller,
        stats,
        dispatcher,
    };

    // GNN training sync — background task that pushes accumulated proof-outcome
    // stats to Julia's /training/update endpoint every 60 seconds.
    // Only fires when >= 10 new outcomes have accumulated since the last push,
    // so idle servers incur no traffic.  Errors are logged at debug level and
    // do not affect the main server loop (fire-and-forget).
    {
        let sync_stats = state.stats.clone();
        let sync_client = state.ml_client.clone();
        let sync_url = state.ml_api_url.clone();
        tokio::spawn(async move {
            let mut last_push_count: u64 = 0;
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            interval.tick().await; // consume the immediate first tick; wait 60s before first push
            loop {
                interval.tick().await;
                let (total, records) = {
                    let guard = sync_stats.read().await;
                    (guard.total_attempts(), guard.export_records())
                };
                if total < last_push_count + 10 || records.is_empty() {
                    continue;
                }
                last_push_count = total;
                let url = format!("{}/training/update", sync_url);
                let payload = json!({ "records": records });
                match sync_client.post(&url).json(&payload).send().await {
                    Ok(resp) if resp.status().is_success() => {
                        info!(
                            "GNN training sync: {} records pushed to Julia",
                            records.len()
                        );
                    },
                    Ok(resp) => {
                        debug!("GNN training sync: Julia returned {}", resp.status());
                    },
                    Err(e) => {
                        debug!("GNN training sync: Julia unavailable ({})", e);
                    },
                }
            }
        });
    }

    // Build router
    let mut app = Router::new()
        // Groove discovery endpoint — returns capability manifest for service mesh.
        // See Groove.idr echidnaManifest for the canonical ABI definition.
        .route("/.well-known/groove", get(groove_manifest))
        // REST API endpoints
        .route("/api/health", get(health_check))
        .route("/api/diagnostics/health", get(diagnostics_health_handler))
        .route("/api/provers", get(list_provers))
        .route("/api/prove", post(prove_handler))
        .route("/api/verify", post(verify_handler))
        .route("/api/verify_parallel", post(verify_parallel_handler))
        .route("/api/verify_raw", post(verify_raw_handler))
        .route("/api/suggest", post(suggest_handler))
        .route("/api/search", get(search_handler))
        .route("/api/session/create", post(create_session))
        .route("/api/session/{id}/state", get(get_session_state))
        .route("/api/session/{id}/apply", post(apply_tactic_handler))
        .route("/api/session/{id}/tree", get(get_proof_tree))
        // Additional UI-specific endpoints
        .route("/api/agent/plan", post(agent_plan_handler))
        .route("/api/aspect-tags", get(get_aspect_tags))
        .route("/api/tactics/suggest", post(suggest_tactics_ui))
        .route("/api/theorems/search", get(search_theorems_ui))
        // WebSocket endpoint (disabled - requires axum ws feature)
        // .route("/ws/interactive", get(websocket_handler))
        .with_state(state);

    // Add CORS if enabled
    if enable_cors {
        app = app.layer(CorsLayer::permissive());
    }

    // Bind server
    let addr: SocketAddr = format!("{}:{}", host, port).parse()?;

    println!(
        "{}",
        "╔═══════════════════════════════════════════════════════════╗".cyan()
    );
    println!(
        "{}",
        "║  ECHIDNA HTTP API Server                                  ║"
            .cyan()
            .bold()
    );
    println!(
        "{}",
        "╚═══════════════════════════════════════════════════════════╝".cyan()
    );
    println!();
    println!(
        "Server listening on: {}",
        format!("https://{}", addr).green().bold()
    );
    println!();
    println!("{}", "Endpoints:".yellow().bold());
    println!("  GET  /.well-known/groove       - Groove discovery manifest");
    println!("  GET  /api/health              - Health check");
    println!("  GET  /api/provers             - List available provers");
    println!("  POST /api/prove               - Prove a theorem");
    println!("  POST /api/verify              - Verify a proof");
    println!("  POST /api/suggest             - Get tactic suggestions");
    println!("  GET  /api/search?q=<pattern>  - Search theorems");
    println!("  POST /api/session/create      - Create proof session");
    println!("  GET  /api/session/{{id}}/state   - Get session state");
    println!("  POST /api/session/{{id}}/apply   - Apply tactic to session");
    println!("  WS   /ws/interactive          - WebSocket live proof session");
    println!();
    println!("Press Ctrl+C to stop the server");
    println!();

    // Start server
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

// ========== Helper Functions ==========

/// Return true if the parsed ProofState contains no meaningful structure.
/// Used to detect the parse+export round-trip bug: a prover backend's
/// `parse_string` returns an empty state on unrecognised input, then
/// `verify_proof` regenerates an empty file which the real backend binary
/// then accepts vacuously (false positive).
fn is_empty_state(state: &echidna::core::ProofState) -> bool {
    state.goals.is_empty()
        && state.context.theorems.is_empty()
        && state.context.axioms.is_empty()
        && state.context.definitions.is_empty()
        && state.context.variables.is_empty()
}

/// Parse prover kind from string
fn parse_prover_kind(s: &str) -> Result<ProverKind, AppError> {
    match s.to_lowercase().as_str() {
        "agda" => Ok(ProverKind::Agda),
        "coq" => Ok(ProverKind::Coq),
        "lean" => Ok(ProverKind::Lean),
        "isabelle" => Ok(ProverKind::Isabelle),
        "z3" => Ok(ProverKind::Z3),
        "cvc5" => Ok(ProverKind::CVC5),
        "metamath" => Ok(ProverKind::Metamath),
        "hollight" => Ok(ProverKind::HOLLight),
        "mizar" => Ok(ProverKind::Mizar),
        "pvs" => Ok(ProverKind::PVS),
        "acl2" => Ok(ProverKind::ACL2),
        "hol4" => Ok(ProverKind::HOL4),
        _ => Err(AppError::BadRequest(format!("Unknown prover: {}", s))),
    }
}

/// Parse tactic from JSON string (simplified)
fn parse_tactic_from_json(s: &str) -> Result<Tactic, AppError> {
    // Simplified parsing - in production, use proper JSON parsing
    let parts: Vec<&str> = s.split_whitespace().collect();

    if parts.is_empty() {
        return Err(AppError::BadRequest("Empty tactic".to_string()));
    }

    match parts[0].to_lowercase().as_str() {
        "apply" => Ok(Tactic::Apply(parts[1..].join(" "))),
        "intro" => Ok(Tactic::Intro(parts.get(1).map(|s| s.to_string()))),
        "rewrite" => Ok(Tactic::Rewrite(parts[1..].join(" "))),
        "simplify" => Ok(Tactic::Simplify),
        "reflexivity" => Ok(Tactic::Reflexivity),
        "assumption" => Ok(Tactic::Assumption),
        _ => Ok(Tactic::Custom {
            prover: "unknown".to_string(),
            command: parts[0].to_string(),
            args: parts[1..].iter().map(|s| s.to_string()).collect(),
        }),
    }
}

// ========== Error Handling ==========

#[derive(Debug)]
enum AppError {
    BadRequest(String),
    NotFound(String),
    ParseError(String),
    VerificationError(String),
    InternalError(String),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg),
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
            AppError::ParseError(msg) => (StatusCode::BAD_REQUEST, format!("Parse error: {}", msg)),
            AppError::VerificationError(msg) => (
                StatusCode::UNPROCESSABLE_ENTITY,
                format!("Verification error: {}", msg),
            ),
            AppError::InternalError(msg) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("Internal error: {}", msg),
            ),
        };

        let body = Json(serde_json::json!({
            "error": message,
        }));

        (status, body).into_response()
    }
}
