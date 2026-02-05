// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! HTTP API server for ECHIDNA
//!
//! Provides REST API and WebSocket endpoints for theorem proving

use anyhow::Result;
use axum::{
    extract::{
        ws::{Message, WebSocket, WebSocketUpgrade},
        Path, Query, State,
    },
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use colored::Colorize;
use echidna::core::{ProofState, Tactic, TacticResult};
use echidna::{ProverBackend, ProverConfig, ProverKind};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock};
use tower_http::cors::CorsLayer;
use tracing::info;

/// Application state shared across handlers
#[derive(Clone)]
struct AppState {
    /// Active proof sessions (session_id -> ProofSession)
    sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    /// HTTP client for Julia ML API
    ml_client: Client,
    /// Julia ML API base URL
    ml_api_url: String,
}

/// A proof session
struct ProofSession {
    prover: Box<dyn ProverBackend>,
    state: Option<ProofState>,
    history: Vec<String>,
}

/// Start the HTTP server
pub async fn start_server(port: u16, host: String, enable_cors: bool) -> Result<()> {
    // Create HTTP client for Julia ML API
    let ml_client = Client::builder()
        .timeout(Duration::from_secs(10))
        .build()?;

    let ml_api_url = "http://127.0.0.1:8090".to_string();

    // Test Julia ML connection
    match ml_client.get(format!("{}/health", ml_api_url)).send().await {
        Ok(resp) if resp.status().is_success() => {
            info!("✓ Connected to Julia ML API at {}", ml_api_url);
        }
        _ => {
            info!("⚠ Julia ML API not available at {} (will use fallback)", ml_api_url);
        }
    }

    let state = AppState {
        sessions: Arc::new(RwLock::new(HashMap::new())),
        ml_client,
        ml_api_url,
    };

    // Build router
    let mut app = Router::new()
        // REST API endpoints
        .route("/api/health", get(health_check))
        .route("/api/provers", get(list_provers))
        .route("/api/prove", post(prove_handler))
        .route("/api/verify", post(verify_handler))
        .route("/api/suggest", post(suggest_handler))
        .route("/api/search", get(search_handler))
        .route("/api/session/create", post(create_session))
        .route("/api/session/:id/state", get(get_session_state))
        .route("/api/session/:id/apply", post(apply_tactic_handler))
        .route("/api/session/:id/tree", get(get_proof_tree))
        // Additional UI-specific endpoints
        .route("/api/aspect-tags", get(get_aspect_tags))
        .route("/api/tactics/suggest", post(suggest_tactics_ui))
        .route("/api/theorems/search", get(search_theorems_ui))
        // WebSocket endpoint
        .route("/ws/interactive", get(websocket_handler))
        .with_state(state);

    // Add CORS if enabled
    if enable_cors {
        app = app.layer(CorsLayer::permissive());
    }

    // Bind server
    let addr: SocketAddr = format!("{}:{}", host, port).parse()?;

    println!("{}", "╔═══════════════════════════════════════════════════════════╗".cyan());
    println!("{}", "║  ECHIDNA HTTP API Server                                  ║".cyan().bold());
    println!("{}", "╚═══════════════════════════════════════════════════════════╝".cyan());
    println!();
    println!("Server listening on: {}", format!("https://{}", addr).green().bold());
    println!();
    println!("{}", "Endpoints:".yellow().bold());
    println!("  GET  /api/health              - Health check");
    println!("  GET  /api/provers             - List available provers");
    println!("  POST /api/prove               - Prove a theorem");
    println!("  POST /api/verify              - Verify a proof");
    println!("  POST /api/suggest             - Get tactic suggestions");
    println!("  GET  /api/search?q=<pattern>  - Search theorems");
    println!("  POST /api/session/create      - Create proof session");
    println!("  GET  /api/session/:id/state   - Get session state");
    println!("  POST /api/session/:id/apply   - Apply tactic to session");
    println!("  WS   /ws/interactive          - WebSocket live proof session");
    println!();
    println!("Press Ctrl+C to stop the server");
    println!();

    // Start server
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app)
        .await?;

    Ok(())
}

// ========== REST API Handlers ==========

/// Health check endpoint
async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// List available provers
async fn list_provers() -> Json<ProversResponse> {
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

/// Prove theorem endpoint
async fn prove_handler(
    Json(req): Json<ProveRequest>,
) -> Result<Json<ProveResponse>, AppError> {
    info!("Prove request for prover: {:?}", req.prover);

    // Create prover
    let mut config = ProverConfig::default();
    config.timeout = req.timeout.unwrap_or(300);
    config.neural_enabled = req.neural.unwrap_or(true);

    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof
    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    // Verify proof
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(ProveResponse {
        success: valid,
        goals: state.goals.len(),
        message: if valid {
            "Proof verified successfully".to_string()
        } else {
            "Proof verification failed".to_string()
        },
    }))
}

/// Verify proof endpoint
async fn verify_handler(
    Json(req): Json<VerifyRequest>,
) -> Result<Json<VerifyResponse>, AppError> {
    info!("Verify request for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof
    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    // Verify
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(VerifyResponse {
        valid,
        goals_remaining: state.goals.len(),
        tactics_used: state.proof_script.len(),
    }))
}

/// Get tactic suggestions
async fn suggest_handler(
    State(state): State<AppState>,
    Json(req): Json<SuggestRequest>,
) -> Result<Json<SuggestResponse>, AppError> {
    info!("Suggest request for prover: {:?}", req.prover);

    // Try Julia ML API first
    let julia_req = json!({
        "goal": req.content,
        "prover": format!("{:?}", req.prover),
        "top_k": req.limit.unwrap_or(5)
    });

    match state.ml_client
        .post(format!("{}/suggest", state.ml_api_url))
        .json(&julia_req)
        .send()
        .await
    {
        Ok(resp) if resp.status().is_success() => {
            if let Ok(ml_resp) = resp.json::<serde_json::Value>().await {
                if let Some(suggestions_arr) = ml_resp["suggestions"].as_array() {
                    let suggestions: Vec<String> = suggestions_arr
                        .iter()
                        .filter_map(|s| s["tactic"].as_str().map(|t| t.to_string()))
                        .collect();

                    if !suggestions.is_empty() {
                        info!("✓ Got {} ML suggestions", suggestions.len());
                        return Ok(Json(SuggestResponse { suggestions }));
                    }
                }
            }
        }
        _ => {
            info!("ML API unavailable, using prover fallback");
        }
    }

    // Fallback: Use prover's built-in suggestions
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    let tactics = prover
        .suggest_tactics(&state, req.limit.unwrap_or(5))
        .await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    let suggestions = tactics
        .iter()
        .map(|t| format!("{:?}", t))
        .collect();

    Ok(Json(SuggestResponse { suggestions }))
}

/// Search theorems
async fn search_handler(
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<SearchResponse>, AppError> {
    let pattern = params
        .get("q")
        .ok_or_else(|| AppError::BadRequest("Missing query parameter 'q'".to_string()))?;

    let prover_name = params.get("prover");

    info!("Search request: pattern={}, prover={:?}", pattern, prover_name);

    let mut all_results = Vec::new();

    // Determine which provers to search
    let provers: Vec<ProverKind> = if let Some(name) = prover_name {
        vec![parse_prover_kind(name)?]
    } else {
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
        ]
    };

    // Search each prover
    for prover_kind in provers {
        let config = ProverConfig::default();

        if let Ok(prover) = echidna::provers::ProverFactory::create(prover_kind, config) {
            if let Ok(results) = prover.search_theorems(pattern).await {
                all_results.extend(results);
            }
        }
    }

    let count = all_results.len();
    Ok(Json(SearchResponse {
        results: all_results,
        count,
    }))
}

/// Create a new proof session
async fn create_session(
    State(state): State<AppState>,
    Json(req): Json<CreateSessionRequest>,
) -> Result<Json<CreateSessionResponse>, AppError> {
    info!("Creating session for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Create session
    let session_id = uuid::Uuid::new_v4().to_string();
    let session = ProofSession {
        prover,
        state: None,
        history: Vec::new(),
    };

    // Store session
    state
        .sessions
        .write()
        .await
        .insert(session_id.clone(), Arc::new(Mutex::new(session)));

    Ok(Json(CreateSessionResponse { session_id }))
}

/// Get session state
async fn get_session_state(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
) -> Result<Json<SessionStateResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?;

    let session = session.lock().await;

    Ok(Json(SessionStateResponse {
        goals: session.state.as_ref().map(|s| s.goals.len()).unwrap_or(0),
        complete: session.state.as_ref().map(|s| s.is_complete()).unwrap_or(false),
        tactics_applied: session.history.len(),
    }))
}

/// Apply tactic to session
async fn apply_tactic_handler(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
    Json(req): Json<ApplyTacticRequest>,
) -> Result<Json<ApplyTacticResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session_arc = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?
        .clone();

    drop(sessions);

    let mut session = session_arc.lock().await;

    // Ensure we have a state
    if session.state.is_none() {
        return Err(AppError::BadRequest("No proof loaded in session".to_string()));
    }

    // Parse tactic (simplified)
    let tactic = parse_tactic_from_json(&req.tactic)?;

    // Apply tactic
    let proof_state = session.state.as_ref().unwrap();
    let result = session.prover.apply_tactic(proof_state, &tactic).await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    match result {
        TacticResult::Success(new_state) => {
            let complete = new_state.is_complete();
            session.state = Some(new_state);
            session.history.push(req.tactic.clone());

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete,
                goals_remaining: session.state.as_ref().unwrap().goals.len(),
                message: "Tactic applied successfully".to_string(),
            }))
        }

        TacticResult::Error(msg) => {
            Ok(Json(ApplyTacticResponse {
                success: false,
                complete: false,
                goals_remaining: session.state.as_ref().unwrap().goals.len(),
                message: msg,
            }))
        }

        TacticResult::QED => {
            session.state.as_mut().unwrap().goals.clear();

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete: true,
                goals_remaining: 0,
                message: "Proof complete!".to_string(),
            }))
        }
    }
}

/// Get aspect tags for filtering
async fn get_aspect_tags() -> Json<AspectTagsResponse> {
    // Return hardcoded aspect tags for now
    // TODO: Load from configuration or database
    let tags = vec![
        AspectTag {
            name: "algebraic".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "geometric".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "logical".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "inductive".to_string(),
            category: "technique".to_string(),
            active: false,
        },
        AspectTag {
            name: "deductive".to_string(),
            category: "technique".to_string(),
            active: false,
        },
        AspectTag {
            name: "automated".to_string(),
            category: "technique".to_string(),
            active: false,
        },
    ];

    Json(AspectTagsResponse { tags })
}

/// Get proof tree for a session
async fn get_proof_tree(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
) -> Result<Json<ProofTreeResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?;

    let session = session.lock().await;

    // Build proof tree from session state
    let tree = if let Some(proof_state) = &session.state {
        serde_json::json!({
            "id": "root",
            "type": "goal",
            "label": proof_state.goals.first()
                .map(|g| format!("{:?}", g.target))
                .unwrap_or_else(|| "No goals".to_string()),
            "children": []
        })
    } else {
        serde_json::json!({
            "id": "root",
            "type": "goal",
            "label": "No proof state",
            "children": []
        })
    };

    Ok(Json(ProofTreeResponse { tree }))
}

/// UI-specific tactic suggestion endpoint
async fn suggest_tactics_ui(
    Json(req): Json<SuggestTacticsUIRequest>,
) -> Result<Json<SuggestTacticsUIResponse>, AppError> {
    let prover = req.prover.as_deref().unwrap_or("Coq");
    let top_k = req.top_k.unwrap_or(5);

    info!("UI tactic suggestion request - prover: {}, goal: {}", prover, req.goal);

    // Call Julia ML API for real AI predictions
    let client = reqwest::Client::new();
    let julia_url = "http://127.0.0.1:8090/suggest";

    let julia_request = serde_json::json!({
        "goal": req.goal,
        "prover": prover,
        "top_k": top_k
    });

    match client.post(julia_url).json(&julia_request).send().await {
        Ok(response) => {
            if response.status().is_success() {
                match response.json::<serde_json::Value>().await {
                    Ok(json) => {
                        let empty_vec = vec![];
                        let suggestions_json = json["suggestions"].as_array().unwrap_or(&empty_vec);
                        let suggestions: Vec<TacticSuggestion> = suggestions_json
                            .iter()
                            .map(|s| {
                                let confidence = s["confidence"].as_f64().unwrap_or(0.0);
                                let tactic = s["tactic"].as_str().unwrap_or("auto").to_string();
                                let premise = s.get("premises")
                                    .and_then(|p| p.as_array())
                                    .and_then(|arr| arr.first())
                                    .and_then(|v| v.as_str())
                                    .map(String::from);

                                // Infer aspect tags from confidence and tactic
                                let aspect_tags = if confidence > 0.8 {
                                    vec!["automated".to_string()]
                                } else if tactic.contains("intro") {
                                    vec!["deductive".to_string()]
                                } else {
                                    vec!["algebraic".to_string(), "deductive".to_string()]
                                };

                                TacticSuggestion {
                                    tactic,
                                    confidence,
                                    premise,
                                    aspect_tags,
                                }
                            })
                            .collect();

                        Ok(Json(SuggestTacticsUIResponse { suggestions }))
                    }
                    Err(e) => {
                        info!("Failed to parse Julia response: {}", e);
                        // Fall back to mock data
                        Ok(Json(SuggestTacticsUIResponse {
                            suggestions: vec![
                                TacticSuggestion {
                                    tactic: "auto".to_string(),
                                    confidence: 0.5,
                                    premise: None,
                                    aspect_tags: vec!["automated".to_string()],
                                }
                            ]
                        }))
                    }
                }
            } else {
                info!("Julia API returned error status: {}", response.status());
                // Fall back to mock data
                Ok(Json(SuggestTacticsUIResponse {
                    suggestions: vec![
                        TacticSuggestion {
                            tactic: "auto".to_string(),
                            confidence: 0.5,
                            premise: None,
                            aspect_tags: vec!["automated".to_string()],
                        }
                    ]
                }))
            }
        }
        Err(e) => {
            info!("Failed to connect to Julia ML API: {}", e);
            // Fall back to mock data if Julia service is down
            Ok(Json(SuggestTacticsUIResponse {
                suggestions: vec![
                    TacticSuggestion {
                        tactic: "auto".to_string(),
                        confidence: 0.5,
                        premise: None,
                        aspect_tags: vec!["automated".to_string()],
                    }
                ]
            }))
        }
    }
}

/// UI-specific theorem search endpoint
async fn search_theorems_ui(
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<SearchTheoremsUIResponse>, AppError> {
    let query = params
        .get("query")
        .or_else(|| params.get("q"))
        .ok_or_else(|| AppError::BadRequest("Missing query parameter".to_string()))?;

    let _tags = params
        .get("tags")
        .map(|t| t.split(',').map(String::from).collect::<Vec<_>>())
        .unwrap_or_default();

    info!("UI theorem search: query={}", query);

    // For now, return mock results
    // TODO: Integrate with actual theorem database
    let results = vec![
        format!("Theorem: associativity_add (a + b) + c = a + (b + c)"),
        format!("Theorem: commutativity_mul a * b = b * a"),
        format!("Lemma: distributivity a * (b + c) = a * b + a * c"),
    ];

    Ok(Json(SearchTheoremsUIResponse { results }))
}

// ========== WebSocket Handler ==========

/// WebSocket handler for interactive proof sessions
async fn websocket_handler(
    ws: WebSocketUpgrade,
    State(state): State<AppState>,
) -> Response {
    ws.on_upgrade(|socket| handle_websocket(socket, state))
}

/// Handle WebSocket connection
async fn handle_websocket(socket: WebSocket, _state: AppState) {
    info!("WebSocket connection established");

    let (mut sender, mut receiver) = socket.split();

    // For this example, we'll just echo messages
    // In production, this would handle proof session commands
    while let Some(msg) = receiver.next().await {
        match msg {
            Ok(Message::Text(text)) => {
                info!("Received: {}", text);

                // Echo back
                if sender
                    .send(Message::Text(format!("Echo: {}", text)))
                    .await
                    .is_err()
                {
                    break;
                }
            }
            Ok(Message::Close(_)) => {
                info!("WebSocket closed");
                break;
            }
            _ => {}
        }
    }
}

// ========== Helper Functions ==========

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

// ========== Request/Response Types ==========

#[derive(Deserialize)]
struct ProveRequest {
    prover: ProverKind,
    content: String,
    timeout: Option<u64>,
    neural: Option<bool>,
}

#[derive(Serialize)]
struct ProveResponse {
    success: bool,
    goals: usize,
    message: String,
}

#[derive(Deserialize)]
struct VerifyRequest {
    prover: ProverKind,
    content: String,
}

#[derive(Serialize)]
struct VerifyResponse {
    valid: bool,
    goals_remaining: usize,
    tactics_used: usize,
}

#[derive(Deserialize)]
struct SuggestRequest {
    prover: ProverKind,
    content: String,
    limit: Option<usize>,
}

#[derive(Serialize)]
struct SuggestResponse {
    suggestions: Vec<String>,
}

#[derive(Serialize)]
struct SearchResponse {
    results: Vec<String>,
    count: usize,
}

#[derive(Deserialize)]
struct CreateSessionRequest {
    prover: ProverKind,
}

#[derive(Serialize)]
struct CreateSessionResponse {
    session_id: String,
}

#[derive(Serialize)]
struct SessionStateResponse {
    goals: usize,
    complete: bool,
    tactics_applied: usize,
}

#[derive(Deserialize)]
struct ApplyTacticRequest {
    tactic: String,
}

#[derive(Serialize)]
struct ApplyTacticResponse {
    success: bool,
    complete: bool,
    goals_remaining: usize,
    message: String,
}

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    version: String,
}

#[derive(Serialize)]
struct ProversResponse {
    provers: Vec<ProverInfo>,
}

#[derive(Serialize)]
struct ProverInfo {
    name: String,
    tier: u8,
    complexity: u8,
}

#[derive(Serialize)]
struct AspectTag {
    name: String,
    category: String,
    active: bool,
}

#[derive(Serialize)]
struct AspectTagsResponse {
    tags: Vec<AspectTag>,
}

#[derive(Serialize)]
struct ProofTreeResponse {
    tree: serde_json::Value,
}

#[derive(Deserialize)]
struct SuggestTacticsUIRequest {
    goal: String,  // Changed from goal_id to accept goal text directly
    prover: Option<String>,
    active_tags: Option<Vec<String>>,
    top_k: Option<usize>,
}

#[derive(Serialize)]
struct SuggestTacticsUIResponse {
    suggestions: Vec<TacticSuggestion>,
}

#[derive(Serialize)]
struct TacticSuggestion {
    tactic: String,
    confidence: f64,
    premise: Option<String>,
    aspect_tags: Vec<String>,
}

#[derive(Serialize)]
struct SearchTheoremsUIResponse {
    results: Vec<String>,
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
            AppError::VerificationError(msg) => {
                (StatusCode::UNPROCESSABLE_ENTITY, format!("Verification error: {}", msg))
            }
            AppError::InternalError(msg) => {
                (StatusCode::INTERNAL_SERVER_ERROR, format!("Internal error: {}", msg))
            }
        };

        let body = Json(serde_json::json!({
            "error": message,
        }));

        (status, body).into_response()
    }
}

// Import for WebSocket stream splitting
use futures::stream::StreamExt;
use futures::SinkExt;
