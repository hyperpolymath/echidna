// SPDX-License-Identifier: PMPL-1.0-or-later
// REST API request handlers - wired to ECHIDNA core

use axum::{
    extract::{Json, Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use echidna::exchange::{
    dedukti::DeduktiModule, opentheory::OpenTheoryArticle, DeduktiExporter, OpenTheoryExporter,
};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use std::sync::Arc;
use tokio::sync::Mutex;

// Import FFI wrapper
use crate::ffi_wrapper;

use crate::{models::*, AppState, ProofSession};

/// Wrapper for FFI-based prover backend
struct FfiProverBackend {
    handle: i32,
    config: ProverConfig,
}

impl FfiProverBackend {
    pub fn new(handle: i32) -> Self {
        FfiProverBackend {
            handle,
            config: ProverConfig::default(),
        }
    }
}

#[async_trait::async_trait]
impl ProverBackend for FfiProverBackend {
    async fn parse_file(
        &self,
        path: std::path::PathBuf,
    ) -> anyhow::Result<echidna::core::ProofState> {
        let content = std::fs::read_to_string(&path)?;
        ffi_wrapper::parse_string(self.handle, &content)?;
        Ok(echidna::core::ProofState::new(Term::Var(content)))
    }

    async fn parse_string(&self, content: &str) -> anyhow::Result<echidna::core::ProofState> {
        ffi_wrapper::parse_string(self.handle, content)?;
        Ok(echidna::core::ProofState::new(Term::Var(content.to_string())))
    }

    async fn verify_proof(&self, _state: &echidna::core::ProofState) -> anyhow::Result<bool> {
        ffi_wrapper::verify_proof(self.handle)
    }

    async fn apply_tactic(
        &self,
        state: &echidna::core::ProofState,
        tactic: &CoreTactic,
    ) -> anyhow::Result<CoreTacticResult> {
        let tactic_str = format!("{:?}", tactic);
        if ffi_wrapper::apply_tactic(self.handle, &tactic_str)? {
            Ok(CoreTacticResult::Success(state.clone()))
        } else {
            Ok(CoreTacticResult::Error("Tactic failed".to_string()))
        }
    }

    async fn suggest_tactics(
        &self,
        _state: &echidna::core::ProofState,
        limit: usize,
    ) -> anyhow::Result<Vec<CoreTactic>> {
        let tactic_names = ffi_wrapper::suggest_tactics(self.handle, limit)?;
        let tactics = tactic_names
            .into_iter()
            .map(|name| CoreTactic::Custom {
                prover: "ffi".to_string(),
                command: name,
                args: vec![],
            })
            .collect();
        Ok(tactics)
    }

    async fn export(&self, _state: &echidna::core::ProofState) -> anyhow::Result<String> {
        ffi_wrapper::export_proof(self.handle)
    }

    async fn version(&self) -> anyhow::Result<String> {
        ffi_wrapper::get_version()
    }

    fn kind(&self) -> CoreProverKind {
        // This is a bit simplified - in a real implementation we'd track the kind
        CoreProverKind::Lean // Default, would need to be set during creation
    }

    async fn search_theorems(&self, _pattern: &str) -> anyhow::Result<Vec<String>> {
        // FFI shim doesn't expose theorem search yet. Return empty list rather
        // than failing so portfolio/search callers degrade gracefully.
        Ok(Vec::new())
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

/// List all available provers (all 30)
#[utoipa::path(
    get,
    path = "/api/v1/provers",
    responses(
        (status = 200, description = "List of available provers", body = [ProverInfo])
    ),
    tag = "provers"
)]
pub async fn list_provers(State(_state): State<AppState>) -> impl IntoResponse {
    let provers: Vec<ProverInfo> = CoreProverKind::all()
        .into_iter()
        .map(|kind| ProverInfo {
            kind: core_kind_to_rest(&kind),
            version: format!("{:?} (ECHIDNA v0.1.0)", kind),
            tier: kind.tier(),
            complexity: kind.complexity(),
            available: true,
        })
        .collect();
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
    State(_state): State<AppState>,
    Path(kind_str): Path<String>,
) -> Result<Json<ProverInfo>, StatusCode> {
    let core_kind: CoreProverKind = kind_str.parse().map_err(|_| StatusCode::NOT_FOUND)?;

    Ok(Json(ProverInfo {
        kind: core_kind_to_rest(&core_kind),
        version: format!("{:?} (ECHIDNA v0.1.0)", core_kind),
        tier: core_kind.tier(),
        complexity: core_kind.complexity(),
        available: true,
    }))
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
    State(state): State<AppState>,
    Json(req): Json<ProofRequest>,
) -> Result<(StatusCode, Json<ProofResponse>), (StatusCode, String)> {
    let core_kind = rest_kind_to_core(&req.prover);

    let mut config = ProverConfig::default();
    if let Some(timeout) = req.timeout_seconds {
        config.timeout = timeout;
    }

    let prover = ProverFactory::create(core_kind, config)
        .map_err(|e| (StatusCode::BAD_REQUEST, e.to_string()))?;

    let proof_id = uuid::Uuid::new_v4().to_string();

    // Parse the goal
    let proof_state = prover
        .parse_string(&req.goal)
        .await
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Parse error: {}", e)))?;

    // Verify the proof
    let valid = prover.verify_proof(&proof_state).await.unwrap_or(false);

    let status = if valid {
        ProofStatus::Success
    } else if proof_state.goals.is_empty() {
        ProofStatus::Success
    } else {
        ProofStatus::InProgress
    };

    let script: Vec<String> = proof_state
        .proof_script
        .iter()
        .map(|t| format!("{:?}", t))
        .collect();

    let session = ProofSession {
        id: proof_id.clone(),
        prover_kind: core_kind,
        prover,
        state: Some(proof_state),
        goal: req.goal.clone(),
        status,
        history: vec![],
        start_time: std::time::Instant::now(),
    };

    state
        .sessions
        .write()
        .await
        .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

    let response = ProofResponse {
        id: proof_id,
        prover: req.prover,
        goal: req.goal,
        status,
        proof_script: script,
        time_elapsed: None,
        error_message: None,
    };

    Ok((StatusCode::CREATED, Json(response)))
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
    State(state): State<AppState>,
    Query(query): Query<ListProofsQuery>,
) -> impl IntoResponse {
    let sessions = state.sessions.read().await;
    let limit = query.limit.unwrap_or(100);

    let mut proofs = Vec::new();
    for (_, session_arc) in sessions.iter().take(limit) {
        let session = session_arc.lock().await;
        let elapsed = session.start_time.elapsed().as_secs_f64();

        if let Some(filter_status) = &query.status {
            if session.status != *filter_status {
                continue;
            }
        }

        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        proofs.push(ProofResponse {
            id: session.id.clone(),
            prover: core_kind_to_rest(&session.prover_kind),
            goal: session.goal.clone(),
            status: session.status,
            proof_script: script,
            time_elapsed: Some(elapsed),
            error_message: None,
        });
    }

    Json(proofs)
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
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<ProofResponse>, StatusCode> {
    let sessions = state.sessions.read().await;
    let session_arc = sessions.get(&id).ok_or(StatusCode::NOT_FOUND)?;
    let session = session_arc.lock().await;
    let elapsed = session.start_time.elapsed().as_secs_f64();

    let script: Vec<String> = session
        .state
        .as_ref()
        .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
        .unwrap_or_default();

    Ok(Json(ProofResponse {
        id: session.id.clone(),
        prover: core_kind_to_rest(&session.prover_kind),
        goal: session.goal.clone(),
        status: session.status,
        proof_script: script,
        time_elapsed: Some(elapsed),
        error_message: None,
    }))
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
pub async fn cancel_proof(State(state): State<AppState>, Path(id): Path<String>) -> StatusCode {
    let mut sessions = state.sessions.write().await;
    if sessions.remove(&id).is_some() {
        StatusCode::NO_CONTENT
    } else {
        StatusCode::NOT_FOUND
    }
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
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<TacticRequest>,
) -> Result<Json<TacticResponse>, (StatusCode, String)> {
    let sessions = state.sessions.read().await;
    let session_arc = sessions
        .get(&id)
        .ok_or((StatusCode::NOT_FOUND, "Proof not found".to_string()))?
        .clone();
    drop(sessions);

    let mut session = session_arc.lock().await;

    let proof_state = session
        .state
        .as_ref()
        .ok_or((StatusCode::BAD_REQUEST, "No proof state loaded".to_string()))?;

    // Parse tactic from request
    let tactic = parse_tactic(&req.name, &req.args);

    let result = session
        .prover
        .apply_tactic(proof_state, &tactic)
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;

    let (success, new_status) = match &result {
        CoreTacticResult::Success(new_state) => {
            let complete = new_state.is_complete();
            session.state = Some(new_state.clone());
            session.history.push(format!("{:?}", tactic));
            if complete {
                session.status = ProofStatus::Success;
            }
            (true, session.status)
        },
        CoreTacticResult::Error(_msg) => (false, session.status),
        CoreTacticResult::QED => {
            session.status = ProofStatus::Success;
            if let Some(s) = session.state.as_mut() {
                s.goals.clear();
            }
            (true, ProofStatus::Success)
        },
    };

    let elapsed = session.start_time.elapsed().as_secs_f64();
    let script: Vec<String> = session
        .state
        .as_ref()
        .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
        .unwrap_or_default();

    Ok(Json(TacticResponse {
        success,
        proof_state: ProofResponse {
            id: session.id.clone(),
            prover: core_kind_to_rest(&session.prover_kind),
            goal: session.goal.clone(),
            status: new_status,
            proof_script: script,
            time_elapsed: Some(elapsed),
            error_message: None,
        },
    }))
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
    State(state): State<AppState>,
    Path(id): Path<String>,
    Query(query): Query<ListProofsQuery>,
) -> Result<Json<Vec<Tactic>>, (StatusCode, String)> {
    let limit = query.limit.unwrap_or(5);

    let sessions = state.sessions.read().await;
    let session_arc = sessions
        .get(&id)
        .ok_or((StatusCode::NOT_FOUND, "Proof not found".to_string()))?
        .clone();
    drop(sessions);

    let session = session_arc.lock().await;

    let proof_state = session
        .state
        .as_ref()
        .ok_or((StatusCode::BAD_REQUEST, "No proof state loaded".to_string()))?;

    // Try Julia ML API first
    let goal_str = proof_state
        .goals
        .first()
        .map(|g| format!("{}", g.target))
        .unwrap_or_default();

    let julia_req = serde_json::json!({
        "goal": goal_str,
        "prover": format!("{:?}", session.prover_kind),
        "top_k": limit
    });

    if let Ok(resp) = state
        .ml_client
        .post(format!("{}/suggest", state.ml_api_url))
        .json(&julia_req)
        .send()
        .await
    {
        if resp.status().is_success() {
            if let Ok(ml_resp) = resp.json::<serde_json::Value>().await {
                if let Some(suggestions_arr) = ml_resp["suggestions"].as_array() {
                    let tactics: Vec<Tactic> = suggestions_arr
                        .iter()
                        .filter_map(|s| {
                            Some(Tactic {
                                name: s["tactic"].as_str()?.to_string(),
                                args: vec![],
                                description: Some("ML-suggested tactic".to_string()),
                                confidence: s["confidence"].as_f64().map(|c| c as f32),
                            })
                        })
                        .collect();

                    if !tactics.is_empty() {
                        return Ok(Json(tactics));
                    }
                }
            }
        }
    }

    // Fallback: use prover's built-in suggestions
    let core_tactics = session
        .prover
        .suggest_tactics(proof_state, limit)
        .await
        .unwrap_or_default();

    let tactics: Vec<Tactic> = core_tactics
        .iter()
        .map(|t| Tactic {
            name: format!("{:?}", t),
            args: vec![],
            description: Some("Prover-suggested tactic".to_string()),
            confidence: None,
        })
        .collect();

    Ok(Json(tactics))
}

// ========== Helper Functions ==========

fn parse_tactic(name: &str, args: &[String]) -> CoreTactic {
    match name.to_lowercase().as_str() {
        "apply" => CoreTactic::Apply(args.first().cloned().unwrap_or_default()),
        "intro" => CoreTactic::Intro(args.first().cloned()),
        "rewrite" => CoreTactic::Rewrite(args.first().cloned().unwrap_or_default()),
        "simplify" | "simp" => CoreTactic::Simplify,
        "reflexivity" | "refl" => CoreTactic::Reflexivity,
        "assumption" => CoreTactic::Assumption,
        "cases" => CoreTactic::Cases(Term::Var(args.first().cloned().unwrap_or_default())),
        "induction" => CoreTactic::Induction(Term::Var(args.first().cloned().unwrap_or_default())),
        "exact" => CoreTactic::Exact(Term::Var(args.first().cloned().unwrap_or_default())),
        _ => CoreTactic::Custom {
            prover: "rest".to_string(),
            command: name.to_string(),
            args: args.to_vec(),
        },
    }
}

fn core_kind_to_rest(kind: &CoreProverKind) -> ProverKind {
    match kind {
        CoreProverKind::Agda => ProverKind::Agda,
        CoreProverKind::Coq => ProverKind::Coq,
        CoreProverKind::Lean => ProverKind::Lean,
        CoreProverKind::Isabelle => ProverKind::Isabelle,
        CoreProverKind::Z3 => ProverKind::Z3,
        CoreProverKind::CVC5 => ProverKind::Cvc5,
        CoreProverKind::Metamath => ProverKind::Metamath,
        CoreProverKind::HOLLight => ProverKind::HolLight,
        CoreProverKind::Mizar => ProverKind::Mizar,
        CoreProverKind::PVS => ProverKind::Pvs,
        CoreProverKind::ACL2 => ProverKind::Acl2,
        CoreProverKind::HOL4 => ProverKind::Hol4,
        CoreProverKind::Idris2 => ProverKind::Idris2,
        CoreProverKind::Vampire => ProverKind::Vampire,
        CoreProverKind::EProver => ProverKind::EProver,
        CoreProverKind::SPASS => ProverKind::Spass,
        CoreProverKind::AltErgo => ProverKind::AltErgo,
        CoreProverKind::FStar => ProverKind::FStar,
        CoreProverKind::Dafny => ProverKind::Dafny,
        CoreProverKind::Why3 => ProverKind::Why3,
        CoreProverKind::TLAPS => ProverKind::TLAPS,
        CoreProverKind::Twelf => ProverKind::Twelf,
        CoreProverKind::Nuprl => ProverKind::Nuprl,
        CoreProverKind::Minlog => ProverKind::Minlog,
        CoreProverKind::Imandra => ProverKind::Imandra,
        CoreProverKind::GLPK => ProverKind::GLPK,
        CoreProverKind::SCIP => ProverKind::SCIP,
        CoreProverKind::MiniZinc => ProverKind::MiniZinc,
        CoreProverKind::Chuffed => ProverKind::Chuffed,
        CoreProverKind::ORTools => ProverKind::ORTools,
        _ => ProverKind::Vampire, // fallback for remaining provers (>30 in core)
    }
}

fn rest_kind_to_core(kind: &ProverKind) -> CoreProverKind {
    match kind {
        ProverKind::Agda => CoreProverKind::Agda,
        ProverKind::Coq => CoreProverKind::Coq,
        ProverKind::Lean => CoreProverKind::Lean,
        ProverKind::Isabelle => CoreProverKind::Isabelle,
        ProverKind::Z3 => CoreProverKind::Z3,
        ProverKind::Cvc5 => CoreProverKind::CVC5,
        ProverKind::Metamath => CoreProverKind::Metamath,
        ProverKind::HolLight => CoreProverKind::HOLLight,
        ProverKind::Mizar => CoreProverKind::Mizar,
        ProverKind::Pvs => CoreProverKind::PVS,
        ProverKind::Acl2 => CoreProverKind::ACL2,
        ProverKind::Hol4 => CoreProverKind::HOL4,
        ProverKind::Idris2 => CoreProverKind::Idris2,
        ProverKind::Vampire => CoreProverKind::Vampire,
        ProverKind::EProver => CoreProverKind::EProver,
        ProverKind::Spass => CoreProverKind::SPASS,
        ProverKind::AltErgo => CoreProverKind::AltErgo,
        ProverKind::FStar => CoreProverKind::FStar,
        ProverKind::Dafny => CoreProverKind::Dafny,
        ProverKind::Why3 => CoreProverKind::Why3,
        ProverKind::TLAPS => CoreProverKind::TLAPS,
        ProverKind::Twelf => CoreProverKind::Twelf,
        ProverKind::Nuprl => CoreProverKind::Nuprl,
        ProverKind::Minlog => CoreProverKind::Minlog,
        ProverKind::Imandra => CoreProverKind::Imandra,
        ProverKind::GLPK => CoreProverKind::GLPK,
        ProverKind::SCIP => CoreProverKind::SCIP,
        ProverKind::MiniZinc => CoreProverKind::MiniZinc,
        ProverKind::Chuffed => CoreProverKind::Chuffed,
        ProverKind::ORTools => CoreProverKind::ORTools,
    }
}

/// Export an existing proof session to a cross-prover exchange format
/// (OpenTheory or Dedukti). The session's current `ProofState` is fed to
/// the selected exporter; the result is serde-serialized and wrapped in
/// `ExportResponse.content`.
///
/// Returns 404 if the session id is unknown or 400 if the session has no
/// proof state loaded yet.
#[utoipa::path(
    get,
    path = "/api/v1/proofs/{id}/export",
    params(
        ("id" = String, Path, description = "Proof session id"),
        ("format" = ExchangeFormat, Query, description = "Target exchange format")
    ),
    responses(
        (status = 200, description = "Exported article / module", body = ExportResponse),
        (status = 400, description = "Session has no proof state"),
        (status = 404, description = "Session not found"),
        (status = 500, description = "Exporter error")
    ),
    tag = "exchange"
)]
pub async fn export_proof(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Query(query): Query<ExportQuery>,
) -> Result<Json<ExportResponse>, (StatusCode, String)> {
    let sessions = state.sessions.read().await;
    let session_arc = sessions
        .get(&id)
        .ok_or((StatusCode::NOT_FOUND, "Proof not found".to_string()))?
        .clone();
    drop(sessions);

    let session = session_arc.lock().await;
    let proof_state = session
        .state
        .as_ref()
        .ok_or((StatusCode::BAD_REQUEST, "No proof state loaded".to_string()))?;

    let content = match query.format {
        ExchangeFormat::OpenTheory => {
            let article = OpenTheoryExporter::export(proof_state)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
            serde_json::to_value(&article)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
        },
        ExchangeFormat::Dedukti => {
            let module = DeduktiExporter::export(proof_state)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
            serde_json::to_value(&module)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
        },
    };

    Ok(Json(ExportResponse {
        format: query.format,
        content,
    }))
}

/// Import an OpenTheory article or Dedukti module and return the
/// resulting `ProofState` as JSON. Stateless — does not create a
/// session. Used by round-trip tests and by clients that already have
/// proof artefacts they want echidna to parse.
///
/// Returns 400 if the content payload does not deserialize into the
/// expected format, or 500 if the importer rejects the structure.
#[utoipa::path(
    post,
    path = "/api/v1/exchange/import",
    request_body = ImportRequest,
    responses(
        (status = 200, description = "Imported ProofState as JSON", body = ImportResponse),
        (status = 400, description = "Content does not match declared format"),
        (status = 500, description = "Importer error")
    ),
    tag = "exchange"
)]
pub async fn import_proof(
    Json(req): Json<ImportRequest>,
) -> Result<Json<ImportResponse>, (StatusCode, String)> {
    let proof_state = match req.format {
        ExchangeFormat::OpenTheory => {
            let article: OpenTheoryArticle = serde_json::from_value(req.content).map_err(|e| {
                (
                    StatusCode::BAD_REQUEST,
                    format!("OpenTheoryArticle parse: {}", e),
                )
            })?;
            OpenTheoryExporter::import(&article)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
        },
        ExchangeFormat::Dedukti => {
            let module: DeduktiModule = serde_json::from_value(req.content).map_err(|e| {
                (
                    StatusCode::BAD_REQUEST,
                    format!("DeduktiModule parse: {}", e),
                )
            })?;
            DeduktiExporter::import(&module)
                .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?
        },
    };

    let proof_state = serde_json::to_value(&proof_state)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;

    Ok(Json(ImportResponse { proof_state }))
}

/// `POST /api/v1/consult` — free-form Q&A endpoint.
///
/// Used by echidnabot's Consultant mode and the BoJ
/// `cartridges/echidna-llm-mcp/consultant_qa` tool when it prefers a
/// native answer over its compose-of-search+suggest fallback.
///
/// Routes through the existing `LlmAdvisor` (which talks to BoJ's
/// model-router-mcp cartridge for cost-aware model selection). Returns
/// 503 when BoJ is unreachable so callers know to fall back.
pub async fn consult(
    State(state): State<AppState>,
    Json(req): Json<ConsultRequest>,
) -> Result<Json<ConsultResponse>, (StatusCode, String)> {
    if req.question.trim().is_empty() {
        return Err((
            StatusCode::BAD_REQUEST,
            "question must not be empty".to_string(),
        ));
    }

    // Borrow the advisor + ensure it's healthy. The advisor's check_health
    // is &mut, so we lock the AppState's advisor mutex briefly to run it.
    let mut advisor = state.llm_advisor.lock().await;
    if !advisor.is_available() {
        if let Err(e) = advisor.check_health().await {
            return Err((
                StatusCode::SERVICE_UNAVAILABLE,
                format!("LLM advisor health check failed: {}", e),
            ));
        }
        if !advisor.is_available() {
            return Err((
                StatusCode::SERVICE_UNAVAILABLE,
                "LLM advisor unavailable (BoJ unreachable)".to_string(),
            ));
        }
    }

    let llm_response = advisor
        .consult(&req.question, req.context.as_deref())
        .await
        .map_err(|e| (StatusCode::BAD_GATEWAY, format!("BoJ consult failed: {}", e)))?;

    Ok(Json(ConsultResponse {
        answer: llm_response.answer,
        model: llm_response.model,
        latency_ms: llm_response.latency_ms,
    }))
}
