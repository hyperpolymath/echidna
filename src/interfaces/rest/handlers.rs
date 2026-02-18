// SPDX-License-Identifier: PMPL-1.0-or-later
// REST API request handlers - wired to ECHIDNA core

use axum::{
    extract::{Json, Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use std::sync::Arc;
use tokio::sync::Mutex;

use crate::{models::*, AppState, ProofSession};

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
    let core_kind: CoreProverKind = kind_str
        .parse()
        .map_err(|_| StatusCode::NOT_FOUND)?;

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
    let valid = prover
        .verify_proof(&proof_state)
        .await
        .unwrap_or(false);

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
pub async fn cancel_proof(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> StatusCode {
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
        }
        CoreTacticResult::Error(_msg) => (false, session.status),
        CoreTacticResult::QED => {
            session.status = ProofStatus::Success;
            if let Some(s) = session.state.as_mut() {
                s.goals.clear();
            }
            (true, ProofStatus::Success)
        }
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

    if let Ok(resp) = state.ml_client
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
        _ => ProverKind::Vampire, // fallback for remaining provers
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
    }
}
