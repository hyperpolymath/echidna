// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Proof-session routes: `/api/session/*`.

use super::{parse_tactic_from_json, AppError, AppState, ProofSession};
use anyhow::Result;
use axum::{
    extract::{Path, State},
    Json,
};
use echidna::core::TacticResult;
use echidna::{ProverConfig, ProverKind};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::info;

/// Create a new proof session
pub(super) async fn create_session(
    State(state): State<AppState>,
    Json(req): Json<CreateSessionRequest>,
) -> Result<Json<CreateSessionResponse>, AppError> {
    info!("Creating session for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Create session
    let session_id = echidna::ids::new_record_id().to_string();
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
pub(super) async fn get_session_state(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
) -> Result<Json<SessionStateResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?;

    let session = session.lock().await;

    Ok(Json(SessionStateResponse {
        goals: session
            .state
            .as_ref()
            .map(|s| s.goals.len())
            .unwrap_or_else(|| 0),
        complete: session
            .state
            .as_ref()
            .map(|s| s.is_complete())
            .unwrap_or(false),
        tactics_applied: session.history.len(),
    }))
}

/// Apply tactic to session
pub(super) async fn apply_tactic_handler(
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
    let Some(proof_state) = session.state.as_ref() else {
        return Err(AppError::BadRequest(
            "No proof loaded in session".to_string(),
        ));
    };
    let goals_before = proof_state.goals.len();

    // Parse tactic (simplified)
    let tactic = parse_tactic_from_json(&req.tactic)?;

    // Apply tactic
    let result = session
        .prover
        .apply_tactic(proof_state, &tactic)
        .await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    match result {
        TacticResult::Success(new_state) => {
            let complete = new_state.is_complete();
            let goals_remaining = new_state.goals.len();
            session.state = Some(new_state);
            session.history.push(req.tactic.clone());

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete,
                goals_remaining,
                message: "Tactic applied successfully".to_string(),
            }))
        },

        TacticResult::Error(msg) => Ok(Json(ApplyTacticResponse {
            success: false,
            complete: false,
            goals_remaining: goals_before,
            message: msg,
        })),

        TacticResult::QED => {
            if let Some(state) = session.state.as_mut() {
                state.goals.clear();
            }

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete: true,
                goals_remaining: 0,
                message: "Proof complete!".to_string(),
            }))
        },
    }
}

/// Get proof tree for a session
pub(super) async fn get_proof_tree(
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

// ========== Request/Response Types ==========

#[derive(Deserialize)]
pub(super) struct CreateSessionRequest {
    prover: ProverKind,
}

#[derive(Serialize)]
pub(super) struct CreateSessionResponse {
    session_id: String,
}

#[derive(Serialize)]
pub(super) struct SessionStateResponse {
    goals: usize,
    complete: bool,
    tactics_applied: usize,
}

#[derive(Deserialize)]
pub(super) struct ApplyTacticRequest {
    tactic: String,
}

#[derive(Serialize)]
pub(super) struct ApplyTacticResponse {
    success: bool,
    complete: bool,
    goals_remaining: usize,
    message: String,
}

#[derive(Serialize)]
pub(super) struct ProofTreeResponse {
    tree: serde_json::Value,
}
