// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Tactic suggestion and theorem search: `/api/suggest`, `/api/search`.

use super::{parse_prover_kind, AppError, AppState};
use anyhow::Result;
use axum::{
    extract::{Query, State},
    Json,
};
use echidna::{ProverConfig, ProverKind};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::HashMap;
use tracing::info;

/// Get tactic suggestions
pub(super) async fn suggest_handler(
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

    match state
        .ml_client
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
        },
        _ => {
            info!("ML API unavailable, using prover fallback");
        },
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

    let suggestions = tactics.iter().map(|t| format!("{:?}", t)).collect();

    Ok(Json(SuggestResponse { suggestions }))
}

/// Search theorems
pub(super) async fn search_handler(
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<SearchResponse>, AppError> {
    let pattern = params
        .get("q")
        .ok_or_else(|| AppError::BadRequest("Missing query parameter 'q'".to_string()))?;

    let prover_name = params.get("prover");

    info!(
        "Search request: pattern={}, prover={:?}",
        pattern, prover_name
    );

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

    // Cross-prover layer (see main.rs::search_command for rationale).
    // Folds VeriSimDB matches into the same response so REST clients
    // see results from backends without native search commands too.
    let verisim_url =
        std::env::var("VERISIM_URL").unwrap_or_else(|_| "http://localhost:8080".to_string());
    if let Ok(cross) = echidna::vcl_ut::cross_prover_search_names(&verisim_url, pattern, 50).await {
        all_results.extend(cross);
    }

    let count = all_results.len();
    Ok(Json(SearchResponse {
        results: all_results,
        count,
    }))
}

// ========== Request/Response Types ==========

#[derive(Deserialize)]
pub(super) struct SuggestRequest {
    prover: ProverKind,
    content: String,
    limit: Option<usize>,
}

#[derive(Serialize)]
pub(super) struct SuggestResponse {
    suggestions: Vec<String>,
}

#[derive(Serialize)]
pub(super) struct SearchResponse {
    results: Vec<String>,
    count: usize,
}
