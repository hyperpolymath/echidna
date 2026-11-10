// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! UI-specific routes: aspect tags, UI tactic suggestions, UI theorem search.

use super::AppError;
use anyhow::Result;
use axum::{extract::Query, Json};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::info;

/// Get aspect tags for filtering.
///
/// The tag vocabulary is intentionally hard-coded here — it's the UI's
/// facet list, not live-verified data, and needs to stay stable across
/// releases so saved filters keep working.
pub(super) async fn get_aspect_tags() -> Json<AspectTagsResponse> {
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

/// UI-specific tactic suggestion endpoint
pub(super) async fn suggest_tactics_ui(
    Json(req): Json<SuggestTacticsUIRequest>,
) -> Result<Json<SuggestTacticsUIResponse>, AppError> {
    let prover = req.prover.as_deref().unwrap_or("Coq");
    let top_k = req.top_k.unwrap_or(5);

    info!(
        "UI tactic suggestion request - prover: {}, goal: {}",
        prover, req.goal
    );

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
                                let premise = s
                                    .get("premises")
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
                    },
                    Err(e) => {
                        info!("Failed to parse Julia response: {}", e);
                        // Fall back to mock data
                        Ok(Json(SuggestTacticsUIResponse {
                            suggestions: vec![TacticSuggestion {
                                tactic: "auto".to_string(),
                                confidence: 0.5,
                                premise: None,
                                aspect_tags: vec!["automated".to_string()],
                            }],
                        }))
                    },
                }
            } else {
                info!("Julia API returned error status: {}", response.status());
                // Fall back to mock data
                Ok(Json(SuggestTacticsUIResponse {
                    suggestions: vec![TacticSuggestion {
                        tactic: "auto".to_string(),
                        confidence: 0.5,
                        premise: None,
                        aspect_tags: vec!["automated".to_string()],
                    }],
                }))
            }
        },
        Err(e) => {
            info!("Failed to connect to Julia ML API: {}", e);
            // Fall back to mock data if Julia service is down
            Ok(Json(SuggestTacticsUIResponse {
                suggestions: vec![TacticSuggestion {
                    tactic: "auto".to_string(),
                    confidence: 0.5,
                    premise: None,
                    aspect_tags: vec!["automated".to_string()],
                }],
            }))
        },
    }
}

/// UI-specific theorem search endpoint
pub(super) async fn search_theorems_ui(
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

    // Full-corpus search lives behind the REST interface
    // (`/api/search/theorems`) which indexes training_data/*.jsonl.
    // This UI endpoint is the keep-alive shim for the old ReScript
    // autocomplete — it returns canned exemplars so the UI has a
    // stable shape, and the real query goes through the search
    // workspace member.
    let results = vec![
        "Theorem: associativity_add (a + b) + c = a + (b + c)".to_string(),
        "Theorem: commutativity_mul a * b = b * a".to_string(),
        "Lemma: distributivity a * (b + c) = a * b + a * c".to_string(),
    ];

    Ok(Json(SearchTheoremsUIResponse { results }))
}

// ========== Request/Response Types ==========

#[derive(Serialize)]
struct AspectTag {
    name: String,
    category: String,
    active: bool,
}

#[derive(Serialize)]
pub(super) struct AspectTagsResponse {
    tags: Vec<AspectTag>,
}

#[derive(Deserialize)]
pub(super) struct SuggestTacticsUIRequest {
    goal: String, // Changed from goal_id to accept goal text directly
    prover: Option<String>,
    #[allow(dead_code)] // Reserved for future aspect-tag filtering
    active_tags: Option<Vec<String>>,
    top_k: Option<usize>,
}

#[derive(Serialize)]
pub(super) struct SuggestTacticsUIResponse {
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
pub(super) struct SearchTheoremsUIResponse {
    results: Vec<String>,
}
