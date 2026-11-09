// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! `POST /api/agent/plan`: MetaController planning without execution.

use super::AppState;
use axum::{extract::State, response::IntoResponse, Json};
use echidna::agent::meta_controller::Plan;
use echidna::agent::AgenticGoal;
use echidna::core::{Goal, Term};
use echidna::ProverKind;
use serde::Deserialize;
use serde_json::json;

// ========== Agent Planning ==========

/// Request to `POST /api/agent/plan`.
///
/// Asks the MetaController to plan a proof attempt: which prover to use,
/// which coprocessor preconditions to run first, and the Bayesian-estimated
/// timeout.  The response is a `Plan` that callers can inspect before
/// deciding whether to submit a full `/api/verify` or `/api/prove` request.
///
/// `aspects` drive the coprocessor routing (e.g. `"arithmetic.factorisation"`
/// triggers a Math precondition; `"algebra.groebner.basis"` triggers Singular).
/// `preferred_prover` and `candidates` are both optional — omitting both lets
/// the Pareto ranker pick freely from Z3 as the default.
#[derive(Debug, Deserialize)]
pub(super) struct AgentPlanRequest {
    /// Goal aspect tags (e.g. `["arithmetic.factorisation", "crypto.hash.sha256"]`).
    #[serde(default)]
    aspects: Vec<String>,

    /// Client's preferred prover, if any.  Overridden by Pareto ranking when
    /// `candidates` is non-empty.
    preferred_prover: Option<ProverKind>,

    /// Candidate provers to rank.  When empty, `preferred_prover` (or Z3)
    /// is selected directly without Pareto scoring.
    #[serde(default)]
    candidates: Vec<ProverKind>,

    /// Default timeout hint (ms) used when no historical data is available.
    #[serde(default = "default_timeout_ms")]
    default_timeout_ms: u64,
}

fn default_timeout_ms() -> u64 {
    30_000
}

/// `POST /api/agent/plan` — return a MetaController plan for the given goal aspects.
///
/// Does not execute any provers or coprocessors; it only plans.  Callers use
/// the returned `coprocessor_preconditions` to understand what computational
/// preparation the system recommends before submitting the proof content.
pub(super) async fn agent_plan_handler(
    State(state): State<AppState>,
    Json(req): Json<AgentPlanRequest>,
) -> impl IntoResponse {
    // Build a minimal AgenticGoal from the request metadata.  The goal target
    // is a placeholder (`Term::Const("?")`) because planning doesn't inspect
    // the proof content — only the aspects and prover preferences matter here.
    use echidna::agent::Priority;
    let goal = AgenticGoal {
        goal: Goal {
            id: echidna::ids::new_record_id().to_string(),
            target: Term::Const("?".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: req.preferred_prover,
        aspects: req.aspects,
        parent: None,
    };

    let plan: Plan = if req.candidates.is_empty() {
        state.meta_controller.plan(&goal).await
    } else {
        use echidna::verification::confidence::TrustLevel;
        state
            .meta_controller
            .plan_with_pareto(
                &goal,
                &req.candidates,
                req.default_timeout_ms,
                TrustLevel::Level2,
            )
            .await
    };

    Json(json!({
        "prover": format!("{:?}", plan.prover),
        "estimated_timeout_ms": plan.estimated_timeout_ms,
        "rationale": plan.rationale,
        "coprocessor_preconditions": plan.coprocessor_preconditions
            .iter()
            .map(|p| json!({
                "kind": format!("{:?}", p.kind),
                "aspect": p.aspect,
            }))
            .collect::<Vec<_>>(),
    }))
}
