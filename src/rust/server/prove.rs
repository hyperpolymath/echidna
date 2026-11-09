// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! `POST /api/prove`.

use super::{AppError, AppState};
use anyhow::Result;
use axum::{extract::State, Json};
use echidna::ProverKind;
use serde::{Deserialize, Serialize};
use tracing::info;

// Used only by the direct factory path, which the `verisim` feature replaces
// with the dispatcher.
#[cfg(not(feature = "verisim"))]
use super::is_empty_state;
#[cfg(not(feature = "verisim"))]
use echidna::provers::ProverOutcome;
#[cfg(not(feature = "verisim"))]
use echidna::ProverConfig;
#[cfg(not(feature = "verisim"))]
use std::time::Instant;

/// Prove theorem endpoint
pub(super) async fn prove_handler(
    State(app_state): State<AppState>,
    Json(req): Json<ProveRequest>,
) -> Result<Json<ProveResponse>, AppError> {
    info!("Prove request for prover: {:?}", req.prover);

    // Route through the full dispatch pipeline when the verisim feature is
    // active.  This fires the VeriSimDB writer for every HTTP proof (parse
    // failures and final results), closing the S4 learning loop.  The writer
    // runs fire-and-forget — a VeriSimDB outage never blocks or alters a
    // result.  Response shape (success/goals/message) is preserved.
    #[cfg(feature = "verisim")]
    {
        let result = app_state
            .dispatcher
            .verify_proof(req.prover, &req.content)
            .await
            .map_err(|e| AppError::VerificationError(e.to_string()))?;
        return Ok(Json(ProveResponse {
            success: result.verified,
            goals: result.goals_remaining,
            message: result.message,
        }));
    }

    // Non-verisim path: direct factory + prover call (existing behaviour).
    #[cfg(not(feature = "verisim"))]
    {
        // Create prover
        let config = ProverConfig {
            timeout: req.timeout.unwrap_or(300),
            neural_enabled: req.neural.unwrap_or(true),
            ..ProverConfig::default()
        };

        let prover = echidna::provers::ProverFactory::create(req.prover, config)
            .map_err(|e| AppError::InternalError(e.to_string()))?;

        // Parse proof
        let state = prover
            .parse_string(&req.content)
            .await
            .map_err(|e| AppError::ParseError(e.to_string()))?;

        // Fail-fast on empty parse results (fixes false-positive: unrecognised
        // content produced an empty ProofState that re-exported to an empty file
        // which the backend prover then happily accepted).
        if is_empty_state(&state) && !req.content.trim().is_empty() {
            let outcome = ProverOutcome::InvalidInput {
                reason: "Parse produced no goals, theorems, definitions, or axioms — \
                         content not recognised by the selected prover backend"
                    .to_string(),
                location: None,
            };
            app_state
                .dispatcher
                .record_prover_result(req.prover, &outcome, 0);
            return Ok(Json(ProveResponse {
                success: false,
                goals: 0,
                message: "Parse produced no goals, theorems, definitions, or axioms — \
                         content not recognised by the selected prover backend"
                    .to_string(),
            }));
        }

        // Verify proof and record health metrics
        let verify_start = Instant::now();
        let valid = prover
            .verify_proof(&state)
            .await
            .map_err(|e| AppError::VerificationError(e.to_string()))?;
        let verify_elapsed_ms = verify_start.elapsed().as_millis() as u64;

        let outcome = if valid {
            ProverOutcome::Proved {
                elapsed_ms: verify_elapsed_ms,
            }
        } else {
            ProverOutcome::NoProofFound {
                elapsed_ms: verify_elapsed_ms,
                reason: Some("Proof verification failed".to_string()),
            }
        };
        app_state
            .dispatcher
            .record_prover_result(req.prover, &outcome, verify_elapsed_ms);

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
}

// ========== Request/Response Types ==========

#[derive(Deserialize)]
pub(super) struct ProveRequest {
    prover: ProverKind,
    content: String,
    timeout: Option<u64>,
    neural: Option<bool>,
}

#[derive(Serialize)]
pub(super) struct ProveResponse {
    success: bool,
    goals: usize,
    message: String,
}
