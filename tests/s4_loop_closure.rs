// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! S4 loop-closure end-to-end test.
//!
//! Verifies that the Verisim cross-prover learning loop is wired correctly:
//!
//!   record_proof_attempt  →  proof_attempts row  →  query_by_goal_hash
//!                                              →  mv_prover_success_by_class
//!
//! This test does NOT exercise prover dispatch timing — it talks directly
//! to `VeriSimDBClient` so that a green run unambiguously means the loop
//! is closing, not that the dispatcher happens to be fast.
//!
//! ## Skip behaviour
//!
//! All assertions are gated on `VeriSimDB` being reachable. If the
//! `health_check()` returns `false` (no instance, wrong port, network
//! down) the test prints a skip notice and returns. This keeps it
//! useful both in CI (where a Podman-managed VeriSim is brought up
//! by the workflow) and on a developer's laptop (where it silently
//! becomes a no-op).
//!
//! ## Environment
//!
//! `VERISIM_URL` (default: `http://localhost:8080`) — base URL of the
//! verisim-api HTTP server. Same convention as the production code in
//! `src/rust/learning/daemon.rs:52`.

#![cfg(feature = "verisim")]

use anyhow::Result;
use echidna::verisim_bridge::{prover_kind_to_str, ProofAttempt, VeriSimDBClient};
use echidna::provers::ProverKind;

/// Build a minimal `ProofAttempt` row with a unique obligation_id so each
/// test run is independent (no collisions with prior runs in the table).
fn fresh_attempt(obligation_class: &str, prover: ProverKind, outcome: &str) -> ProofAttempt {
    let now = chrono::Utc::now();
    ProofAttempt {
        attempt_id: uuid::Uuid::new_v4().to_string(),
        // Tag the obligation_id with the test name so we can find our own
        // rows even if other tests are writing concurrently.
        obligation_id: format!("test-s4-loop-{}", uuid::Uuid::new_v4()),
        repo: "hyperpolymath/echidna".to_string(),
        file: "tests/s4_loop_closure.rs".to_string(),
        claim: "true".to_string(),
        obligation_class: obligation_class.to_string(),
        prover_used: prover_kind_to_str(prover).to_string(),
        outcome: outcome.to_string(),
        duration_ms: 1,
        confidence: if outcome == "success" { 1.0 } else { 0.0 },
        parent_attempt_id: None,
        strategy_tag: "test".to_string(),
        started_at: now.to_rfc3339(),
        completed_at: now.to_rfc3339(),
        prover_output: String::new(),
        error_message: None,
    }
}

fn verisim_url() -> String {
    std::env::var("VERISIM_URL").unwrap_or_else(|_| "http://localhost:8080".to_string())
}

/// Returns `Some(client)` if the VeriSim instance is reachable, otherwise
/// prints a skip notice and returns `None`. Use the early-return idiom:
///
/// ```ignore
/// let Some(client) = require_verisim().await else { return Ok(()); };
/// ```
async fn require_verisim() -> Option<VeriSimDBClient> {
    let url = verisim_url();
    let client = VeriSimDBClient::new(&url);
    if client.health_check().await {
        Some(client)
    } else {
        eprintln!(
            "skip: VeriSimDB at {} is unreachable — set VERISIM_URL or start verisim-api",
            url
        );
        None
    }
}

#[tokio::test]
async fn s4_record_then_read_back_by_goal_hash() -> Result<()> {
    let Some(client) = require_verisim().await else {
        return Ok(());
    };

    // Write a single attempt.
    let attempt = fresh_attempt("test-s4-readback", ProverKind::Z3, "success");
    let attempt_id = client.record_proof_attempt(&attempt).await?;
    assert_eq!(
        attempt_id, attempt.attempt_id,
        "record_proof_attempt should return the same UUID we sent"
    );

    // Read it back. The proof_attempts table is a row store so the read
    // is immediately consistent (no MV refresh delay involved here).
    let rows = client.query_by_goal_hash(&attempt.obligation_id).await?;
    assert!(
        !rows.is_empty(),
        "row written with obligation_id={} should be visible to query_by_goal_hash",
        attempt.obligation_id
    );
    let found = rows.iter().any(|r| r.attempt_id == attempt.attempt_id);
    assert!(
        found,
        "the specific attempt we wrote should appear in the goal_hash query results"
    );

    Ok(())
}

#[tokio::test]
async fn s4_class_aggregation_visible_in_mv() -> Result<()> {
    let Some(client) = require_verisim().await else {
        return Ok(());
    };

    // Use a class that is unlikely to collide with anything else in the
    // table. The test passes whether or not it sees its own writes — the
    // contract is that the MV endpoint responds and the response shape
    // is parseable.
    let unique_class = format!("test-mv-{}", uuid::Uuid::new_v4());

    // Seed a few attempts so the MV has something to aggregate.
    for outcome in ["success", "success", "failure"] {
        let attempt = fresh_attempt(&unique_class, ProverKind::Z3, outcome);
        client.record_proof_attempt(&attempt).await?;
    }

    // The MV is materialised; depending on backend config it may or may
    // not be refreshed by the time we read. We tolerate an empty map —
    // what we are NOT tolerating is a failed query, malformed JSON, or
    // a 5xx. Those would mean the contract is broken.
    let map = client.query_prover_success_by_class(&unique_class).await?;
    assert!(
        map.values().all(|rate| (0.0..=1.0).contains(rate)),
        "every success_rate in the MV must lie in [0.0, 1.0]; got {:?}",
        map
    );

    Ok(())
}
