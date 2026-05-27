// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Integration test: mock HTTP server proves the GNN wire format works and
//! that the 5 key backends (rocq, lean, agda, isabelle, z3) consume
//! `/gnn/rank` and prepend model-derived apply tactics.
//!
//! No Julia installation needed — the mock server is an in-process axum
//! server bound to a random port.  Run with:
//!
//!   cargo test --test gnn_augment_integration

use axum::{
    extract::Json as ExtractJson,
    response::Json,
    routing::{get, post},
    Router,
};
use echidna::{
    core::{Goal, ProofState, Term},
    gnn::client::{GnnClient, GnnConfig},
    provers::{ProverConfig, ProverFactory, ProverKind},
};
use serde_json::{json, Value};
use std::net::SocketAddr;
use tokio::net::TcpListener;

// ─── helpers ────────────────────────────────────────────────────────────────

fn minimal_proof_state() -> ProofState {
    let goal = Goal {
        id: "g0".to_string(),
        target: Term::Const("forall n : nat, n + 0 = n".to_string()),
        hypotheses: vec![],
    };
    ProofState {
        goals: vec![goal],
        context: echidna::core::Context::default(),
        proof_script: vec![],
        metadata: std::collections::HashMap::new(),
    }
}

/// Spawn a mock GNN server on a random port and return its base URL.
///
/// The server responds:
///   GET /gnn/health → gnn_model_loaded: true, vocab_size: 42, model_path: "/fake/path"
///   POST /gnn/rank  → premises ["lemma_foo", "thm_bar", "ax_baz"], scores [0.9, 0.7, 0.5]
async fn spawn_mock_gnn_server() -> String {
    let health_handler = get(|| async {
        Json(json!({
            "status": "ok",
            "gnn_model_loaded": true,
            "model_path": "/fake/path",
            "vocab_size": 42,
            "training_records_received": 0u64,
            "num_gnn_layers": 4,
            "service": "mock",
            "version": "test"
        }))
    });

    let rank_handler = post(|_body: ExtractJson<Value>| async {
        Json(json!({
            "success": true,
            "scores": [0.9_f32, 0.7_f32, 0.5_f32],
            "premise_names": ["lemma_foo", "thm_bar", "ax_baz"],
            "inference_time_ms": 1.0_f32
        }))
    });

    let app = Router::new()
        .route("/gnn/health", health_handler)
        .route("/gnn/rank", rank_handler);

    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr: SocketAddr = listener.local_addr().unwrap();
    let base_url = format!("http://127.0.0.1:{}", addr.port());

    tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });

    // Give the server a moment to accept connections.
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    base_url
}

fn gnn_config(base_url: &str) -> ProverConfig {
    ProverConfig {
        gnn_api_url: Some(base_url.to_string()),
        neural_enabled: true,
        ..ProverConfig::default()
    }
}

// ─── test: GnnClient::health_status() ───────────────────────────────────────

#[tokio::test]
async fn test_health_status_richer_payload() {
    let base_url = spawn_mock_gnn_server().await;
    let client = GnnClient::with_config(GnnConfig {
        api_url: base_url,
        timeout_ms: 5000,
        ..GnnConfig::default()
    });

    let health = client
        .health_status()
        .await
        .expect("health_status should succeed");

    assert!(health.gnn_model_loaded, "mock reports model loaded");
    assert_eq!(health.model_path.as_deref(), Some("/fake/path"));
    assert_eq!(health.vocab_size, 42);
    assert_eq!(health.training_records_received, 0);
    assert_eq!(health.num_gnn_layers, 4);
    assert_eq!(health.service, "mock");
    assert_eq!(health.version, "test");
}

// ─── helper: assert top tactic from suggest_tactics ─────────────────────────

async fn assert_top_tactic_is_apply(kind: ProverKind, prover_name: &str, base_url: &str) {
    let backend = ProverFactory::create(kind, gnn_config(base_url))
        .unwrap_or_else(|e| panic!("Failed to create {:?} backend: {}", kind, e));

    let state = minimal_proof_state();
    let tactics = backend
        .suggest_tactics(&state, 10)
        .await
        .unwrap_or_else(|e| panic!("{} suggest_tactics failed: {}", prover_name, e));

    assert!(
        !tactics.is_empty(),
        "{}: suggest_tactics returned empty list",
        prover_name
    );

    let first = &tactics[0];
    match first {
        echidna::core::Tactic::Custom {
            prover,
            command,
            args,
        } => {
            assert_eq!(
                prover.as_str(),
                prover_name,
                "{}: expected prover name in first tactic",
                prover_name
            );
            assert_eq!(
                command.as_str(),
                "apply",
                "{}: expected 'apply' command in first tactic",
                prover_name
            );
            assert_eq!(
                args,
                &vec!["lemma_foo".to_string()],
                "{}: expected top-ranked premise as argument",
                prover_name
            );
        },
        other => {
            panic!(
                "{}: expected Tactic::Custom(apply lemma_foo) as first tactic, got {:?}",
                prover_name, other
            );
        },
    }
}

// ─── per-backend tests ───────────────────────────────────────────────────────

#[tokio::test]
async fn test_rocq_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Rocq, "rocq", &base_url).await;
}

#[tokio::test]
async fn test_lean_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Lean, "lean", &base_url).await;
}

#[tokio::test]
async fn test_agda_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Agda, "agda", &base_url).await;
}

#[tokio::test]
async fn test_isabelle_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Isabelle, "isabelle", &base_url).await;
}

#[tokio::test]
async fn test_z3_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Z3, "z3", &base_url).await;
}
