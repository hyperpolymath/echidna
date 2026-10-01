// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Integration test: mock HTTP server proves the GNN wire format works and
//! that the 10 GNN-augmented Tier-1 backends (rocq, lean, agda, isabelle, z3
//! from the S5 pilot, plus idris2, fstar, cvc5, vampire, dafny extending it)
//! consume `/gnn/rank` and prepend model-derived apply tactics.
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

#[tokio::test]
async fn test_idris2_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Idris2, "idris2", &base_url).await;
}

#[tokio::test]
async fn test_fstar_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::FStar, "fstar", &base_url).await;
}

#[tokio::test]
async fn test_cvc5_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CVC5, "cvc5", &base_url).await;
}

#[tokio::test]
async fn test_vampire_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Vampire, "vampire", &base_url).await;
}

#[tokio::test]
async fn test_dafny_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Dafny, "dafny", &base_url).await;
}

// ─── Tier-1 finisher: altergo + eprover ─────────────────────────────────────

#[tokio::test]
async fn test_altergo_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::AltErgo, "altergo", &base_url).await;
}

#[tokio::test]
async fn test_eprover_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::EProver, "eprover", &base_url).await;
}

// ─── Tier-2 sweep: 33 backends ───────────────────────────────────────────────

#[tokio::test]
async fn test_acl2_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ACL2, "acl2", &base_url).await;
}

#[tokio::test]
async fn test_agsyhol_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::AgsyHOL, "agsyhol", &base_url).await;
}

#[tokio::test]
async fn test_aprove_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::AProVE, "aprove", &base_url).await;
}

#[tokio::test]
async fn test_athena_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Athena, "athena", &base_url).await;
}

#[tokio::test]
async fn test_cameleer_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Cameleer, "cameleer", &base_url).await;
}

#[tokio::test]
async fn test_cbmc_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CBMC, "cbmc", &base_url).await;
}

#[tokio::test]
async fn test_chuffed_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Chuffed, "chuffed", &base_url).await;
}

#[tokio::test]
async fn test_csi_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CSI, "csi", &base_url).await;
}

#[tokio::test]
async fn test_dreal_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::DReal, "dreal", &base_url).await;
}

#[tokio::test]
async fn test_glpk_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::GLPK, "glpk", &base_url).await;
}

#[tokio::test]
async fn test_hol4_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::HOL4, "HOL4", &base_url).await;
}

#[tokio::test]
async fn test_hol_light_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::HOLLight, "hol_light", &base_url).await;
}

#[tokio::test]
async fn test_imandra_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Imandra, "imandra", &base_url).await;
}

#[tokio::test]
async fn test_iprover_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::IProver, "iprover", &base_url).await;
}

#[tokio::test]
async fn test_key_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::KeY, "key", &base_url).await;
}

#[tokio::test]
async fn test_lash_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Lash, "lash", &base_url).await;
}

#[tokio::test]
async fn test_leo3_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Leo3, "leo3", &base_url).await;
}

#[tokio::test]
async fn test_metamath_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Metamath, "metamath", &base_url).await;
}

#[tokio::test]
async fn test_metitarski_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MetiTarski, "metitarski", &base_url).await;
}

#[tokio::test]
async fn test_minizinc_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MiniZinc, "minizinc", &base_url).await;
}

#[tokio::test]
async fn test_minlog_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Minlog, "minlog", &base_url).await;
}

#[tokio::test]
async fn test_mizar_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Mizar, "mizar", &base_url).await;
}

#[tokio::test]
async fn test_nuprl_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Nuprl, "nuprl", &base_url).await;
}

#[tokio::test]
async fn test_ortools_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ORTools, "ortools", &base_url).await;
}

#[tokio::test]
async fn test_princess_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Princess, "princess", &base_url).await;
}

#[tokio::test]
async fn test_pvs_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::PVS, "PVS", &base_url).await;
}

#[tokio::test]
async fn test_satallax_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Satallax, "satallax", &base_url).await;
}

#[tokio::test]
async fn test_scip_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::SCIP, "scip", &base_url).await;
}

#[tokio::test]
async fn test_spass_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::SPASS, "spass", &base_url).await;
}

#[tokio::test]
async fn test_tlaps_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::TLAPS, "tlaps", &base_url).await;
}

#[tokio::test]
async fn test_twee_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Twee, "twee", &base_url).await;
}

#[tokio::test]
async fn test_twelf_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Twelf, "twelf", &base_url).await;
}

#[tokio::test]
async fn test_why3_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Why3, "why3", &base_url).await;
}

// ─── Tier-3 / niche sweep: full ProverKind coverage ─────────────────────────

#[tokio::test]
async fn test_abc_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ABC, "abc", &base_url).await;
}

#[tokio::test]
async fn test_acl2s_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ACL2s, "acl2s", &base_url).await;
}

#[tokio::test]
async fn test_alloy_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Alloy, "alloy", &base_url).await;
}

#[tokio::test]
async fn test_arend_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Arend, "arend", &base_url).await;
}

#[tokio::test]
async fn test_boogie_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Boogie, "boogie", &base_url).await;
}

#[tokio::test]
async fn test_cadical_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CaDiCaL, "cadical", &base_url).await;
}

#[tokio::test]
async fn test_coq_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Coq, "coq", &base_url).await;
}

#[tokio::test]
async fn test_cryptoverif_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CryptoVerif, "cryptoverif", &base_url).await;
}

#[tokio::test]
async fn test_cubical_agda_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::CubicalAgda, "cubical_agda", &base_url).await;
}

#[tokio::test]
async fn test_dedukti_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Dedukti, "dedukti", &base_url).await;
}

#[tokio::test]
async fn test_elk_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ELK, "elk", &base_url).await;
}

#[tokio::test]
async fn test_faial_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Faial, "faial", &base_url).await;
}

#[tokio::test]
async fn test_framac_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::FramaC, "framac", &base_url).await;
}

#[tokio::test]
async fn test_gnatprove_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::GNATprove, "gnatprove", &base_url).await;
}

#[tokio::test]
async fn test_gpuverify_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::GPUVerify, "gpuverify", &base_url).await;
}

#[tokio::test]
async fn test_hp_ecosystem_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::TypeLL, "hp_ecosystem", &base_url).await;
}

#[tokio::test]
async fn test_ileancop_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::IleanCoP, "ileancop", &base_url).await;
}

#[tokio::test]
async fn test_isabelle_zf_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::IsabelleZF, "isabelle_zf", &base_url).await;
}

#[tokio::test]
async fn test_kissat_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Kissat, "kissat", &base_url).await;
}

#[tokio::test]
async fn test_konclude_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Konclude, "konclude", &base_url).await;
}

#[tokio::test]
async fn test_lambda_prolog_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::LambdaProlog, "lambda_prolog", &base_url).await;
}

#[tokio::test]
async fn test_lean3_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Lean3, "lean3", &base_url).await;
}

#[tokio::test]
async fn test_liquid_haskell_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::LiquidHaskell, "liquid-haskell", &base_url).await;
}

#[tokio::test]
async fn test_matita_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Matita, "matita", &base_url).await;
}

#[tokio::test]
async fn test_mercury_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Mercury, "mercury", &base_url).await;
}

#[tokio::test]
async fn test_mettel2_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MetTeL2, "mettel2", &base_url).await;
}

#[tokio::test]
async fn test_minisat_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MiniSat, "minisat", &base_url).await;
}

#[tokio::test]
async fn test_mizar_ar_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MizAR, "mizar_ar", &base_url).await;
}

#[tokio::test]
async fn test_mleancop_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::MleanCoP, "mleancop", &base_url).await;
}

#[tokio::test]
async fn test_nanocop_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::NanoCoP, "nanocop", &base_url).await;
}

#[tokio::test]
async fn test_naproche_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Naproche, "naproche", &base_url).await;
}

#[tokio::test]
async fn test_nitpick_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Nitpick, "nitpick", &base_url).await;
}

#[tokio::test]
async fn test_nunchaku_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Nunchaku, "nunchaku", &base_url).await;
}

#[tokio::test]
async fn test_nusmv_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::NuSMV, "nusmv", &base_url).await;
}

#[tokio::test]
async fn test_opensmt_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::OpenSmt, "opensmt", &base_url).await;
}

#[tokio::test]
async fn test_prism_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Prism, "prism", &base_url).await;
}

#[tokio::test]
async fn test_prob_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ProB, "prob", &base_url).await;
}

#[tokio::test]
async fn test_prover9_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Prover9, "prover9", &base_url).await;
}

#[tokio::test]
async fn test_proverif_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::ProVerif, "proverif", &base_url).await;
}

#[tokio::test]
async fn test_qepcad_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Qepcad, "qepcad", &base_url).await;
}

#[tokio::test]
async fn test_redlog_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Redlog, "redlog", &base_url).await;
}

#[tokio::test]
async fn test_seahorn_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::SeaHorn, "seahorn", &base_url).await;
}

#[tokio::test]
async fn test_smtrat_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::SmtRat, "smtrat", &base_url).await;
}

#[tokio::test]
async fn test_spin_checker_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::SPIN, "spin", &base_url).await;
}

#[tokio::test]
async fn test_stainless_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Stainless, "stainless", &base_url).await;
}

#[tokio::test]
async fn test_storm_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Storm, "storm", &base_url).await;
}

#[tokio::test]
async fn test_tamarin_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Tamarin, "tamarin", &base_url).await;
}

#[tokio::test]
async fn test_tlc_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::TLC, "tlc", &base_url).await;
}

#[tokio::test]
async fn test_typed_wasm_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::TypedWasm, "typed_wasm", &base_url).await;
}

#[tokio::test]
async fn test_uppaal_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::UPPAAL, "uppaal", &base_url).await;
}

#[tokio::test]
async fn test_uppaal_stratego_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::UppaalStratego, "uppaal_stratego", &base_url).await;
}

#[tokio::test]
async fn test_viper_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Viper, "viper", &base_url).await;
}

#[tokio::test]
async fn test_zipperposition_gnn_wires_top_premise() {
    let base_url = spawn_mock_gnn_server().await;
    assert_top_tactic_is_apply(ProverKind::Zipperposition, "zipperposition", &base_url).await;
}
