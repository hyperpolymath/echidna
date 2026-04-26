// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA — Live-Prover Test Suite
//
// Exercises real prover binaries against canonical micro-goals.  Complements
// the mock-based `sanity_suite.rs` / `e2e_prover_test.rs` suites.
//
// Gated by the `live-provers` Cargo feature so a developer without the 48
// prover binaries installed does not see spurious failures.  In CI the
// .github/workflows/live-provers.yml workflow enables the feature and the
// per-tier matrix jobs each provision the single binary they test.
//
// Skip semantics: every test first runs `which <binary>` via the `which`
// crate; if the binary is absent the test is *skipped* (returns Ok) rather
// than failing.  This lets the same suite run locally (sparse tool install)
// and in CI (per-job single binary) without branching.
//
// Wave-1 (this file): Tier-1 backends — version-check smoke tests.  Proves
// the subprocess wiring is real, not mocked, and that the binary responds.
// L3 hygiene: emits VeriSimDB records for each test outcome via
// `record_proof_attempt`, feeding the learning loop.
//
// Wave-2+: adds per-backend canonical micro-goals (fed through
// `ProverBackend::verify_proof`) once the fixtures land under
// `tests/live_goals/`.  See ~/Desktop/ECHIDNA-L3-LIVE-PROVER-CI-PROMPT.md for
// the continuation plan.

#![cfg(feature = "live-provers")]

use std::path::PathBuf;
use std::time::Instant;

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use echidna::verisim_bridge::{ProofAttempt, VeriSimDBClient};

/// Check if a binary exists on PATH.  Returns the resolved absolute path
/// for diagnostics, or None when the binary is absent.
fn binary_on_path(name: &str) -> Option<PathBuf> {
    which::which(name).ok()
}

/// Build a default `ProverConfig` for live tests.  Uses a short timeout so
/// that a misbehaving backend cannot stall the matrix.
fn live_config(executable: &str) -> ProverConfig {
    ProverConfig {
        executable: PathBuf::from(executable),
        library_paths: vec![],
        args: vec![],
        timeout: 30,
        neural_enabled: false,
        gnn_api_url: None,
    }
}

/// Construct a live backend of the given kind.  Returns `None` when the
/// binary is absent on PATH (auto-skip signal to callers).
fn try_live_backend(kind: ProverKind, exe: &str) -> Option<Box<dyn ProverBackend>> {
    let _resolved = binary_on_path(exe)?;
    let config = live_config(exe);
    ProverFactory::create(kind, config).ok()
}

/// Emit a VeriSimDB proof-attempt record for the test outcome.
/// Non-fatal: if VeriSimDB is unreachable, log a warning and continue —
/// never fail the test. This feeds the learning loop in hypatia's rule H3.
async fn emit_live_result(kind: ProverKind, exe: &str, version: Option<&str>, elapsed_ms: u64) {
    let outcome = if version.is_some() { "success" } else { "failure" };
    let error_msg = if version.is_none() {
        Some(format!("{} version() returned no version string", kind_label(kind)))
    } else {
        None
    };

    let attempt = ProofAttempt {
        attempt_id: format!(
            "live-version-{}-{}",
            exe.replace(['/', '\\'], "_"),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis()
        ),
        obligation_id: format!("live-version-check-{}", exe),
        repo: "hyperpolymath/echidna".to_string(),
        file: "tests/live_prover_suite.rs".to_string(),
        claim: format!("Prover {} is reachable and can report version", kind_label(kind)),
        obligation_class: "system_integration".to_string(),
        prover_used: format!("{:?}", kind).to_lowercase(),
        outcome: outcome.to_string(),
        duration_ms: elapsed_ms,
        confidence: if version.is_some() { 1.0 } else { 0.0 },
        parent_attempt_id: None,
        strategy_tag: "live_version_check".to_string(),
        started_at: chrono::Utc::now()
            .checked_sub_signed(chrono::Duration::milliseconds(elapsed_ms as i64))
            .unwrap_or_else(chrono::Utc::now)
            .to_rfc3339(),
        completed_at: chrono::Utc::now().to_rfc3339(),
        prover_output: version.unwrap_or("").to_string(),
        error_message: error_msg,
    };

    // Resolve VeriSimDB URL from VERISIMDB_URL env var or default to localhost:7700
    let verisimdb_url = std::env::var("VERISIMDB_URL")
        .unwrap_or_else(|_| "http://localhost:7700".to_string());
    let client = VeriSimDBClient::new(&verisimdb_url);
    if let Err(e) = client.record_proof_attempt(&attempt).await {
        eprintln!(
            "VeriSimDB emit skipped for {}: {} (VeriSimDB not running?)",
            kind_label(kind),
            e
        );
    }
}

/// Version-check helper: instantiates the backend, calls `version()`, and
/// asserts the call succeeded and returned *something*.  A backend that
/// compiles but cannot speak to its binary returns `Err`, which we surface
/// as a test failure — that is exactly the mock-vs-reality gap this suite
/// exists to catch.  Also emits a VeriSimDB record on completion.
async fn assert_version_reachable(kind: ProverKind, exe: &str) {
    let Some(backend) = try_live_backend(kind, exe) else {
        eprintln!(
            "SKIP: {} not on PATH (searched for `{}`)",
            kind_label(kind),
            exe
        );
        return;
    };

    let start_time = Instant::now();
    match backend.version().await {
        Ok(v) => {
            let elapsed_ms = start_time.elapsed().as_millis() as u64;
            assert!(
                !v.trim().is_empty(),
                "{} version() returned empty string — subprocess is wired but produced no output",
                kind_label(kind),
            );
            eprintln!("OK: {} reported version = {:?}", kind_label(kind), v);
            emit_live_result(kind, exe, Some(&v), elapsed_ms).await;
        },
        Err(e) => {
            let elapsed_ms = start_time.elapsed().as_millis() as u64;
            eprintln!("FAIL: {} version() failed: {}", kind_label(kind), e);
            emit_live_result(kind, exe, None, elapsed_ms).await;
            panic!(
                "{} live version() failed: {}.  Binary found on PATH but the \
                 backend's subprocess wiring did not produce a usable version \
                 string.  This is exactly the class of bug mock-only CI hides.",
                kind_label(kind),
                e,
            );
        },
    }
}

fn kind_label(kind: ProverKind) -> &'static str {
    match kind {
        ProverKind::Z3 => "Z3",
        ProverKind::CVC5 => "CVC5",
        ProverKind::AltErgo => "Alt-Ergo",
        ProverKind::Vampire => "Vampire",
        ProverKind::EProver => "EProver",
        ProverKind::SPASS => "SPASS",
        ProverKind::GLPK => "GLPK",
        ProverKind::MiniZinc => "MiniZinc",
        ProverKind::Chuffed => "Chuffed",
        ProverKind::Coq => "Coq",
        ProverKind::Agda => "Agda",
        ProverKind::Idris2 => "Idris2",
        ProverKind::Lean => "Lean",
        ProverKind::Isabelle => "Isabelle",
        ProverKind::Why3 => "Why3",
        ProverKind::Dafny => "Dafny",
        ProverKind::FStar => "F*",
        ProverKind::TLAPS => "TLAPS",
        ProverKind::Tamarin => "Tamarin",
        ProverKind::ProVerif => "ProVerif",
        ProverKind::Metamath => "Metamath",
        ProverKind::Twelf => "Twelf",
        ProverKind::ORTools => "OR-Tools",
        ProverKind::HOL4 => "HOL4",
        ProverKind::ACL2 => "ACL2",
        ProverKind::SCIP => "SCIP",
        ProverKind::Imandra => "Imandra",
        _ => "<other>",
    }
}

// ==========================================================================
// Tier 1 — trivial: runs on every PR
// ==========================================================================

#[tokio::test]
async fn live_z3_version() {
    assert_version_reachable(ProverKind::Z3, "z3").await;
}

#[tokio::test]
async fn live_cvc5_version() {
    assert_version_reachable(ProverKind::CVC5, "cvc5").await;
}

#[tokio::test]
async fn live_alt_ergo_version() {
    assert_version_reachable(ProverKind::AltErgo, "alt-ergo").await;
}

#[tokio::test]
async fn live_vampire_version() {
    assert_version_reachable(ProverKind::Vampire, "vampire").await;
}

#[tokio::test]
async fn live_eprover_version() {
    assert_version_reachable(ProverKind::EProver, "eprover").await;
}

#[tokio::test]
async fn live_spass_version() {
    assert_version_reachable(ProverKind::SPASS, "SPASS").await;
}

#[tokio::test]
async fn live_glpk_version() {
    assert_version_reachable(ProverKind::GLPK, "glpsol").await;
}

#[tokio::test]
async fn live_minizinc_version() {
    assert_version_reachable(ProverKind::MiniZinc, "minizinc").await;
}

#[tokio::test]
async fn live_chuffed_version() {
    assert_version_reachable(ProverKind::Chuffed, "fzn-chuffed").await;
}

// ==========================================================================
// Tier 2 — build-from-source: runs nightly
// ==========================================================================

#[tokio::test]
async fn live_coq_version() {
    assert_version_reachable(ProverKind::Coq, "coqc").await;
}

#[tokio::test]
async fn live_agda_version() {
    assert_version_reachable(ProverKind::Agda, "agda").await;
}

#[tokio::test]
async fn live_idris2_version() {
    assert_version_reachable(ProverKind::Idris2, "idris2").await;
}

#[tokio::test]
async fn live_lean4_version() {
    assert_version_reachable(ProverKind::Lean, "lean").await;
}

#[tokio::test]
async fn live_isabelle_version() {
    assert_version_reachable(ProverKind::Isabelle, "isabelle").await;
}

#[tokio::test]
async fn live_why3_version() {
    assert_version_reachable(ProverKind::Why3, "why3").await;
}

#[tokio::test]
async fn live_dafny_version() {
    assert_version_reachable(ProverKind::Dafny, "dafny").await;
}

#[tokio::test]
async fn live_fstar_version() {
    // Canonical binary name is `fstar.exe` (per ProverKind::FStar executable()
    // in src/rust/provers/mod.rs — F* uses the `.exe` suffix even on Linux).
    assert_version_reachable(ProverKind::FStar, "fstar.exe").await;
}

#[tokio::test]
async fn live_tlaps_version() {
    // TLA+ Proof System's prover is `tlapm` (per provers/mod.rs).
    assert_version_reachable(ProverKind::TLAPS, "tlapm").await;
}

// ==========================================================================
// Tier 3 — weekly.  Upstream-tarball or heavier-build provers.  Most of
// these SKIP locally and in PR CI; the weekly tier3 matrix in
// live-provers.yml provisions each binary in its own job before running
// `cargo test ... <backend>`, so only the matching test runs per job.
// ==========================================================================

#[tokio::test]
async fn live_tamarin_version() {
    assert_version_reachable(ProverKind::Tamarin, "tamarin-prover").await;
}

#[tokio::test]
async fn live_proverif_version() {
    assert_version_reachable(ProverKind::ProVerif, "proverif").await;
}

#[tokio::test]
async fn live_metamath_version() {
    assert_version_reachable(ProverKind::Metamath, "metamath").await;
}

#[tokio::test]
async fn live_twelf_version() {
    // Twelf's CLI entry is `twelf-server` per provers/mod.rs.
    assert_version_reachable(ProverKind::Twelf, "twelf-server").await;
}

#[tokio::test]
async fn live_ortools_version() {
    // Echidna's ORTools backend invokes `ortools_solve` (wrapper around the
    // OR-Tools C++ solve CLI).  Provisioned via upstream tarball.
    assert_version_reachable(ProverKind::ORTools, "ortools_solve").await;
}

#[tokio::test]
async fn live_hol4_version() {
    // HOL4 requires Poly/ML + a tree build; provisioning is deferred to
    // Containerfile.  Test SKIPs on runners without `hol` on PATH.
    assert_version_reachable(ProverKind::HOL4, "hol").await;
}

#[tokio::test]
async fn live_acl2_version() {
    // ACL2 requires a Common Lisp image; provisioning deferred to Containerfile.
    assert_version_reachable(ProverKind::ACL2, "acl2").await;
}

#[tokio::test]
async fn live_scip_version() {
    // SCIP requires a cmake build of SCIP Optimization Suite; deferred to
    // Containerfile.  Test SKIPs until provisioned.
    assert_version_reachable(ProverKind::SCIP, "scip").await;
}

#[tokio::test]
async fn live_imandra_version() {
    // Imandra is proprietary; handled via vendor-supplied container where a
    // licence is available.  Test SKIPs on public CI.
    assert_version_reachable(ProverKind::Imandra, "imandra").await;
}

// ==========================================================================
// Tier 4 — quarterly.  GPU verification backends.  Require CUDA SDK or
// OpenCL runtime; provisioned via Containerfile or developer workstation.
// Tests SKIP when the binary is absent.
// ==========================================================================

#[tokio::test]
async fn live_gpuverify_version() {
    // GPUVerify targets CUDA/OpenCL kernels via Boogie+Z3.
    // Install: https://github.com/mc-imperial/gpuverify
    assert_version_reachable(ProverKind::GPUVerify, "gpuverify").await;
}

#[tokio::test]
async fn live_faial_version() {
    // Faial is a static GPU data-race detector targeting CUDA.
    // Install: https://github.com/elliotttate/faial (or `cargo install faial`)
    assert_version_reachable(ProverKind::Faial, "faial-drf").await;
}
