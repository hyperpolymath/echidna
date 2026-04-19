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
//
// Wave-2+: adds per-backend canonical micro-goals (fed through
// `ProverBackend::verify_proof`) once the fixtures land under
// `tests/live_goals/`.  See ~/Desktop/ECHIDNA-L3-LIVE-PROVER-CI-PROMPT.md for
// the continuation plan.

#![cfg(feature = "live-provers")]

use std::path::PathBuf;

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};

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
        args: vec![],
        timeout: 30,
        neural_enabled: false,
    }
}

/// Construct a live backend of the given kind.  Returns `None` when the
/// binary is absent on PATH (auto-skip signal to callers).
fn try_live_backend(
    kind: ProverKind,
    exe: &str,
) -> Option<Box<dyn ProverBackend>> {
    let _resolved = binary_on_path(exe)?;
    let config = live_config(exe);
    ProverFactory::create(kind, config).ok()
}

/// Version-check helper: instantiates the backend, calls `version()`, and
/// asserts the call succeeded and returned *something*.  A backend that
/// compiles but cannot speak to its binary returns `Err`, which we surface
/// as a test failure — that is exactly the mock-vs-reality gap this suite
/// exists to catch.
async fn assert_version_reachable(kind: ProverKind, exe: &str) {
    let Some(backend) = try_live_backend(kind, exe) else {
        eprintln!("SKIP: {} not on PATH (searched for `{}`)", kind_label(kind), exe);
        return;
    };
    match backend.version().await {
        Ok(v) => {
            assert!(
                !v.trim().is_empty(),
                "{} version() returned empty string — subprocess is wired but produced no output",
                kind_label(kind),
            );
            eprintln!("OK: {} reported version = {:?}", kind_label(kind), v);
        }
        Err(e) => {
            panic!(
                "{} live version() failed: {}.  Binary found on PATH but the \
                 backend's subprocess wiring did not produce a usable version \
                 string.  This is exactly the class of bug mock-only CI hides.",
                kind_label(kind),
                e,
            );
        }
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
