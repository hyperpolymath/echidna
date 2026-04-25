// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA — Live-Prover Verify Roundtrip Test Suite
//
// The Phase 3 backend fix (commits `ac209ee`, `b1258da`, `940e940`) reworked
// every lossy `verify_proof` so it prefers the original source over the
// Term-IR round-trip.  The 625-test unit suite stubs solver binaries, so a
// regression in that fix would not be caught there.  This suite runs the
// real `prove_command` pipeline (parse_file → verify_proof) against
// per-prover fixtures in `tests/live_goals/` and asserts both a positive
// verdict on a valid proof and a negative verdict on a broken one.
//
// Auto-skip semantics match `tests/live_prover_suite.rs`: when the binary
// isn't on PATH the test prints SKIP and returns Ok so developers without
// every prover installed don't see spurious failures.  CI
// (.github/workflows/live-provers.yml) enables the feature per tier with
// the matching binary provisioned.
//
// Covered (apt-installable MVP): Z3, CVC5, Coq, Agda, Metamath, SPASS.
// Uncovered (need manual install, exercised inside Containerfile.mcp):
// Lean 4, Isabelle, F*, Mizar.

#![cfg(feature = "live-provers")]

use std::path::{Path, PathBuf};

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};

/// Locate a binary on PATH.  Returns `None` when absent (auto-skip signal).
fn binary_on_path(name: &str) -> Option<PathBuf> {
    which::which(name).ok()
}

/// `ProverConfig` pointing at the real binary with a tight timeout.
/// The short timeout keeps a misbehaving backend from stalling the matrix.
fn live_config(executable: &Path) -> ProverConfig {
    ProverConfig {
        executable: executable.to_path_buf(),
        library_paths: vec![],
        args: vec![],
        timeout: 30,
        neural_enabled: false,
    }
}

/// Instantiate a live backend.  Returns `None` when the binary is absent.
fn try_live_backend(kind: ProverKind, exe: &str) -> Option<Box<dyn ProverBackend>> {
    let resolved = binary_on_path(exe)?;
    let config = live_config(&resolved);
    ProverFactory::create(kind, config).ok()
}

/// Fixture path relative to the crate root.
fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("live_goals")
        .join(name)
}

/// Run parse_file + verify_proof end-to-end against a fixture.
/// Returns `Ok(verified)`; `None` is caller's signal that the binary is
/// absent.  Any *error* from the pipeline fails the test — the pipeline
/// should produce `Ok(true/false)`, never propagate an error for a
/// well-formed input/invalid-proof distinction.
async fn verify_fixture(
    kind: ProverKind,
    exe: &str,
    fixture_name: &str,
) -> Option<bool> {
    let backend = try_live_backend(kind, exe)?;
    let path = fixture(fixture_name);
    let state = backend
        .parse_file(path.clone())
        .await
        .unwrap_or_else(|e| panic!("{:?}: parse_file({:?}) failed: {e}", kind, path));
    let verified = backend
        .verify_proof(&state)
        .await
        .unwrap_or_else(|e| panic!("{:?}: verify_proof({:?}) failed: {e}", kind, path));
    Some(verified)
}

/// One positive + one negative assertion in the shape every MVP prover
/// test uses below.  Skip (returning without panicking) when the binary
/// isn't on PATH.
async fn check_pair(
    kind: ProverKind,
    exe: &str,
    good: &str,
    bad: &str,
) {
    let Some(ok) = verify_fixture(kind, exe, good).await else {
        eprintln!("SKIP: {exe} not on PATH ({good}/{bad})");
        return;
    };
    assert!(
        ok,
        "{kind:?}: expected verified=true for {good}, got false — \
         the source_path stash pattern regressed or the solver rejected the fixture",
    );
    // Negative case is optional: some fixtures for some backends can't be
    // reliably "broken" in a way the solver rejects quickly.  Run only if
    // the fixture exists.
    if fixture(bad).exists() {
        let bad_verdict = verify_fixture(kind, exe, bad)
            .await
            .expect("binary was present for good fixture, must be present for bad");
        assert!(
            !bad_verdict,
            "{kind:?}: expected verified=false for {bad}, got true — \
             the broken fixture unexpectedly type-checks",
        );
    }
}

// ============================================================================
// SMT solvers (shared fixtures — same SMT-LIB works for Z3 and CVC5)
// ============================================================================

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_z3() {
    check_pair(ProverKind::Z3, "z3", "tautology.smt2", "contradiction.smt2").await;
}

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_cvc5() {
    check_pair(ProverKind::CVC5, "cvc5", "tautology.smt2", "contradiction.smt2").await;
}

// ============================================================================
// Interactive proof assistants
// ============================================================================

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_coq() {
    check_pair(ProverKind::Coq, "coqc", "identity.v", "broken.v").await;
}

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_agda() {
    check_pair(ProverKind::Agda, "agda", "Identity.agda", "Broken.agda").await;
}

// ============================================================================
// Specialised
// ============================================================================

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_metamath() {
    // Metamath's negative case (a deliberately broken .mm) would need a
    // non-trivial database to construct.  Positive-only for now — the
    // CLI shells out to `metamath; verify proof *` and only accepts the
    // "All proofs verified" banner.
    check_pair(ProverKind::Metamath, "metamath", "trivial.mm", "__no_bad_fixture__").await;
}

// ============================================================================
// First-order ATP
// ============================================================================

#[tokio::test(flavor = "multi_thread")]
async fn verify_roundtrip_spass() {
    // SPASS binary installs as /usr/bin/SPASS (uppercase) on Debian-derived
    // distros.  `which` is case-sensitive, so try both.
    let exe = if binary_on_path("SPASS").is_some() {
        "SPASS"
    } else {
        "spass"
    };
    check_pair(ProverKind::SPASS, exe, "trivial.dfg", "__no_bad_fixture__").await;
}
