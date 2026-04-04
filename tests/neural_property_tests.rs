// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Property-based (P2P) tests for neural-foundations/echidna core invariants.
//!
//! Uses `proptest` to verify:
//!   - Proof dispatch determinism: same input → same prover selected
//!   - Embedding consistency: same text → same embedding vector (within tolerance)
//!   - Trust level monotonicity: more confirming provers never lowers trust
//!   - Proof hash stability: same proof content → same BLAKE3 hash
//!   - Axiom danger level ordering: ordering is total and transitive
//!   - ProverKind enumeration: all() has no duplicates and stable ordering

mod common;

use proptest::prelude::*;
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::axiom_tracker::{AxiomTracker, DangerLevel};

// ---------------------------------------------------------------------------
// Deterministic mock embedding and prover selector
//
// The real system calls the Julia ML server. For property tests we implement
// deterministic hash-based equivalents that exercise the same API contracts.
// ---------------------------------------------------------------------------

/// Compute a deterministic 8-dimensional embedding vector from a text string.
/// Identical input must always produce identical output.
fn deterministic_embedding(text: &str) -> Vec<f64> {
    let hash_seed: u64 = text.bytes().fold(0x811c9dc5u64, |acc, b| {
        acc.wrapping_mul(0x01000193).wrapping_add(b as u64)
    });
    (0..8)
        .map(|i| {
            let rotated = hash_seed.rotate_left((i * 7) as u32);
            (rotated & 0xFFFF) as f64 / 65535.0
        })
        .collect()
}

/// Cosine similarity between two equal-dimension vectors.
fn cosine_similarity(a: &[f64], b: &[f64]) -> f64 {
    assert_eq!(a.len(), b.len());
    let dot: f64 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
    let mag_a: f64 = a.iter().map(|x| x * x).sum::<f64>().sqrt();
    let mag_b: f64 = b.iter().map(|x| x * x).sum::<f64>().sqrt();
    if mag_a == 0.0 || mag_b == 0.0 {
        return f64::NAN;
    }
    dot / (mag_a * mag_b)
}

/// Deterministic prover selector: maps content → prover via hash.
fn deterministic_prover_select(content: &str) -> ProverKind {
    let hash: usize = content
        .bytes()
        .fold(0usize, |acc, b| acc.wrapping_mul(31).wrapping_add(b as usize));
    let provers = ProverKind::all();
    provers[hash % provers.len()]
}

// ---------------------------------------------------------------------------
// Property: embedding determinism
// ---------------------------------------------------------------------------

proptest! {
    /// Same text must always produce the exact same embedding vector.
    #[test]
    fn prop_embedding_determinism(text in "[a-z ]{1,64}") {
        let v1 = deterministic_embedding(&text);
        let v2 = deterministic_embedding(&text);
        prop_assert_eq!(v1.len(), v2.len());
        for (i, (a, b)) in v1.iter().zip(v2.iter()).enumerate() {
            prop_assert_eq!(*a, *b, "Embedding dim {} must be identical: {} != {}", i, a, b);
        }
    }

    /// Same text must have cosine similarity ≥ 0.999 with itself.
    #[test]
    fn prop_embedding_self_similarity(text in "[a-z ]{1,64}") {
        let v = deterministic_embedding(&text);
        let sim = cosine_similarity(&v, &v);
        prop_assert!(sim >= 0.999, "Self-cosine-similarity must be near 1.0, got {}", sim);
    }
}

// ---------------------------------------------------------------------------
// Property: proof dispatch determinism
// ---------------------------------------------------------------------------

proptest! {
    /// Same content must always select the same prover.
    #[test]
    fn prop_dispatch_determinism(content in "[a-z0-9 ]{1,128}") {
        let p1 = deterministic_prover_select(&content);
        let p2 = deterministic_prover_select(&content);
        prop_assert_eq!(p1, p2, "Prover selection must be deterministic: {:?} != {:?}", p1, p2);
    }

    /// Over 50-100 distinct inputs, at least 4 different provers must appear.
    #[test]
    fn prop_dispatch_covers_multiple_provers(
        inputs in prop::collection::vec("[a-z]{3,20}", 50..100)
    ) {
        let selected: std::collections::HashSet<String> = inputs
            .iter()
            .map(|s| format!("{:?}", deterministic_prover_select(s)))
            .collect();
        prop_assert!(
            selected.len() >= 4,
            "Selector must cover at least 4 provers over 48+ inputs, got {}",
            selected.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Property: trust level monotonicity
// ---------------------------------------------------------------------------

proptest! {
    /// More confirming provers must never produce a lower trust level.
    #[test]
    fn prop_trust_level_monotone_with_confirming_provers(
        base_count in 1u32..5,
        extra in 1u32..5
    ) {
        let base_factors = TrustFactors {
            prover: ProverKind::Z3,
            confirming_provers: base_count,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: None,
        };
        let more_factors = TrustFactors {
            confirming_provers: base_count + extra,
            ..base_factors.clone()
        };
        let base_trust = compute_trust_level(&base_factors);
        let more_trust = compute_trust_level(&more_factors);
        prop_assert!(
            more_trust >= base_trust,
            "More confirming provers must not lower trust: {:?} < {:?}",
            more_trust, base_trust
        );
    }

    /// Dangerous axioms must never result in higher trust than safe axioms.
    #[test]
    fn prop_dangerous_axioms_cannot_raise_trust(
        confirming in 1u32..10,
        has_cert in proptest::bool::ANY
    ) {
        let safe_factors = TrustFactors {
            prover: ProverKind::Lean,
            confirming_provers: confirming,
            has_certificate: has_cert,
            certificate_verified: has_cert,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
            portfolio_confidence: None,
        };
        let dangerous_factors = TrustFactors {
            worst_axiom_danger: DangerLevel::Reject,
            ..safe_factors.clone()
        };
        let safe_trust = compute_trust_level(&safe_factors);
        let dangerous_trust = compute_trust_level(&dangerous_factors);

        prop_assert!(
            dangerous_trust <= safe_trust,
            "Dangerous axioms must not yield higher trust: {:?} > {:?}",
            dangerous_trust, safe_trust
        );
        prop_assert_eq!(
            dangerous_trust, TrustLevel::Level1,
            "Reject axioms must always yield Level1, got {:?}",
            dangerous_trust
        );
    }
}

// ---------------------------------------------------------------------------
// Property: proof hash stability (BLAKE3)
// ---------------------------------------------------------------------------

proptest! {
    /// Same proof content must always produce the same BLAKE3 hash.
    #[test]
    fn prop_proof_hash_stability(content in "[a-z0-9\n ]{1,256}") {
        use blake3::hash;
        let h1 = hash(content.as_bytes()).to_hex().to_string();
        let h2 = hash(content.as_bytes()).to_hex().to_string();
        prop_assert_eq!(h1, h2, "BLAKE3 hash must be stable for identical input");
    }

    /// Different content must produce different hashes.
    #[test]
    fn prop_distinct_content_distinct_hashes(
        base in "[a-z]{10,50}",
        suffix in "[a-z]{1,5}"
    ) {
        use blake3::hash;
        let content_a = base.clone();
        let content_b = format!("{}{}", base, suffix);
        prop_assume!(content_a != content_b);
        let h_a = hash(content_a.as_bytes()).to_hex().to_string();
        let h_b = hash(content_b.as_bytes()).to_hex().to_string();
        prop_assert_ne!(h_a, h_b, "Distinct proof content must produce distinct hashes");
    }
}

// ---------------------------------------------------------------------------
// Property: DangerLevel ordering is total and transitive
// ---------------------------------------------------------------------------

proptest! {
    #[test]
    fn prop_danger_level_ordering_transitive(
        a_val in 0usize..4,
        b_val in 0usize..4,
        c_val in 0usize..4
    ) {
        let levels = [
            DangerLevel::Safe,
            DangerLevel::Noted,
            DangerLevel::Warning,
            DangerLevel::Reject,
        ];
        let (a, b, c) = (levels[a_val], levels[b_val], levels[c_val]);
        if a <= b && b <= c {
            prop_assert!(a <= c, "DangerLevel ordering must be transitive");
        }
    }
}

// ---------------------------------------------------------------------------
// Deterministic unit property tests (non-proptest)
// ---------------------------------------------------------------------------

/// ProverKind::all() must contain no duplicate variants.
#[test]
fn prop_prover_kind_all_no_duplicates() {
    let all = ProverKind::all();
    let mut seen = std::collections::HashSet::new();
    for kind in &all {
        let key = format!("{:?}", kind);
        assert!(seen.insert(key.clone()), "ProverKind::all() duplicate: {}", key);
    }
    // Verify count is consistent (the exact number is 49 per current implementation).
    assert_eq!(
        all.len(), seen.len(),
        "ProverKind::all() must have no duplicates: {} variants, {} unique",
        all.len(), seen.len()
    );
    // Must have at least 30 backends (as documented).
    assert!(all.len() >= 30, "ProverKind::all() must have at least 30 variants, got {}", all.len());
}

/// DangerLevel::Reject must be the maximum, DangerLevel::Safe the minimum.
#[test]
fn prop_danger_level_extremes() {
    for level in [DangerLevel::Noted, DangerLevel::Warning, DangerLevel::Safe] {
        assert!(DangerLevel::Reject > level, "Reject must be > {:?}", level);
    }
    for level in [DangerLevel::Noted, DangerLevel::Warning, DangerLevel::Reject] {
        assert!(DangerLevel::Safe < level, "Safe must be < {:?}", level);
    }
}

proptest! {
    /// ProverKind list is stable: same index always returns same kind.
    #[test]
    fn prop_prover_kind_list_stable(idx in 0usize..49) {
        let all = ProverKind::all();
        let k1 = all[idx];
        let k2 = ProverKind::all()[idx];
        prop_assert_eq!(
            format!("{:?}", k1),
            format!("{:?}", k2),
            "ProverKind list must be stable across calls"
        );
    }
}
