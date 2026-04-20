// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Routing and dispatch latency benchmarks for ECHIDNA.
//!
//! Measures:
//!   - LLM routing decision latency (deterministic prover selection)
//!   - Axiom scan throughput for various proof sizes
//!   - Trust level computation latency under varying factor combinations
//!   - ProverFactory instantiation cost (amortises cold-start cost)
//!   - Agentic planning throughput (goal queue processing rate)
//!   - BLAKE3 proof hashing throughput at different content sizes
//!
//! Run with: `cargo bench --bench routing_benchmarks`
//! Generates HTML reports in `target/criterion/`

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use echidna::agent::AgentConfig;
use echidna::dispatch::DispatchConfig;
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::axiom_tracker::{AxiomTracker, DangerLevel};
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};

// ============================================================================
// Routing Decision Latency
//
// Measures the time to select a prover from content. In production this
// happens for every incoming proof request before the prover is invoked.
// ============================================================================

/// Benchmark: deterministic prover selection from content hash.
///
/// This is the critical hot path for routing: a proof request arrives,
/// the system must decide which of 48 backends to dispatch to.
fn bench_routing_decision_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("routing_decision_latency");

    let test_contents = [
        ("short_smt", "(assert (= x x))"),
        (
            "medium_lean4",
            "theorem comm (a b : Nat) : a + b = b + a := Nat.add_comm a b",
        ),
        (
            "long_coq",
            "Theorem plus_comm : forall n m : nat, n + m = m + n. \
              Proof. intros n m. induction n as [| n' IHn']. - simpl. rewrite <- plus_n_O. reflexivity. \
              - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity. Qed.",
        ),
    ];

    for (label, content) in test_contents {
        group.bench_with_input(
            BenchmarkId::new("select_prover", label),
            &content,
            |b, content| {
                b.iter(|| {
                    // Deterministic hash-based prover selection — the routing hot path.
                    let hash: usize = content.as_bytes().iter().fold(0usize, |acc, &byte| {
                        acc.wrapping_mul(31).wrapping_add(byte as usize)
                    });
                    let provers = black_box(ProverKind::all());
                    let selected = provers[hash % provers.len()];
                    black_box(selected)
                })
            },
        );
    }

    group.finish();
}

// ============================================================================
// Axiom Scan Throughput
//
// The axiom scanner is called for every proof result before computing trust.
// Its performance directly affects end-to-end proof verification latency.
// ============================================================================

/// Benchmark: axiom scanning at various proof content sizes.
fn bench_axiom_scan_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("axiom_scan_throughput");

    let sizes = [64, 256, 1024, 4096];

    for size in sizes {
        // Generate a proof content string of approximately `size` bytes.
        let content: String = std::iter::repeat("(assert (= x x))\n")
            .flat_map(|s| s.chars())
            .take(size)
            .collect();

        group.bench_with_input(
            BenchmarkId::new("scan_bytes", size),
            &content,
            |b, content| {
                b.iter(|| {
                    let tracker = AxiomTracker::new();
                    let result = tracker.scan(ProverKind::Z3, black_box(content));
                    black_box(result)
                })
            },
        );
    }

    group.finish();
}

// ============================================================================
// Trust Level Computation Latency
//
// Trust level computation happens after every proof verification. It must
// be fast because it sits on the critical path.
// ============================================================================

/// Benchmark: trust level computation under various factor combinations.
fn bench_trust_level_computation(c: &mut Criterion) {
    let mut group = c.benchmark_group("trust_level_computation");

    let factor_sets = [
        (
            "single_prover_no_cert",
            TrustFactors {
                prover: ProverKind::Z3,
                confirming_provers: 1,
                has_certificate: false,
                certificate_verified: false,
                worst_axiom_danger: DangerLevel::Safe,
                solver_integrity_ok: true,
                portfolio_confidence: None,
            },
        ),
        (
            "cross_checked_with_cert",
            TrustFactors {
                prover: ProverKind::Lean,
                confirming_provers: 3,
                has_certificate: true,
                certificate_verified: true,
                worst_axiom_danger: DangerLevel::Safe,
                solver_integrity_ok: true,
                portfolio_confidence: None,
            },
        ),
        (
            "reject_axiom_fast_path",
            TrustFactors {
                prover: ProverKind::Z3,
                confirming_provers: 5,
                has_certificate: true,
                certificate_verified: true,
                worst_axiom_danger: DangerLevel::Reject,
                solver_integrity_ok: true,
                portfolio_confidence: None,
            },
        ),
    ];

    for (label, factors) in factor_sets {
        group.bench_with_input(
            BenchmarkId::new("compute_trust", label),
            &factors,
            |b, f| {
                b.iter(|| {
                    let level = compute_trust_level(black_box(f));
                    black_box(level)
                })
            },
        );
    }

    group.finish();
}

// ============================================================================
// ProverFactory Instantiation Cost
//
// Measures the cold-start cost of creating a prover backend. This is relevant
// for server startup and for lazy initialisation strategies.
// ============================================================================

/// Benchmark: ProverFactory::create for different backends.
fn bench_prover_factory_instantiation(c: &mut Criterion) {
    let mut group = c.benchmark_group("prover_factory_instantiation");

    let backends = [
        ("z3", ProverKind::Z3),
        ("lean", ProverKind::Lean),
        ("coq", ProverKind::Coq),
        ("idris2", ProverKind::Idris2),
        ("agda", ProverKind::Agda),
    ];

    let config = ProverConfig::default();

    for (label, kind) in backends {
        group.bench_with_input(
            BenchmarkId::new("create_backend", label),
            &kind,
            |b, &kind| {
                b.iter(|| {
                    let prover = ProverFactory::create(black_box(kind), config.clone());
                    black_box(prover)
                })
            },
        );
    }

    group.finish();
}

// ============================================================================
// Agentic Planning Throughput
//
// Measures how quickly AgentConfig can be constructed and cloned.
// In the agentic planner, a new config may be derived for each sub-goal.
// ============================================================================

/// Benchmark: AgentConfig construction and cloning throughput.
fn bench_agentic_config_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("agentic_planning_throughput");

    // Benchmark: construction from scratch.
    group.bench_function("agent_config_construct", |b| {
        b.iter(|| {
            black_box(AgentConfig {
                max_concurrent: 8,
                max_attempts: 3,
                timeout_secs: 120,
                neural_enabled: true,
                reflection_enabled: true,
                planning_enabled: true,
            })
        })
    });

    // Benchmark: clone from existing config.
    let base_config = AgentConfig::default();
    group.bench_function("agent_config_clone", |b| {
        b.iter(|| black_box(base_config.clone()))
    });

    // Benchmark: JSON serialisation (used for config logging and audit).
    group.bench_function("agent_config_serialise", |b| {
        b.iter(|| {
            let json = serde_json::to_string(black_box(&base_config)).unwrap();
            black_box(json)
        })
    });

    group.finish();
}

// ============================================================================
// BLAKE3 Proof Hashing Throughput
//
// Proof identity hashing is on the critical path for certificate verification
// and deduplication. This benchmark baselines the cost per proof size.
// ============================================================================

/// Benchmark: BLAKE3 proof hashing at various content sizes.
fn bench_proof_hash_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_hash_throughput");

    let sizes = [64usize, 256, 1024, 4096, 16384];

    for size in sizes {
        let content: Vec<u8> = (0..size).map(|i| (i % 256) as u8).collect();
        group.bench_with_input(
            BenchmarkId::new("blake3_hash_bytes", size),
            &content,
            |b, data| {
                b.iter(|| {
                    let hash = blake3::hash(black_box(data));
                    black_box(hash)
                })
            },
        );
    }

    group.finish();
}

// ============================================================================
// DispatchConfig Construction
//
// DispatchConfig is constructed per-request in the routing layer.
// Its construction cost should be negligible.
// ============================================================================

/// Benchmark: DispatchConfig construction and default/custom.
fn bench_dispatch_config_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("dispatch_config_construction");

    group.bench_function("default_config", |b| {
        b.iter(|| black_box(DispatchConfig::default()))
    });

    group.bench_function("custom_config", |b| {
        b.iter(|| {
            black_box(DispatchConfig {
                cross_check: true,
                min_trust_level: TrustLevel::Level4,
                track_axioms: true,
                generate_certificates: true,
                timeout: 60,
                diagnostics: false,
            })
        })
    });

    group.finish();
}

// ============================================================================
// Criterion groups
// ============================================================================

criterion_group!(
    routing_benches,
    bench_routing_decision_latency,
    bench_axiom_scan_throughput,
    bench_trust_level_computation,
    bench_prover_factory_instantiation,
    bench_agentic_config_throughput,
    bench_proof_hash_throughput,
    bench_dispatch_config_construction,
);

criterion_main!(routing_benches);
