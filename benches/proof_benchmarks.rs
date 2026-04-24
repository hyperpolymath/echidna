// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Performance benchmarks for ECHIDNA proof operations
//!
//! Run with: cargo bench
//! Generates HTML reports in target/criterion/

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use echidna::core::{Context, Goal, Hypothesis, ProofState, Term};
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::axiom_tracker::AxiomTracker;
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::mutation::MutationTester;
use echidna::verification::pareto::{ParetoFrontier, ProofCandidate, ProofObjective};
use echidna::verification::portfolio::PortfolioConfidence;
use echidna::verification::statistics::StatisticsTracker;
use echidna::verification::DangerLevel;

use std::collections::HashMap;

// ============================================================================
// Core Type Benchmarks
// ============================================================================

/// Benchmark ProofState construction with varying goal counts
fn bench_proof_state_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_state_construction");
    for goal_count in [1, 5, 10, 50, 100] {
        group.bench_with_input(
            BenchmarkId::from_parameter(goal_count),
            &goal_count,
            |b, &n| {
                b.iter(|| {
                    let goals: Vec<Goal> = (0..n)
                        .map(|i| Goal {
                            id: format!("goal_{i}"),
                            hypotheses: vec![Hypothesis {
                                name: format!("h_{i}"),
                                ty: Term::Const("Prop".to_string()),
                                body: None,
                                type_info: None,
                            }],
                            target: Term::App {
                                func: Box::new(Term::Const("eq".to_string())),
                                args: vec![
                                    Term::Var(format!("x_{i}")),
                                    Term::Var(format!("x_{i}")),
                                ],
                            },
                        })
                        .collect();
                    black_box(ProofState {
                        goals,
                        context: Context::default(),
                        proof_script: vec![],
                        metadata: HashMap::new(),
                    })
                })
            },
        );
    }
    group.finish();
}

/// Benchmark Term AST construction (deeply nested)
fn bench_term_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("term_construction");
    for depth in [1, 5, 10, 20] {
        group.bench_with_input(BenchmarkId::from_parameter(depth), &depth, |b, &d| {
            b.iter(|| {
                let mut term = Term::Const("base".to_string());
                for i in 0..d {
                    term = Term::App {
                        func: Box::new(Term::Const(format!("f_{i}"))),
                        args: vec![term],
                    };
                }
                black_box(term)
            })
        });
    }
    group.finish();
}

// ============================================================================
// Prover Factory Benchmarks
// ============================================================================

/// Benchmark prover creation for representative backends
fn bench_prover_creation(c: &mut Criterion) {
    let provers = [
        ("Agda", ProverKind::Agda),
        ("Coq", ProverKind::Coq),
        ("Lean", ProverKind::Lean),
        ("Z3", ProverKind::Z3),
        ("CVC5", ProverKind::CVC5),
        ("Idris2", ProverKind::Idris2),
        ("Vampire", ProverKind::Vampire),
        ("Metamath", ProverKind::Metamath),
    ];

    let mut group = c.benchmark_group("prover_creation");
    for (name, kind) in &provers {
        group.bench_function(*name, |b| {
            b.iter(|| {
                let config = ProverConfig::default();
                black_box(ProverFactory::create(*kind, config).unwrap())
            })
        });
    }
    group.finish();
}

/// Benchmark prover kind detection from file extension
fn bench_prover_detection(c: &mut Criterion) {
    let files = [
        "test.agda",
        "test.v",
        "test.lean",
        "test.smt2",
        "test.thy",
        "test.idr",
        "test.p",
        "test.mm",
    ];

    let mut group = c.benchmark_group("prover_detection");
    for file in &files {
        group.bench_function(*file, |b| {
            let path = std::path::Path::new(file);
            b.iter(|| black_box(ProverFactory::detect_from_file(path)))
        });
    }
    group.finish();
}

// ============================================================================
// Trust Pipeline Benchmarks
// ============================================================================

/// Benchmark trust level computation with varying scenarios
fn bench_trust_computation(c: &mut Criterion) {
    let scenarios = [
        (
            "max_trust",
            TrustFactors {
                prover: ProverKind::Lean,
                confirming_provers: 3,
                has_certificate: true,
                certificate_verified: true,
                worst_axiom_danger: DangerLevel::Safe,
                solver_integrity_ok: true,
                portfolio_confidence: Some(PortfolioConfidence::CrossChecked),
            },
        ),
        (
            "single_prover",
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
            "dangerous",
            TrustFactors {
                prover: ProverKind::Lean,
                confirming_provers: 2,
                has_certificate: true,
                certificate_verified: true,
                worst_axiom_danger: DangerLevel::Reject,
                solver_integrity_ok: true,
                portfolio_confidence: Some(PortfolioConfidence::CrossChecked),
            },
        ),
    ];

    let mut group = c.benchmark_group("trust_computation");
    for (name, factors) in &scenarios {
        group.bench_function(*name, |b| {
            b.iter(|| black_box(compute_trust_level(factors)))
        });
    }
    group.finish();
}

/// Benchmark axiom danger scanning
fn bench_axiom_scanning(c: &mut Criterion) {
    let test_contents = [
        (
            "clean_lean",
            ProverKind::Lean,
            "theorem foo : True := trivial",
        ),
        (
            "sorry_lean",
            ProverKind::Lean,
            "theorem foo : True := by sorry",
        ),
        (
            "admitted_coq",
            ProverKind::Coq,
            "Theorem foo : True. Proof. Admitted.",
        ),
        (
            "believe_me_idris",
            ProverKind::Idris2,
            "foo : Bool\nfoo = believe_me True",
        ),
    ];

    let mut group = c.benchmark_group("axiom_scanning");
    for (name, prover, content) in &test_contents {
        group.bench_function(*name, |b| {
            let tracker = AxiomTracker::new();
            b.iter(|| black_box(tracker.scan(*prover, content)))
        });
    }
    group.finish();
}

// ============================================================================
// Verification Module Benchmarks
// ============================================================================

/// Benchmark mutation test generation
fn bench_mutation_generation(c: &mut Criterion) {
    c.bench_function("mutation_generation", |b| {
        let term = Term::App {
            func: Box::new(Term::Const("forall".to_string())),
            args: vec![Term::Lambda {
                param: "x".to_string(),
                param_type: Some(Box::new(Term::Universe(0))),
                body: Box::new(Term::App {
                    func: Box::new(Term::Const("eq".to_string())),
                    args: vec![
                        Term::App {
                            func: Box::new(Term::Const("add".to_string())),
                            args: vec![Term::Var("x".to_string()), Term::Const("0".to_string())],
                        },
                        Term::Var("x".to_string()),
                    ],
                }),
            }],
        };
        b.iter(|| {
            let tester = MutationTester::new();
            black_box(tester.generate_mutations(&term))
        })
    });
}

/// Benchmark Pareto frontier computation
fn bench_pareto_frontier(c: &mut Criterion) {
    let mut group = c.benchmark_group("pareto_frontier");
    for n_points in [10, 50, 100] {
        group.bench_with_input(BenchmarkId::from_parameter(n_points), &n_points, |b, &n| {
            b.iter(|| {
                let mut candidates: Vec<ProofCandidate> = (0..n)
                    .map(|i| ProofCandidate {
                        id: format!("candidate_{i}"),
                        objectives: ProofObjective {
                            proof_time_ms: (i as u64) * 100,
                            trust_level: TrustLevel::Level3,
                            memory_bytes: (n as u64 - i as u64) * 1024,
                            proof_steps: i * 5,
                        },
                        is_pareto_optimal: false,
                    })
                    .collect();
                black_box(ParetoFrontier::compute(&mut candidates))
            })
        });
    }
    group.finish();
}

/// Benchmark statistics tracker updates
fn bench_statistics_tracking(c: &mut Criterion) {
    c.bench_function("statistics_update_100", |b| {
        b.iter(|| {
            let mut tracker = StatisticsTracker::new();
            for i in 0..100u64 {
                tracker.record_success(ProverKind::Z3, "arithmetic", i * 10);
            }
            black_box(tracker.total_attempts())
        })
    });
}

// ============================================================================
// FFI Benchmarks
// ============================================================================

/// Benchmark FFI prover kind mapping roundtrip
fn bench_ffi_kind_mapping(c: &mut Criterion) {
    c.bench_function("ffi_kind_roundtrip_all_48", |b| {
        b.iter(|| {
            for i in 0u8..49 {
                if let Some(k) = echidna::ffi::kind_from_u8(i) {
                    black_box(echidna::ffi::kind_to_u8(k));
                }
            }
        })
    });
}

// ============================================================================
// Benchmark Groups
// ============================================================================

criterion_group!(
    core_benches,
    bench_proof_state_construction,
    bench_term_construction,
);

criterion_group!(
    prover_benches,
    bench_prover_creation,
    bench_prover_detection,
);

criterion_group!(trust_benches, bench_trust_computation, bench_axiom_scanning,);

criterion_group!(
    verification_benches,
    bench_mutation_generation,
    bench_pareto_frontier,
    bench_statistics_tracking,
);

criterion_group!(ffi_benches, bench_ffi_kind_mapping,);

criterion_main!(
    core_benches,
    prover_benches,
    trust_benches,
    verification_benches,
    ffi_benches,
);
