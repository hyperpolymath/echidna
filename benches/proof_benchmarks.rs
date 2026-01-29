// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Performance benchmarks for ECHIDNA proof operations

use criterion::{black_box, criterion_group, criterion_main, Criterion};

/// Benchmark simple proof search operations
fn bench_simple_arithmetic(c: &mut Criterion) {
    c.bench_function("simple_goal_complexity", |b| {
        b.iter(|| {
            let goal = black_box("forall n : nat, n + 0 = n");
            // Simulate complexity calculation
            goal.matches("forall").count() * 10 + goal.len() / 10
        })
    });
}

/// Benchmark proof state construction
fn bench_proof_state(c: &mut Criterion) {
    c.bench_function("proof_state_creation", |b| {
        b.iter(|| {
            let hypotheses = vec!["H1: P".to_string(), "H2: Q".to_string()];
            let conclusion = "P /\\ Q";
            // Simulate proof state construction
            black_box(hypotheses.len() + conclusion.len())
        })
    });
}

/// Benchmark tactic application simulation
fn bench_tactic_application(c: &mut Criterion) {
    c.bench_function("tactic_selection", |b| {
        b.iter(|| {
            let goal = black_box("forall n : nat, n + 0 = n");
            // Simulate tactic selection heuristics
            if goal.contains("forall") {
                "intros"
            } else if goal.contains("=") {
                "reflexivity"
            } else {
                "auto"
            }
        })
    });
}

/// Benchmark ML confidence calculation
fn bench_ml_confidence(c: &mut Criterion) {
    c.bench_function("confidence_calculation", |b| {
        b.iter(|| {
            let goal_length = black_box(42);
            let quantifiers = black_box(2);
            // Simulate confidence score calculation
            let complexity = quantifiers as f64 * 10.0 + goal_length as f64 / 10.0;
            1.0 / (1.0 + (-complexity / 100.0).exp())
        })
    });
}

criterion_group!(
    benches,
    bench_simple_arithmetic,
    bench_proof_state,
    bench_tactic_application,
    bench_ml_confidence
);
criterion_main!(benches);
