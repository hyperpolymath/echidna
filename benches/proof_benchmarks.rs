// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// Criterion-based benchmarks for proof search performance

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use echidna::provers::*;
use echidna::core::*;

fn bench_simple_arithmetic(c: &mut Criterion) {
    let mut group = c.benchmark_group("simple_arithmetic");

    // Benchmark: n + 0 = n (right identity)
    group.bench_function("add_zero_right", |b| {
        b.iter(|| {
            let goal = black_box("forall n : nat, n + 0 = n");
            // Simulate proof search (replace with actual prover call)
            goal.len()
        })
    });

    // Benchmark: 0 + n = n (left identity)
    group.bench_function("add_zero_left", |b| {
        b.iter(|| {
            let goal = black_box("forall n : nat, 0 + n = n");
            goal.len()
        })
    });

    // Benchmark: n + m = m + n (commutativity)
    group.bench_function("add_commutativity", |b| {
        b.iter(|| {
            let goal = black_box("forall n m : nat, n + m = m + n");
            goal.len()
        })
    });

    group.finish();
}

fn bench_ml_inference(c: &mut Criterion) {
    let mut group = c.benchmark_group("ml_inference");

    let goals = vec![
        "forall n, n + 0 = n",
        "forall n m, n + m = m + n",
        "forall n m p, (n + m) + p = n + (m + p)",
    ];

    for (i, goal) in goals.iter().enumerate() {
        group.bench_with_input(
            BenchmarkId::new("tactic_suggestion", i),
            goal,
            |b, &goal| {
                b.iter(|| {
                    // Simulate ML inference (replace with actual Julia API call)
                    let _hash = black_box(goal).as_bytes().iter().sum::<u8>();
                })
            },
        );
    }

    group.finish();
}

fn bench_proof_tree_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_tree");

    group.bench_function("create_tree", |b| {
        b.iter(|| {
            // Simulate proof tree construction
            let mut nodes = Vec::new();
            for i in 0..10 {
                nodes.push(black_box(i));
            }
            nodes
        })
    });

    group.bench_function("add_tactic", |b| {
        b.iter(|| {
            let mut tactics = Vec::new();
            for _ in 0..5 {
                tactics.push(black_box("intro".to_string()));
            }
            tactics
        })
    });

    group.finish();
}

fn bench_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("parsing");

    let terms = vec![
        "forall n : nat, n + 0 = n",
        "exists x : nat, x > 0",
        "forall n m p : nat, (n + m) + p = n + (m + p)",
    ];

    for (i, term) in terms.iter().enumerate() {
        group.bench_with_input(
            BenchmarkId::new("parse_term", i),
            term,
            |b, &term| {
                b.iter(|| {
                    // Simulate term parsing
                    black_box(term).chars().count()
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_simple_arithmetic,
    bench_ml_inference,
    bench_proof_tree_construction,
    bench_parsing
);
criterion_main!(benches);
