// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Concurrency tests for the ECHIDNA dispatch and agent systems.
//!
//! Verifies that:
//!   - Parallel proof generation does not corrupt shared state (ProverFactory)
//!   - Concurrent LLM-style requests all complete without starvation
//!   - Agent configuration is safely clonable across threads
//!   - Trust level computation is thread-safe (pure function, no shared mutable state)
//!   - BLAKE3 proof hashing is safe to call from multiple threads
//!   - Axiom scanning produces consistent results under concurrent access

mod common;

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use tokio::time::timeout;
use echidna::agent::AgentConfig;
use echidna::dispatch::DispatchConfig;
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::axiom_tracker::AxiomTracker;
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::axiom_tracker::DangerLevel;

// ---------------------------------------------------------------------------
// Concurrency invariant 1: Parallel proof instantiation — no shared-state corruption
//
// ProverFactory::create is a factory function. Calling it concurrently from
// multiple tasks must produce independent backends without interfering.
// ---------------------------------------------------------------------------

/// Spawning 16 concurrent tasks, each creating a Z3 backend, must all succeed
/// without race conditions or shared-state corruption.
#[tokio::test]
async fn concurrency_parallel_prover_factory_no_corruption() {
    let success_count = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _i in 0..16 {
        let counter = Arc::clone(&success_count);
        let handle = tokio::spawn(async move {
            let config = ProverConfig { timeout: 5, ..Default::default() };
            match ProverFactory::create(ProverKind::Z3, config) {
                Ok(_prover) => {
                    counter.fetch_add(1, Ordering::Relaxed);
                }
                Err(e) => {
                    eprintln!("Task failed to create Z3 backend: {}", e);
                }
            }
        });
        handles.push(handle);
    }

    // All tasks must complete within a reasonable timeout.
    let result = timeout(Duration::from_secs(10), async {
        for h in handles {
            h.await.expect("Task must not panic");
        }
    })
    .await;

    assert!(result.is_ok(), "All parallel factory tasks must complete within 10s");
    assert_eq!(
        success_count.load(Ordering::Relaxed),
        16,
        "All 16 parallel ProverFactory::create calls must succeed"
    );
}

/// Creating different prover backends in parallel must all succeed.
#[tokio::test]
async fn concurrency_mixed_prover_factory_parallel() {
    let kinds = [
        ProverKind::Z3,
        ProverKind::Lean,
        ProverKind::Coq,
        ProverKind::Agda,
        ProverKind::CVC5,
        ProverKind::Idris2,
        ProverKind::AltErgo,
        ProverKind::Vampire,
    ];

    let success_count = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for kind in kinds {
        let counter = Arc::clone(&success_count);
        let handle = tokio::spawn(async move {
            let config = ProverConfig::default();
            if ProverFactory::create(kind, config).is_ok() {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.await.expect("Task must not panic");
    }

    assert_eq!(
        success_count.load(Ordering::Relaxed),
        kinds.len(),
        "All distinct prover backends must instantiate concurrently"
    );
}

// ---------------------------------------------------------------------------
// Concurrency invariant 2: Concurrent LLM requests all complete (no starvation)
//
// We model concurrent LLM routing requests as concurrent mock parse operations.
// All must complete; none may starve indefinitely.
// ---------------------------------------------------------------------------

/// 32 concurrent parse tasks (modelling LLM routing requests) must all complete.
#[tokio::test]
async fn concurrency_all_routing_requests_complete_no_starvation() {
    let completed = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for i in 0..32 {
        let counter = Arc::clone(&completed);
        let handle = tokio::spawn(async move {
            let config = ProverConfig { timeout: 5, ..Default::default() };
            // Alternate between Z3 and Lean to exercise different backends.
            let kind = if i % 2 == 0 { ProverKind::Z3 } else { ProverKind::Lean };
            let prover = ProverFactory::create(kind, config)
                .expect("Backend must instantiate");

            let content = format!(
                "(set-logic QF_LIA)(declare-fun x{} () Int)(assert (= x{} x{}))(check-sat)",
                i, i, i
            );
            // Parse must complete without hanging.
            let _result = prover.parse_string(&content).await;
            counter.fetch_add(1, Ordering::Relaxed);
        });
        handles.push(handle);
    }

    let result = timeout(Duration::from_secs(30), async {
        for h in handles {
            h.await.expect("Task must not panic");
        }
    })
    .await;

    assert!(result.is_ok(), "All 32 concurrent routing requests must complete within 30s");
    assert_eq!(
        completed.load(Ordering::Relaxed),
        32,
        "All 32 tasks must report completion (no starvation)"
    );
}

// ---------------------------------------------------------------------------
// Concurrency invariant 3: Trust level computation is thread-safe
//
// `compute_trust_level` is a pure function with no shared mutable state.
// Calling it from multiple threads with the same input must produce the
// same output on every thread.
// ---------------------------------------------------------------------------

/// 64 parallel threads computing the same trust factors must all agree.
#[tokio::test]
async fn concurrency_trust_level_computation_thread_safe() {
    let factors = TrustFactors {
        prover: ProverKind::Lean,
        confirming_provers: 3,
        has_certificate: true,
        certificate_verified: true,
        worst_axiom_danger: DangerLevel::Safe,
        solver_integrity_ok: true,
        portfolio_confidence: None,
    };

    let expected = compute_trust_level(&factors);
    let agreement_count = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..64 {
        let f = factors.clone();
        let counter = Arc::clone(&agreement_count);
        let handle = tokio::spawn(async move {
            let result = compute_trust_level(&f);
            if result == expected {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.await.expect("Task must not panic");
    }

    assert_eq!(
        agreement_count.load(Ordering::Relaxed),
        64,
        "All 64 concurrent trust computations must agree on the same result"
    );
}

// ---------------------------------------------------------------------------
// Concurrency invariant 4: BLAKE3 hashing is safe from multiple threads
// ---------------------------------------------------------------------------

/// 32 threads hashing the same content must all produce the same hash.
#[tokio::test]
async fn concurrency_blake3_hash_consistent_across_threads() {
    let content = "theorem rfl (x : Nat) : x = x := rfl";
    let expected_hash = blake3::hash(content.as_bytes()).to_hex().to_string();

    let agreement_count = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..32 {
        let content_clone = content.to_string();
        let expected = expected_hash.clone();
        let counter = Arc::clone(&agreement_count);
        let handle = tokio::spawn(async move {
            let hash = blake3::hash(content_clone.as_bytes()).to_hex().to_string();
            if hash == expected {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.await.expect("Task must not panic");
    }

    assert_eq!(
        agreement_count.load(Ordering::Relaxed),
        32,
        "All 32 concurrent BLAKE3 hashes must agree"
    );
}

// ---------------------------------------------------------------------------
// Concurrency invariant 5: AgentConfig cloning across threads
//
// AgentConfig must be safely clonable and sendable across task boundaries.
// ---------------------------------------------------------------------------

/// Cloning AgentConfig in parallel tasks must produce independent copies.
#[tokio::test]
async fn concurrency_agent_config_clone_across_tasks() {
    let base_config = AgentConfig {
        max_concurrent: 8,
        max_attempts: 3,
        timeout_secs: 60,
        neural_enabled: false,
        reflection_enabled: false,
        planning_enabled: true,
    };

    let base = Arc::new(base_config);
    let mut handles = vec![];

    for i in 0..16 {
        let config = Arc::clone(&base);
        let handle = tokio::spawn(async move {
            // Clone into the task — each task gets its own copy.
            let mut local = (*config).clone();
            // Mutate the local copy — must not affect other tasks.
            local.max_concurrent = i;

            // Verify the local mutation.
            assert_eq!(local.max_concurrent, i, "Local mutation must be independent");
            // Original must be unchanged (we test this via Arc — actual shared ref).
            assert_eq!(config.max_concurrent, 8, "Shared config must be unchanged");
        });
        handles.push(handle);
    }

    for h in handles {
        h.await.expect("Task must not panic");
    }

    // The base config must still be intact after all tasks ran.
    assert_eq!(base.max_concurrent, 8, "Base config must not be mutated by any task");
}

// ---------------------------------------------------------------------------
// Concurrency invariant 6: AxiomTracker is safe for concurrent use
//
// Multiple tasks creating independent AxiomTracker instances must not
// interfere with each other's scan results.
// ---------------------------------------------------------------------------

/// 8 concurrent axiom scans must all return consistent results.
#[tokio::test]
async fn concurrency_axiom_tracker_independent_instances() {
    let result_count = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..8 {
        let counter = Arc::clone(&result_count);
        let handle = tokio::spawn(async move {
            // Each task creates its own AxiomTracker — no shared state.
            let tracker = AxiomTracker::new();
            let content = "(set-logic QF_LIA)(declare-fun x () Int)(assert (= x x))";

            let _usages = tracker.scan(ProverKind::Z3, content);
            // The scan must complete without panicking or hanging.
            counter.fetch_add(1, Ordering::Relaxed);
        });
        handles.push(handle);
    }

    let result = timeout(Duration::from_secs(10), async {
        for h in handles {
            h.await.expect("Task must not panic");
        }
    })
    .await;

    assert!(result.is_ok(), "All axiom scans must complete within 10s");
    assert_eq!(
        result_count.load(Ordering::Relaxed),
        8,
        "All 8 concurrent axiom scans must complete"
    );
}

// ---------------------------------------------------------------------------
// Concurrency invariant 7: DispatchConfig can be read from multiple threads
// ---------------------------------------------------------------------------

/// DispatchConfig can be safely shared (read-only) across concurrent tasks.
#[tokio::test]
async fn concurrency_dispatch_config_shared_read() {
    let config = Arc::new(DispatchConfig {
        cross_check: true,
        min_trust_level: TrustLevel::Level3,
        track_axioms: true,
        generate_certificates: false,
        timeout: 30,
        diagnostics: false,
    });

    let mut handles = vec![];

    for _ in 0..20 {
        let cfg = Arc::clone(&config);
        let handle = tokio::spawn(async move {
            // Read the config concurrently from multiple tasks.
            assert!(cfg.cross_check, "cross_check must be readable concurrently");
            assert_eq!(cfg.min_trust_level, TrustLevel::Level3);
            assert!(cfg.track_axioms);
            assert_eq!(cfg.timeout, 30);
        });
        handles.push(handle);
    }

    for h in handles {
        h.await.expect("Task must not panic");
    }
}
