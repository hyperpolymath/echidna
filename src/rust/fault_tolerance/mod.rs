// SPDX-License-Identifier: PMPL-1.0-or-later
// Fault-tolerance primitives for echidna prover backends
// Includes circuit breakers, retry policies, bulkheads

pub mod resilience;

pub use resilience::{
    CircuitBreaker, CircuitBreakerError, CircuitState, RetryPolicy, BulkheadConfig, BackoffStrategy,
};
