// SPDX-License-Identifier: AGPL-3.0-or-later
// Fault-tolerance primitives for echidna prover backends
// Includes circuit breakers, retry policies, bulkheads

pub mod resilience;

pub use resilience::{
    BackoffStrategy, BulkheadConfig, CircuitBreaker, CircuitBreakerError, CircuitState, RetryPolicy,
};
