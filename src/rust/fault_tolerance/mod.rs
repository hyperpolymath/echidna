// SPDX-License-Identifier: MPL-2.0
// Fault-tolerance primitives for echidna prover backends
// Includes circuit breakers, retry policies, bulkheads

pub mod resilience;

pub use resilience::{
    BackoffStrategy, BulkheadConfig, CircuitBreaker, CircuitBreakerError, CircuitState, RetryPolicy,
};
