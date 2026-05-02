// SPDX-License-Identifier: PMPL-1.0-or-later
// Circuit breaker, retry policy, bulkhead isolation for fault tolerance

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use std::fmt;

/// Possible states of a circuit breaker
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// Requests pass through; failures increment counter
    Closed,
    /// Circuit is open; requests fail immediately without calling function
    Open,
    /// Half-open; one test request allowed to check recovery
    HalfOpen,
}

/// Error types from circuit breaker and resilience operations
#[derive(Debug, Clone)]
pub enum CircuitBreakerError {
    CircuitOpen,
    ProverFailed(String),
    Timeout,
    RetryExhausted { attempts: usize, last_error: String },
    BulkheadRejected { reason: String },
}

impl fmt::Display for CircuitBreakerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CircuitOpen => write!(f, "Circuit breaker is open"),
            Self::ProverFailed(msg) => write!(f, "Prover failed: {}", msg),
            Self::Timeout => write!(f, "Operation timed out"),
            Self::RetryExhausted { attempts, last_error } => {
                write!(f, "Retries exhausted ({} attempts): {}", attempts, last_error)
            }
            Self::BulkheadRejected { reason } => write!(f, "Bulkhead rejected: {}", reason),
        }
    }
}

impl std::error::Error for CircuitBreakerError {}

/// Backoff strategy for retries
#[derive(Debug, Clone)]
pub enum BackoffStrategy {
    /// Exponential backoff: base^attempt, capped at max
    Exponential { base: u64, max: Duration },
    /// Linear backoff: increment duration per attempt
    Linear { increment: Duration, max: Duration },
    /// Fibonacci backoff: F(n) * base_duration
    Fibonacci { max: Duration },
}

impl BackoffStrategy {
    /// Calculate backoff duration for a given attempt number (0-indexed)
    pub fn backoff_duration(&self, attempt: usize) -> Duration {
        match self {
            Self::Exponential { base, max } => {
                let duration = Duration::from_millis(*base << attempt);
                if duration > *max {
                    *max
                } else {
                    duration
                }
            }
            Self::Linear { increment, max } => {
                let duration = *increment * (attempt as u32 + 1);
                if duration > *max {
                    *max
                } else {
                    duration
                }
            }
            Self::Fibonacci { max } => {
                let fib = fibonacci(attempt);
                let duration = Duration::from_millis(fib * 10);
                if duration > *max {
                    *max
                } else {
                    duration
                }
            }
        }
    }
}

/// Fibonacci sequence: compute n-th number
fn fibonacci(n: usize) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => {
            let mut a = 0u64;
            let mut b = 1u64;
            for _ in 2..=n {
                let next = a.wrapping_add(b);
                a = b;
                b = next;
            }
            b
        }
    }
}

/// Retry policy with backoff strategy
#[derive(Debug, Clone)]
pub struct RetryPolicy {
    pub max_attempts: usize,
    pub backoff_strategy: BackoffStrategy,
    pub jitter_factor: f64,  // 0.0-1.0; adds randomness to backoff
}

impl RetryPolicy {
    pub fn new(max_attempts: usize, backoff_strategy: BackoffStrategy) -> Self {
        RetryPolicy {
            max_attempts,
            backoff_strategy,
            jitter_factor: 0.1,
        }
    }

    pub fn with_jitter(mut self, factor: f64) -> Self {
        self.jitter_factor = factor.clamp(0.0, 1.0);
        self
    }

    /// Calculate actual backoff with jitter
    pub fn backoff_with_jitter(&self, attempt: usize) -> Duration {
        let base = self.backoff_strategy.backoff_duration(attempt);
        let jitter_ms = (base.as_millis() as f64 * self.jitter_factor * rand::random::<f64>()) as u128;
        base + Duration::from_millis(jitter_ms as u64)
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        RetryPolicy {
            max_attempts: 3,
            backoff_strategy: BackoffStrategy::Exponential {
                base: 10,
                max: Duration::from_secs(5),
            },
            jitter_factor: 0.1,
        }
    }
}

/// Circuit breaker for individual prover
pub struct CircuitBreaker {
    name: String,
    state: Arc<Mutex<CircuitState>>,
    failure_threshold: usize,
    success_threshold: usize,
    timeout: Duration,
    last_failure: Arc<Mutex<Option<Instant>>>,
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
}

impl CircuitBreaker {
    pub fn new(name: String, failure_threshold: usize, success_threshold: usize, timeout: Duration) -> Self {
        CircuitBreaker {
            name,
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_threshold,
            success_threshold,
            timeout,
            last_failure: Arc::new(Mutex::new(None)),
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
        }
    }

    pub fn state(&self) -> CircuitState {
        *self.state.lock().unwrap()
    }

    /// Identifier for this breaker (typically the prover/backend name).
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn failure_count(&self) -> u32 {
        self.failure_count.load(Ordering::SeqCst)
    }

    pub fn success_count(&self) -> u32 {
        self.success_count.load(Ordering::SeqCst)
    }

    /// Record a successful call
    pub fn record_success(&self) {
        let mut state = self.state.lock().unwrap();
        match *state {
            CircuitState::HalfOpen => {
                self.success_count.fetch_add(1, Ordering::SeqCst);
                if self.success_count.load(Ordering::SeqCst) as usize >= self.success_threshold {
                    *state = CircuitState::Closed;
                    self.failure_count.store(0, Ordering::SeqCst);
                    self.success_count.store(0, Ordering::SeqCst);
                }
            }
            CircuitState::Closed => {
                self.failure_count.store(0, Ordering::SeqCst);
            }
            _ => {}
        }
    }

    /// Record a failed call
    pub fn record_failure(&self) {
        let mut state = self.state.lock().unwrap();
        self.failure_count.fetch_add(1, Ordering::SeqCst);

        match *state {
            CircuitState::Closed => {
                if self.failure_count.load(Ordering::SeqCst) as usize >= self.failure_threshold {
                    *state = CircuitState::Open;
                    *self.last_failure.lock().unwrap() = Some(Instant::now());
                }
            }
            CircuitState::HalfOpen => {
                *state = CircuitState::Open;
                *self.last_failure.lock().unwrap() = Some(Instant::now());
            }
            _ => {}
        }
    }

    /// Check if circuit can transition from Open to HalfOpen
    pub fn check_timeout_recovery(&self) {
        let mut state = self.state.lock().unwrap();
        if let CircuitState::Open = *state {
            if let Some(last_failure) = *self.last_failure.lock().unwrap() {
                if last_failure.elapsed() >= self.timeout {
                    *state = CircuitState::HalfOpen;
                    self.success_count.store(0, Ordering::SeqCst);
                }
            }
        }
    }

    /// Attempt a call through the circuit breaker
    pub async fn call<F, T>(&self, f: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, String>>,
    {
        self.check_timeout_recovery();

        match self.state() {
            CircuitState::Open => Err(CircuitBreakerError::CircuitOpen),
            CircuitState::HalfOpen | CircuitState::Closed => {
                match f.await {
                    Ok(result) => {
                        self.record_success();
                        Ok(result)
                    }
                    Err(e) => {
                        self.record_failure();
                        Err(CircuitBreakerError::ProverFailed(e))
                    }
                }
            }
        }
    }
}

/// Bulkhead isolation for concurrent access
pub struct BulkheadConfig {
    pub max_concurrent_per_prover: usize,
    pub timeout_per_call: Duration,
    pub queue_size: usize,
}

impl Default for BulkheadConfig {
    fn default() -> Self {
        BulkheadConfig {
            max_concurrent_per_prover: 5,
            timeout_per_call: Duration::from_secs(30),
            queue_size: 20,
        }
    }
}

pub struct Bulkhead {
    config: BulkheadConfig,
    current_permits: Arc<AtomicU32>,
}

impl Bulkhead {
    pub fn new(config: BulkheadConfig) -> Self {
        let max_permits = config.max_concurrent_per_prover as u32;
        Bulkhead {
            config,
            current_permits: Arc::new(AtomicU32::new(max_permits)),
        }
    }

    pub fn available_permits(&self) -> u32 {
        self.current_permits.load(Ordering::SeqCst)
    }

    /// Configuration this bulkhead was constructed with.
    pub fn config(&self) -> &BulkheadConfig {
        &self.config
    }

    pub fn is_available(&self) -> bool {
        self.available_permits() > 0
    }

    /// Try to acquire a permit; returns Err if no permits available
    pub fn try_acquire(&self) -> Result<BulkheadGuard, CircuitBreakerError> {
        if self.current_permits.load(Ordering::SeqCst) == 0 {
            return Err(CircuitBreakerError::BulkheadRejected {
                reason: "No available permits".to_string(),
            });
        }

        self.current_permits.fetch_sub(1, Ordering::SeqCst);
        Ok(BulkheadGuard {
            permits: self.current_permits.clone(),
        })
    }
}

/// Guard to release a bulkhead permit on drop
pub struct BulkheadGuard {
    permits: Arc<AtomicU32>,
}

impl Drop for BulkheadGuard {
    fn drop(&mut self) {
        self.permits.fetch_add(1, Ordering::SeqCst);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(2), 1);
        assert_eq!(fibonacci(3), 2);
        assert_eq!(fibonacci(4), 3);
        assert_eq!(fibonacci(5), 5);
        assert_eq!(fibonacci(10), 55);
    }

    #[test]
    fn test_backoff_exponential() {
        let strategy = BackoffStrategy::Exponential {
            base: 10,
            max: Duration::from_secs(1),
        };
        assert_eq!(strategy.backoff_duration(0), Duration::from_millis(10));
        assert_eq!(strategy.backoff_duration(1), Duration::from_millis(20));
        assert_eq!(strategy.backoff_duration(2), Duration::from_millis(40));
        assert!(strategy.backoff_duration(10) <= Duration::from_secs(1));
    }

    #[test]
    fn test_backoff_linear() {
        let strategy = BackoffStrategy::Linear {
            increment: Duration::from_millis(100),
            max: Duration::from_secs(1),
        };
        assert_eq!(strategy.backoff_duration(0), Duration::from_millis(100));
        assert_eq!(strategy.backoff_duration(1), Duration::from_millis(200));
        assert_eq!(strategy.backoff_duration(2), Duration::from_millis(300));
    }

    #[test]
    fn test_circuit_breaker_basic() {
        let cb = CircuitBreaker::new("test".to_string(), 2, 2, Duration::from_secs(1));
        assert_eq!(cb.state(), CircuitState::Closed);

        // Two failures should open circuit
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Closed);
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
    }

    #[test]
    fn test_circuit_breaker_recovery() {
        let cb = CircuitBreaker::new("test".to_string(), 1, 1, Duration::from_millis(100));

        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);

        // Wait for timeout
        std::thread::sleep(Duration::from_millis(150));
        cb.check_timeout_recovery();
        assert_eq!(cb.state(), CircuitState::HalfOpen);

        // Success should close
        cb.record_success();
        assert_eq!(cb.state(), CircuitState::Closed);
    }

    #[test]
    fn test_bulkhead() {
        let config = BulkheadConfig {
            max_concurrent_per_prover: 2,
            timeout_per_call: Duration::from_secs(5),
            queue_size: 10,
        };
        let bulkhead = Bulkhead::new(config);

        // Should have 2 permits
        assert_eq!(bulkhead.available_permits(), 2);

        // Acquire one
        let _guard1 = bulkhead.try_acquire().unwrap();
        assert_eq!(bulkhead.available_permits(), 1);

        // Acquire another
        let _guard2 = bulkhead.try_acquire().unwrap();
        assert_eq!(bulkhead.available_permits(), 0);

        // Should fail now
        assert!(bulkhead.try_acquire().is_err());

        // Drop one guard; should be available again
        drop(_guard1);
        assert_eq!(bulkhead.available_permits(), 1);
    }

    #[tokio::test]
    async fn test_circuit_breaker_call() {
        let cb = CircuitBreaker::new("test".to_string(), 2, 1, Duration::from_secs(1));

        // First call succeeds
        let result = cb.call(async { Ok(42) }).await;
        assert!(result.is_ok());

        // Fail twice to open circuit
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);

        // Now calls should fail immediately
        let result = cb.call(async { Ok(43) }).await;
        assert!(matches!(result, Err(CircuitBreakerError::CircuitOpen)));
    }
}
