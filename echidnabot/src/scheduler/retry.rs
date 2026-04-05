// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Retry logic with exponential backoff and circuit breaker
//!
//! Implements retry mechanism for:
//! - Network timeouts
//! - Temporary prover unavailability
//! - Rate limiting
//! - Transient ECHIDNA Core failures
//!
//! Strategy: Exponential backoff with jitter
//! - Retry 1: 1s
//! - Retry 2: 2s
//! - Retry 3: 4s
//! - Max retries: 3
//!
//! Circuit breaker:
//! - Opens after 5 consecutive failures
//! - Auto-resets after 5 minutes
//! - When open, all requests fail immediately

use crate::error::{Error, Result};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use tokio::time::sleep;
use tracing::{debug, info, warn};

/// Retry configuration
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// Maximum number of retry attempts
    pub max_retries: usize,
    /// Initial backoff duration
    pub initial_backoff: Duration,
    /// Maximum backoff duration
    pub max_backoff: Duration,
    /// Backoff multiplier
    pub multiplier: f64,
    /// Add jitter to prevent thundering herd
    pub jitter: bool,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff: Duration::from_secs(1),
            max_backoff: Duration::from_secs(60),
            multiplier: 2.0,
            jitter: true,
        }
    }
}

// =============================================================================
// Circuit Breaker
// =============================================================================

/// Circuit breaker state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// Normal operation -- requests pass through
    Closed,
    /// Too many failures -- requests fail immediately
    Open,
    /// Testing if the service has recovered
    HalfOpen,
}

/// Circuit breaker for ECHIDNA API protection.
///
/// Opens after `failure_threshold` consecutive failures and auto-resets
/// after `reset_timeout`. Prevents overwhelming a failing service.
pub struct CircuitBreaker {
    /// Current state
    state: Mutex<CircuitState>,
    /// Consecutive failure count
    failure_count: AtomicUsize,
    /// Threshold to trip the breaker
    failure_threshold: usize,
    /// Time to wait before attempting to close the circuit
    reset_timeout: Duration,
    /// When the circuit was last opened
    last_failure_time: Mutex<Option<Instant>>,
}

impl CircuitBreaker {
    /// Create a new circuit breaker.
    ///
    /// # Arguments
    /// * `failure_threshold` - Number of consecutive failures before opening
    /// * `reset_timeout` - Duration to wait before trying half-open
    pub fn new(failure_threshold: usize, reset_timeout: Duration) -> Self {
        Self {
            state: Mutex::new(CircuitState::Closed),
            failure_count: AtomicUsize::new(0),
            failure_threshold,
            reset_timeout,
            last_failure_time: Mutex::new(None),
        }
    }

    /// Create a circuit breaker with default ECHIDNA settings.
    ///
    /// Opens after 5 failures, resets after 5 minutes.
    pub fn default_echidna() -> Self {
        Self::new(5, Duration::from_secs(300))
    }

    /// Check if the circuit allows a request to pass through.
    ///
    /// Returns `Ok(())` if the request should proceed, or `Err` if the
    /// circuit is open and the request should be rejected.
    pub async fn check(&self) -> Result<()> {
        let mut state = self.state.lock().await;

        match *state {
            CircuitState::Closed => Ok(()),
            CircuitState::Open => {
                // Check if reset timeout has elapsed
                let last_failure = self.last_failure_time.lock().await;
                if let Some(last) = *last_failure {
                    if last.elapsed() >= self.reset_timeout {
                        info!("Circuit breaker transitioning to half-open");
                        *state = CircuitState::HalfOpen;
                        return Ok(());
                    }
                }

                warn!(
                    "Circuit breaker is OPEN ({} consecutive failures). \
                     Resets in {:?}.",
                    self.failure_count.load(Ordering::Relaxed),
                    self.reset_timeout,
                );

                Err(Error::Echidna(
                    "Circuit breaker is open: ECHIDNA API has failed too many \
                     consecutive times. Auto-resetting in 5 minutes."
                        .to_string(),
                ))
            }
            CircuitState::HalfOpen => {
                // Allow one request through to test recovery
                Ok(())
            }
        }
    }

    /// Record a successful operation.
    pub async fn record_success(&self) {
        self.failure_count.store(0, Ordering::Relaxed);
        let mut state = self.state.lock().await;
        if *state == CircuitState::HalfOpen {
            info!("Circuit breaker closing (service recovered)");
            *state = CircuitState::Closed;
        }
    }

    /// Record a failed operation.
    pub async fn record_failure(&self) {
        let count = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;

        if count >= self.failure_threshold {
            let mut state = self.state.lock().await;
            if *state != CircuitState::Open {
                warn!(
                    "Circuit breaker OPENING after {} consecutive failures",
                    count,
                );
                *state = CircuitState::Open;
                let mut last = self.last_failure_time.lock().await;
                *last = Some(Instant::now());
            }
        }
    }

    /// Get the current circuit state.
    pub async fn state(&self) -> CircuitState {
        *self.state.lock().await
    }

    /// Get the consecutive failure count.
    pub fn failure_count(&self) -> usize {
        self.failure_count.load(Ordering::Relaxed)
    }

    /// Manually reset the circuit breaker.
    pub async fn reset(&self) {
        self.failure_count.store(0, Ordering::Relaxed);
        let mut state = self.state.lock().await;
        *state = CircuitState::Closed;
        let mut last = self.last_failure_time.lock().await;
        *last = None;
        info!("Circuit breaker manually reset");
    }
}

impl Default for CircuitBreaker {
    fn default() -> Self {
        Self::default_echidna()
    }
}

// =============================================================================
// Retry Policy
// =============================================================================

/// Retry policy with exponential backoff.
pub struct RetryPolicy {
    config: RetryConfig,
}

impl RetryPolicy {
    /// Create a new retry policy with default configuration
    pub fn new() -> Self {
        Self {
            config: RetryConfig::default(),
        }
    }

    /// Create a retry policy with custom configuration
    pub fn with_config(config: RetryConfig) -> Self {
        Self { config }
    }

    /// Execute a fallible operation with retries.
    ///
    /// # Arguments
    /// * `operation` - Async function to execute
    /// * `is_retryable` - Function to determine if error should be retried
    ///
    /// # Returns
    /// Result of the operation, or last error if all retries exhausted
    pub async fn execute<F, Fut, T, E>(
        &self,
        mut operation: F,
        is_retryable: impl Fn(&E) -> bool,
    ) -> std::result::Result<T, E>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = std::result::Result<T, E>>,
        E: std::fmt::Display,
    {
        let mut attempt = 0;
        let mut backoff = self.config.initial_backoff;

        loop {
            match operation().await {
                Ok(result) => {
                    if attempt > 0 {
                        debug!("Operation succeeded after {} retries", attempt);
                    }
                    return Ok(result);
                }
                Err(error) => {
                    attempt += 1;

                    if attempt > self.config.max_retries {
                        warn!(
                            "Operation failed after {} attempts: {}",
                            self.config.max_retries, error
                        );
                        return Err(error);
                    }

                    if !is_retryable(&error) {
                        warn!("Operation failed with non-retryable error: {}", error);
                        return Err(error);
                    }

                    // Calculate delay with optional jitter
                    let delay = if self.config.jitter {
                        let jitter_factor = 0.5 + (rand::random::<f64>() * 0.5); // 0.5-1.0
                        Duration::from_secs_f64(backoff.as_secs_f64() * jitter_factor)
                    } else {
                        backoff
                    };

                    warn!(
                        "Operation failed (attempt {}/{}): {}. Retrying in {:?}...",
                        attempt, self.config.max_retries, error, delay
                    );

                    sleep(delay).await;

                    // Exponential backoff
                    backoff = Duration::from_secs_f64(
                        (backoff.as_secs_f64() * self.config.multiplier)
                            .min(self.config.max_backoff.as_secs_f64()),
                    );
                }
            }
        }
    }

    /// Execute with automatic retry on common transient errors.
    pub async fn execute_auto<F, Fut, T>(&self, operation: F) -> Result<T>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        self.execute(operation, is_transient_error).await
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// Determine if an error is transient and should be retried.
pub fn is_transient_error(error: &Error) -> bool {
    match error {
        // Network errors - always retry
        Error::Http(_) => true,

        // ECHIDNA errors - check if transient
        Error::Echidna(msg) => {
            let msg_lower = msg.to_lowercase();
            msg_lower.contains("timeout")
                || msg_lower.contains("unavailable")
                || msg_lower.contains("rate limit")
                || msg_lower.contains("temporary")
                || msg_lower.contains("503")
                || msg_lower.contains("504")
        }

        // Proof timeout -- do NOT retry (intentional, resource-saving)
        Error::Timeout => false,

        // Database errors - some are retryable
        Error::Sqlx(sqlx_err) => {
            let err_msg = sqlx_err.to_string().to_lowercase();
            err_msg.contains("connection")
                || err_msg.contains("timeout")
                || err_msg.contains("deadlock")
        }

        // Internal errors - generally not retryable
        Error::Internal(_) => false,

        // Config/validation errors - never retry
        Error::Config(_) | Error::InvalidInput(_) => false,

        // All other errors - default to not retrying for safety
        _ => false,
    }
}

/// Retry helper for async operations.
///
/// # Example
/// ```no_run
/// use echidnabot::scheduler::retry::retry;
///
/// # async fn example() {
/// let result = retry(3, || async {
///     // Your async operation
///     Ok::<_, echidnabot::Error>(())
/// }).await;
/// # }
/// ```
pub async fn retry<F, Fut, T>(max_attempts: usize, operation: F) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let config = RetryConfig {
        max_retries: max_attempts,
        ..Default::default()
    };

    RetryPolicy::with_config(config)
        .execute_auto(operation)
        .await
}

/// Retry with custom backoff.
pub async fn retry_with_backoff<F, Fut, T>(
    max_attempts: usize,
    initial_backoff: Duration,
    operation: F,
) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let config = RetryConfig {
        max_retries: max_attempts,
        initial_backoff,
        ..Default::default()
    };

    RetryPolicy::with_config(config)
        .execute_auto(operation)
        .await
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[tokio::test]
    async fn test_retry_success_first_attempt() {
        let counter = Arc::new(AtomicUsize::new(0));
        let counter_clone = counter.clone();

        let result = retry(3, || {
            let counter = counter_clone.clone();
            async move {
                counter.fetch_add(1, Ordering::SeqCst);
                Ok::<_, Error>(42)
            }
        })
        .await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn test_retry_success_after_failures() {
        let counter = Arc::new(AtomicUsize::new(0));
        let counter_clone = counter.clone();

        let result = retry(3, || {
            let counter = counter_clone.clone();
            async move {
                let attempt = counter.fetch_add(1, Ordering::SeqCst) + 1;
                if attempt < 3 {
                    // Use Echidna error with transient message (retryable)
                    Err(Error::Echidna("503 unavailable".to_string()))
                } else {
                    Ok(42)
                }
            }
        })
        .await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[tokio::test]
    async fn test_retry_exhausted() {
        let counter = Arc::new(AtomicUsize::new(0));
        let counter_clone = counter.clone();

        let result = retry(3, || {
            let counter = counter_clone.clone();
            async move {
                counter.fetch_add(1, Ordering::SeqCst);
                // Use Echidna error with transient message (retryable)
                Err::<i32, _>(Error::Echidna("503 unavailable".to_string()))
            }
        })
        .await;

        assert!(result.is_err());
        assert_eq!(counter.load(Ordering::SeqCst), 4); // Initial + 3 retries = 4
    }

    #[tokio::test]
    async fn test_non_retryable_error() {
        let counter = Arc::new(AtomicUsize::new(0));
        let counter_clone = counter.clone();

        let result = retry(3, || {
            let counter = counter_clone.clone();
            async move {
                counter.fetch_add(1, Ordering::SeqCst);
                Err::<i32, _>(Error::InvalidInput("bad input".to_string()))
            }
        })
        .await;

        assert!(result.is_err());
        assert_eq!(counter.load(Ordering::SeqCst), 1); // No retries
    }

    #[test]
    fn test_is_transient_error() {
        // Transient errors
        assert!(is_transient_error(&Error::Echidna("timeout".to_string())));
        assert!(is_transient_error(&Error::Echidna(
            "503 unavailable".to_string()
        )));
        assert!(is_transient_error(&Error::Echidna(
            "rate limit exceeded".to_string()
        )));
        assert!(is_transient_error(&Error::Echidna(
            "504 gateway timeout".to_string()
        )));
        assert!(is_transient_error(&Error::Echidna(
            "temporary failure".to_string()
        )));

        // Non-transient errors
        assert!(!is_transient_error(&Error::InvalidInput("bad".to_string())));
        assert!(!is_transient_error(&Error::Config("bad config".to_string())));
        assert!(!is_transient_error(&Error::Timeout)); // Proof timeout -- don't retry
        assert!(!is_transient_error(&Error::Internal("panic".to_string())));
    }

    // =========================================================================
    // Circuit Breaker Tests
    // =========================================================================

    #[tokio::test]
    async fn test_circuit_breaker_starts_closed() {
        let cb = CircuitBreaker::new(3, Duration::from_secs(60));
        assert_eq!(cb.state().await, CircuitState::Closed);
        assert_eq!(cb.failure_count(), 0);
        assert!(cb.check().await.is_ok());
    }

    #[tokio::test]
    async fn test_circuit_breaker_opens_after_threshold() {
        let cb = CircuitBreaker::new(3, Duration::from_secs(60));

        cb.record_failure().await;
        assert_eq!(cb.state().await, CircuitState::Closed);

        cb.record_failure().await;
        assert_eq!(cb.state().await, CircuitState::Closed);

        cb.record_failure().await;
        assert_eq!(cb.state().await, CircuitState::Open);

        // Should reject requests when open
        let result = cb.check().await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_circuit_breaker_success_resets_count() {
        let cb = CircuitBreaker::new(3, Duration::from_secs(60));

        cb.record_failure().await;
        cb.record_failure().await;
        assert_eq!(cb.failure_count(), 2);

        cb.record_success().await;
        assert_eq!(cb.failure_count(), 0);
        assert_eq!(cb.state().await, CircuitState::Closed);
    }

    #[tokio::test]
    async fn test_circuit_breaker_manual_reset() {
        let cb = CircuitBreaker::new(2, Duration::from_secs(60));

        cb.record_failure().await;
        cb.record_failure().await;
        assert_eq!(cb.state().await, CircuitState::Open);

        cb.reset().await;
        assert_eq!(cb.state().await, CircuitState::Closed);
        assert_eq!(cb.failure_count(), 0);
        assert!(cb.check().await.is_ok());
    }

    #[tokio::test]
    async fn test_circuit_breaker_half_open_on_timeout() {
        // Use a very short reset timeout for testing
        let cb = CircuitBreaker::new(2, Duration::from_millis(50));

        cb.record_failure().await;
        cb.record_failure().await;
        assert_eq!(cb.state().await, CircuitState::Open);

        // Wait for reset timeout
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Should transition to half-open on next check
        assert!(cb.check().await.is_ok());
        assert_eq!(cb.state().await, CircuitState::HalfOpen);
    }

    #[tokio::test]
    async fn test_circuit_breaker_half_open_success_closes() {
        let cb = CircuitBreaker::new(2, Duration::from_millis(50));

        cb.record_failure().await;
        cb.record_failure().await;

        // Wait for reset timeout
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Transition to half-open
        cb.check().await.ok();
        assert_eq!(cb.state().await, CircuitState::HalfOpen);

        // Success should close the circuit
        cb.record_success().await;
        assert_eq!(cb.state().await, CircuitState::Closed);
    }

    #[tokio::test]
    async fn test_circuit_breaker_default_echidna() {
        let cb = CircuitBreaker::default_echidna();
        // 5 failures, 5 minute timeout
        assert_eq!(cb.failure_threshold, 5);
        assert_eq!(cb.reset_timeout, Duration::from_secs(300));
    }
}
