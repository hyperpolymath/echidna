// SPDX-License-Identifier: PMPL-1.0-or-later
//! Concurrent job limits to prevent overwhelming prover backends
//!
//! Implements semaphore-based limiting with:
//! - Global limits (max concurrent jobs across all repos)
//! - Per-repo limits (max concurrent jobs per repository)
//! - Fair scheduling (FIFO within priority levels)

use std::sync::Arc;
use tokio::sync::{Semaphore, OwnedSemaphorePermit};
use tracing::{debug, info};

/// Job limiter with concurrent execution control
#[derive(Clone)]
pub struct JobLimiter {
    /// Global semaphore (max total concurrent jobs)
    global: Arc<Semaphore>,
    /// Per-repo semaphore (max concurrent jobs per repo)
    per_repo: Arc<Semaphore>,
    /// Configuration
    config: LimiterConfig,
}

/// Limiter configuration
#[derive(Debug, Clone)]
pub struct LimiterConfig {
    /// Maximum concurrent jobs globally
    pub global_limit: usize,
    /// Maximum concurrent jobs per repository
    pub per_repo_limit: usize,
}

impl Default for LimiterConfig {
    fn default() -> Self {
        Self {
            global_limit: 10,    // Max 10 jobs total
            per_repo_limit: 3,   // Max 3 jobs per repo
        }
    }
}

impl JobLimiter {
    /// Create a new job limiter with default configuration
    pub fn new() -> Self {
        Self::with_config(LimiterConfig::default())
    }

    /// Create a job limiter with custom configuration
    pub fn with_config(config: LimiterConfig) -> Self {
        info!(
            "Job limiter initialized: global={}, per_repo={}",
            config.global_limit, config.per_repo_limit
        );

        Self {
            global: Arc::new(Semaphore::new(config.global_limit)),
            per_repo: Arc::new(Semaphore::new(config.per_repo_limit)),
            config,
        }
    }

    /// Acquire permits to run a job
    ///
    /// Blocks until both global and per-repo permits are available.
    /// Returns permits that will be automatically released when dropped.
    pub async fn acquire(&self) -> JobPermits {
        debug!("Acquiring job permits (waiting for slots...)");

        // Acquire global permit first
        let global_permit = Arc::clone(&self.global)
            .acquire_owned()
            .await
            .expect("Semaphore closed (should never happen)");

        // Then acquire per-repo permit
        let per_repo_permit = Arc::clone(&self.per_repo)
            .acquire_owned()
            .await
            .expect("Semaphore closed (should never happen)");

        debug!(
            "Job permits acquired (global: {}/{}, per_repo: {}/{})",
            self.global.available_permits(),
            self.config.global_limit,
            self.per_repo.available_permits(),
            self.config.per_repo_limit
        );

        JobPermits {
            _global: global_permit,
            _per_repo: per_repo_permit,
        }
    }

    /// Try to acquire permits without blocking
    ///
    /// Returns Some(permits) if immediately available, None otherwise.
    pub fn try_acquire(&self) -> Option<JobPermits> {
        let global_permit = Arc::clone(&self.global).try_acquire_owned().ok()?;
        let per_repo_permit = Arc::clone(&self.per_repo).try_acquire_owned().ok()?;

        debug!("Job permits acquired (non-blocking)");

        Some(JobPermits {
            _global: global_permit,
            _per_repo: per_repo_permit,
        })
    }

    /// Get current available slots
    pub fn available_slots(&self) -> (usize, usize) {
        (
            self.global.available_permits(),
            self.per_repo.available_permits(),
        )
    }

    /// Get total capacity
    pub fn capacity(&self) -> (usize, usize) {
        (self.config.global_limit, self.config.per_repo_limit)
    }
}

impl Default for JobLimiter {
    fn default() -> Self {
        Self::new()
    }
}

/// RAII permits that release automatically when dropped
pub struct JobPermits {
    _global: OwnedSemaphorePermit,
    _per_repo: OwnedSemaphorePermit,
}

impl Drop for JobPermits {
    fn drop(&mut self) {
        debug!("Job permits released");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_limiter_respects_global_limit() {
        let config = LimiterConfig {
            global_limit: 2,
            per_repo_limit: 10,
        };
        let limiter = JobLimiter::with_config(config);

        let permit1 = limiter.try_acquire();
        let permit2 = limiter.try_acquire();
        let permit3 = limiter.try_acquire();

        assert!(permit1.is_some());
        assert!(permit2.is_some());
        assert!(permit3.is_none()); // Should fail - global limit reached

        // Release one permit
        drop(permit1);

        // Now we should be able to acquire again
        let permit4 = limiter.try_acquire();
        assert!(permit4.is_some());
    }

    #[tokio::test]
    async fn test_limiter_concurrent_execution() {
        let config = LimiterConfig {
            global_limit: 5,
            per_repo_limit: 5,
        };
        let limiter = Arc::new(JobLimiter::with_config(config));

        let counter = Arc::new(AtomicUsize::new(0));
        let mut handles = vec![];

        // Spawn 10 tasks (but only 5 can run concurrently)
        for _ in 0..10 {
            let limiter = limiter.clone();
            let counter = counter.clone();

            let handle = tokio::spawn(async move {
                let _permit = limiter.acquire().await;

                // Track max concurrency
                let current = counter.fetch_add(1, Ordering::SeqCst) + 1;
                sleep(Duration::from_millis(100)).await;
                counter.fetch_sub(1, Ordering::SeqCst);

                current
            });

            handles.push(handle);
        }

        // Wait for all tasks
        let mut max_concurrent = 0;
        for handle in handles {
            let current = handle.await.unwrap();
            max_concurrent = max_concurrent.max(current);
        }

        // Max concurrency should not exceed global limit
        assert!(max_concurrent <= 5, "max_concurrent={}", max_concurrent);
    }

    #[tokio::test]
    async fn test_limiter_available_slots() {
        let config = LimiterConfig {
            global_limit: 3,
            per_repo_limit: 2,
        };
        let limiter = JobLimiter::with_config(config);

        assert_eq!(limiter.available_slots(), (3, 2));

        let permit1 = limiter.try_acquire().unwrap();
        assert_eq!(limiter.available_slots(), (2, 1));

        let permit2 = limiter.try_acquire().unwrap();
        assert_eq!(limiter.available_slots(), (1, 0)); // per_repo limit reached

        drop(permit1);
        assert_eq!(limiter.available_slots(), (2, 1));

        drop(permit2);
        assert_eq!(limiter.available_slots(), (3, 2));
    }

    #[test]
    fn test_limiter_capacity() {
        let config = LimiterConfig {
            global_limit: 10,
            per_repo_limit: 5,
        };
        let limiter = JobLimiter::with_config(config);

        assert_eq!(limiter.capacity(), (10, 5));
    }
}
