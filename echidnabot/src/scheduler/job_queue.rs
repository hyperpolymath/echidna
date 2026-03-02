//! Job queue management

use std::collections::VecDeque;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::sync::Mutex;
use uuid::Uuid;

use super::{JobId, ProofJob};
use crate::error::Result;

/// Job scheduler managing the verification queue
pub struct JobScheduler {
    /// Queue of pending jobs (priority-ordered)
    queue: Arc<Mutex<VecDeque<ProofJob>>>,

    /// Currently running jobs
    running: Arc<Mutex<Vec<ProofJob>>>,

    /// Number of active jobs
    active_count: AtomicUsize,

    /// Maximum concurrent jobs
    max_concurrent: usize,

    /// Maximum queue size
    max_queue_size: usize,
}

impl JobScheduler {
    /// Create a new job scheduler
    pub fn new(max_concurrent: usize, max_queue_size: usize) -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            running: Arc::new(Mutex::new(Vec::new())),
            active_count: AtomicUsize::new(0),
            max_concurrent,
            max_queue_size,
        }
    }

    /// Enqueue a new proof job
    ///
    /// Returns None if a duplicate job already exists (same repo, commit, prover)
    pub async fn enqueue(&self, job: ProofJob) -> Result<Option<JobId>> {
        let mut queue = self.queue.lock().await;

        // Check queue size limit
        if queue.len() >= self.max_queue_size {
            tracing::warn!("Job queue full, rejecting job {}", job.id);
            return Ok(None);
        }

        // Check for duplicates
        let is_duplicate = queue.iter().any(|j| {
            j.repo_id == job.repo_id
                && j.commit_sha == job.commit_sha
                && j.prover == job.prover
        });

        if is_duplicate {
            tracing::debug!("Duplicate job detected, skipping");
            return Ok(None);
        }

        let job_id = job.id;

        // Insert in priority order
        let insert_pos = queue
            .iter()
            .position(|j| j.priority < job.priority)
            .unwrap_or(queue.len());

        queue.insert(insert_pos, job);

        tracing::info!("Enqueued job {} (queue size: {})", job_id, queue.len());
        Ok(Some(job_id))
    }

    /// Try to start the next job if capacity allows
    pub async fn try_start_next(&self) -> Option<ProofJob> {
        if self.active_count.load(Ordering::Relaxed) >= self.max_concurrent {
            return None;
        }

        let mut queue = self.queue.lock().await;
        let mut job = queue.pop_front()?;

        job.start();
        self.active_count.fetch_add(1, Ordering::Relaxed);

        let mut running = self.running.lock().await;
        running.push(job.clone());

        tracing::info!(
            "Started job {} (active: {}/{})",
            job.id,
            self.active_count.load(Ordering::Relaxed),
            self.max_concurrent
        );

        Some(job)
    }

    /// Mark a job as completed
    pub async fn complete_job(&self, job_id: JobId, success: bool, message: String) {
        let mut running = self.running.lock().await;

        if let Some(pos) = running.iter().position(|j| j.id == job_id) {
            let mut job = running.remove(pos);
            job.complete(super::JobResult {
                success,
                message,
                prover_output: String::new(),
                duration_ms: job.duration_ms().unwrap_or(0),
                verified_files: vec![],
                failed_files: vec![],
            });

            self.active_count.fetch_sub(1, Ordering::Relaxed);

            tracing::info!(
                "Completed job {} (success: {}, active: {})",
                job_id,
                success,
                self.active_count.load(Ordering::Relaxed)
            );
        }
    }

    /// Get job by ID
    pub async fn get_job(&self, job_id: JobId) -> Option<ProofJob> {
        // Check running jobs
        {
            let running = self.running.lock().await;
            if let Some(job) = running.iter().find(|j| j.id == job_id) {
                return Some(job.clone());
            }
        }

        // Check queue
        {
            let queue = self.queue.lock().await;
            if let Some(job) = queue.iter().find(|j| j.id == job_id) {
                return Some(job.clone());
            }
        }

        None
    }

    /// Get all jobs for a repository
    pub async fn jobs_for_repo(&self, repo_id: Uuid) -> Vec<ProofJob> {
        let mut jobs = Vec::new();

        {
            let running = self.running.lock().await;
            jobs.extend(running.iter().filter(|j| j.repo_id == repo_id).cloned());
        }

        {
            let queue = self.queue.lock().await;
            jobs.extend(queue.iter().filter(|j| j.repo_id == repo_id).cloned());
        }

        jobs
    }

    /// Cancel a job
    pub async fn cancel_job(&self, job_id: JobId) -> bool {
        // Try to remove from queue first
        {
            let mut queue = self.queue.lock().await;
            if let Some(pos) = queue.iter().position(|j| j.id == job_id) {
                let mut job = match queue.remove(pos) {
                    Some(j) => j,
                    None => return false,
                };
                job.cancel();
                tracing::info!("Cancelled queued job {}", job_id);
                return true;
            }
        }

        // Can't cancel running jobs (would need to implement cancellation tokens)
        tracing::warn!("Cannot cancel running job {}", job_id);
        false
    }

    /// Get queue statistics
    pub async fn stats(&self) -> QueueStats {
        let queue = self.queue.lock().await;
        let running = self.running.lock().await;

        QueueStats {
            queued: queue.len(),
            running: running.len(),
            max_concurrent: self.max_concurrent,
            max_queue_size: self.max_queue_size,
        }
    }

    /// Check if there's capacity for more jobs
    pub fn has_capacity(&self) -> bool {
        self.active_count.load(Ordering::Relaxed) < self.max_concurrent
    }
}

/// Queue statistics
#[derive(Debug, Clone)]
pub struct QueueStats {
    pub queued: usize,
    pub running: usize,
    pub max_concurrent: usize,
    pub max_queue_size: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatcher::ProverKind;
    use crate::scheduler::{JobPriority, JobStatus};

    #[tokio::test]
    async fn test_enqueue_and_start() {
        let scheduler = JobScheduler::new(2, 10);

        let job1 = ProofJob::new(
            Uuid::new_v4(),
            "abc123".to_string(),
            ProverKind::Metamath,
            vec!["test.mm".to_string()],
        );

        let job2 = ProofJob::new(
            Uuid::new_v4(),
            "def456".to_string(),
            ProverKind::Metamath,
            vec!["test2.mm".to_string()],
        );

        // Enqueue jobs
        assert!(scheduler.enqueue(job1).await.unwrap().is_some());
        assert!(scheduler.enqueue(job2).await.unwrap().is_some());

        // Start first job
        let started = scheduler.try_start_next().await;
        assert!(started.is_some());
        assert_eq!(started.unwrap().status, JobStatus::Running);

        // Stats should show 1 running, 1 queued
        let stats = scheduler.stats().await;
        assert_eq!(stats.running, 1);
        assert_eq!(stats.queued, 1);
    }

    #[tokio::test]
    async fn test_duplicate_detection() {
        let scheduler = JobScheduler::new(2, 10);
        let repo_id = Uuid::new_v4();

        let job1 = ProofJob::new(
            repo_id,
            "abc123".to_string(),
            ProverKind::Metamath,
            vec!["test.mm".to_string()],
        );

        let job2 = ProofJob::new(
            repo_id,
            "abc123".to_string(), // Same commit
            ProverKind::Metamath,  // Same prover
            vec!["test.mm".to_string()],
        );

        // First should succeed
        assert!(scheduler.enqueue(job1).await.unwrap().is_some());

        // Duplicate should be rejected
        assert!(scheduler.enqueue(job2).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_priority_ordering() {
        let scheduler = JobScheduler::new(1, 10);
        let repo_id = Uuid::new_v4();

        let low_priority = ProofJob::new(
            repo_id,
            "low".to_string(),
            ProverKind::Metamath,
            vec!["low.mm".to_string()],
        )
        .with_priority(JobPriority::Low);

        let high_priority = ProofJob::new(
            repo_id,
            "high".to_string(),
            ProverKind::Lean,
            vec!["high.lean".to_string()],
        )
        .with_priority(JobPriority::High);

        // Enqueue low priority first
        scheduler.enqueue(low_priority).await.unwrap();

        // Enqueue high priority second
        scheduler.enqueue(high_priority).await.unwrap();

        // High priority should come out first
        let started = scheduler.try_start_next().await.unwrap();
        assert_eq!(started.commit_sha, "high");
    }
}
