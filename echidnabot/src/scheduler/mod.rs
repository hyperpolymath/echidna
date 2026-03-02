//! Job scheduler for proof verification tasks

pub mod job_queue;

pub use job_queue::JobScheduler;

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::dispatcher::ProverKind;

/// Unique job identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct JobId(pub Uuid);

impl JobId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

impl Default for JobId {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for JobId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Proof verification job
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofJob {
    pub id: JobId,
    pub repo_id: Uuid,
    pub commit_sha: String,
    pub prover: ProverKind,
    pub file_paths: Vec<String>,
    pub status: JobStatus,
    pub priority: JobPriority,
    pub queued_at: DateTime<Utc>,
    pub started_at: Option<DateTime<Utc>>,
    pub completed_at: Option<DateTime<Utc>>,
    pub result: Option<JobResult>,
}

impl ProofJob {
    pub fn new(repo_id: Uuid, commit_sha: String, prover: ProverKind, file_paths: Vec<String>) -> Self {
        Self {
            id: JobId::new(),
            repo_id,
            commit_sha,
            prover,
            file_paths,
            status: JobStatus::Queued,
            priority: JobPriority::Normal,
            queued_at: Utc::now(),
            started_at: None,
            completed_at: None,
            result: None,
        }
    }

    /// Create a high-priority job (e.g., for PR checks)
    pub fn with_priority(mut self, priority: JobPriority) -> Self {
        self.priority = priority;
        self
    }

    /// Mark as started
    pub fn start(&mut self) {
        self.status = JobStatus::Running;
        self.started_at = Some(Utc::now());
    }

    /// Mark as completed
    pub fn complete(&mut self, result: JobResult) {
        self.status = match result.success {
            true => JobStatus::Completed,
            false => JobStatus::Failed,
        };
        self.completed_at = Some(Utc::now());
        self.result = Some(result);
    }

    /// Mark as cancelled
    pub fn cancel(&mut self) {
        self.status = JobStatus::Cancelled;
        self.completed_at = Some(Utc::now());
    }

    /// Get duration in milliseconds (if completed)
    pub fn duration_ms(&self) -> Option<u64> {
        match (self.started_at, self.completed_at) {
            (Some(start), Some(end)) => {
                Some((end - start).num_milliseconds().max(0) as u64)
            }
            _ => None,
        }
    }
}

/// Job execution status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum JobStatus {
    Queued,
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// Job priority for queue ordering
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum JobPriority {
    Low = 0,
    Normal = 1,
    High = 2,     // PR checks
    Critical = 3, // Manual triggers
}

/// Result of a completed job
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JobResult {
    pub success: bool,
    pub message: String,
    pub prover_output: String,
    pub duration_ms: u64,
    pub verified_files: Vec<String>,
    pub failed_files: Vec<String>,
}
