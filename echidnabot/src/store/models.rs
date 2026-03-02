//! Database models

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::adapters::Platform;
use crate::dispatcher::ProverKind;
use crate::scheduler::{JobId, JobStatus, JobPriority};

/// Repository record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Repository {
    pub id: Uuid,
    pub platform: Platform,
    pub owner: String,
    pub name: String,
    pub webhook_secret: Option<String>,
    pub enabled_provers: Vec<ProverKind>,
    pub check_on_push: bool,
    pub check_on_pr: bool,
    pub auto_comment: bool,
    pub enabled: bool,
    pub last_checked_commit: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl Repository {
    pub fn new(platform: Platform, owner: String, name: String) -> Self {
        let now = Utc::now();
        Self {
            id: Uuid::new_v4(),
            platform,
            owner,
            name,
            webhook_secret: None,
            enabled_provers: vec![ProverKind::Metamath], // Default to easiest prover
            check_on_push: true,
            check_on_pr: true,
            auto_comment: true,
            enabled: true,
            last_checked_commit: None,
            created_at: now,
            updated_at: now,
        }
    }

    pub fn full_name(&self) -> String {
        format!("{}/{}", self.owner, self.name)
    }
}

/// Proof job database record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofJobRecord {
    pub id: Uuid,
    pub repo_id: Uuid,
    pub commit_sha: String,
    pub prover: ProverKind,
    pub file_paths: Vec<String>,
    pub status: JobStatus,
    pub priority: JobPriority,
    pub queued_at: DateTime<Utc>,
    pub started_at: Option<DateTime<Utc>>,
    pub completed_at: Option<DateTime<Utc>>,
    pub error_message: Option<String>,
}

impl From<crate::scheduler::ProofJob> for ProofJobRecord {
    fn from(job: crate::scheduler::ProofJob) -> Self {
        Self {
            id: job.id.0,
            repo_id: job.repo_id,
            commit_sha: job.commit_sha,
            prover: job.prover,
            file_paths: job.file_paths,
            status: job.status,
            priority: job.priority,
            queued_at: job.queued_at,
            started_at: job.started_at,
            completed_at: job.completed_at,
            error_message: job.result.as_ref().filter(|r| !r.success).map(|r| r.message.clone()),
        }
    }
}

/// Proof result database record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofResultRecord {
    pub id: Uuid,
    pub job_id: Uuid,
    pub success: bool,
    pub message: String,
    pub prover_output: String,
    pub duration_ms: i64,
    pub verified_files: Vec<String>,
    pub failed_files: Vec<String>,
    pub created_at: DateTime<Utc>,
}

impl ProofResultRecord {
    pub fn new(job_id: JobId, result: &crate::scheduler::JobResult) -> Self {
        Self {
            id: Uuid::new_v4(),
            job_id: job_id.0,
            success: result.success,
            message: result.message.clone(),
            prover_output: result.prover_output.clone(),
            duration_ms: result.duration_ms as i64,
            verified_files: result.verified_files.clone(),
            failed_files: result.failed_files.clone(),
            created_at: Utc::now(),
        }
    }
}

/// Check run record (for tracking GitHub/GitLab status updates)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckRunRecord {
    pub id: Uuid,
    pub job_id: Uuid,
    pub platform: Platform,
    pub external_id: String,  // Platform-specific ID
    pub status: String,
    pub conclusion: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}
