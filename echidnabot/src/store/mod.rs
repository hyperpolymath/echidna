//! Persistent state store

pub mod models;
mod sqlite;

pub use sqlite::SqliteStore;

use async_trait::async_trait;
use uuid::Uuid;

use crate::adapters::Platform;
use crate::error::Result;
use crate::scheduler::JobId;
use models::{Repository, ProofJobRecord, ProofResultRecord};

/// Abstract store trait for different database backends
#[async_trait]
pub trait Store: Send + Sync {
    // Repository operations
    async fn create_repository(&self, repo: &Repository) -> Result<()>;
    async fn get_repository(&self, id: Uuid) -> Result<Option<Repository>>;
    async fn get_repository_by_name(
        &self,
        platform: Platform,
        owner: &str,
        name: &str,
    ) -> Result<Option<Repository>>;
    async fn list_repositories(&self, platform: Option<Platform>) -> Result<Vec<Repository>>;
    async fn update_repository(&self, repo: &Repository) -> Result<()>;
    async fn delete_repository(&self, id: Uuid) -> Result<()>;

    // Job operations
    async fn create_job(&self, job: &ProofJobRecord) -> Result<()>;
    async fn get_job(&self, id: JobId) -> Result<Option<ProofJobRecord>>;
    async fn update_job(&self, job: &ProofJobRecord) -> Result<()>;
    async fn list_jobs_for_repo(&self, repo_id: Uuid, limit: usize) -> Result<Vec<ProofJobRecord>>;
    async fn list_pending_jobs(&self, limit: usize) -> Result<Vec<ProofJobRecord>>;

    // Result operations
    async fn save_result(&self, result: &ProofResultRecord) -> Result<()>;
    async fn get_result_for_job(&self, job_id: JobId) -> Result<Option<ProofResultRecord>>;

    // Utility
    async fn health_check(&self) -> Result<bool>;
}
