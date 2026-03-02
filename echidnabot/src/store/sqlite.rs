//! SQLite store implementation

use async_trait::async_trait;
use sqlx::{sqlite::SqlitePoolOptions, Pool, Sqlite};
use uuid::Uuid;

use super::{models::*, Store};
use crate::adapters::Platform;
use crate::dispatcher::ProverKind;
use crate::error::{Error, Result};
use crate::scheduler::JobId;

/// SQLite-backed store
pub struct SqliteStore {
    pool: Pool<Sqlite>,
}

impl SqliteStore {
    /// Create a new SQLite store
    pub async fn new(database_url: &str) -> Result<Self> {
        let pool = SqlitePoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;

        let store = Self { pool };
        store.run_migrations().await?;

        Ok(store)
    }

    /// Run database migrations
    async fn run_migrations(&self) -> Result<()> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS repositories (
                id TEXT PRIMARY KEY,
                platform TEXT NOT NULL,
                owner TEXT NOT NULL,
                name TEXT NOT NULL,
                webhook_secret TEXT,
                enabled_provers TEXT NOT NULL,
                check_on_push INTEGER NOT NULL DEFAULT 1,
                check_on_pr INTEGER NOT NULL DEFAULT 1,
                auto_comment INTEGER NOT NULL DEFAULT 1,
                enabled INTEGER NOT NULL DEFAULT 1,
                last_checked_commit TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE(platform, owner, name)
            )
            "#,
        )
        .execute(&self.pool)
        .await?;

        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS proof_jobs (
                id TEXT PRIMARY KEY,
                repo_id TEXT NOT NULL REFERENCES repositories(id),
                commit_sha TEXT NOT NULL,
                prover TEXT NOT NULL,
                file_paths TEXT NOT NULL,
                status TEXT NOT NULL,
                priority INTEGER NOT NULL DEFAULT 1,
                queued_at TEXT NOT NULL,
                started_at TEXT,
                completed_at TEXT,
                error_message TEXT
            )
            "#,
        )
        .execute(&self.pool)
        .await?;

        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS proof_results (
                id TEXT PRIMARY KEY,
                job_id TEXT NOT NULL REFERENCES proof_jobs(id),
                success INTEGER NOT NULL,
                message TEXT NOT NULL,
                prover_output TEXT NOT NULL,
                duration_ms INTEGER NOT NULL,
                verified_files TEXT NOT NULL,
                failed_files TEXT NOT NULL,
                created_at TEXT NOT NULL
            )
            "#,
        )
        .execute(&self.pool)
        .await?;

        sqlx::query(
            r#"
            CREATE INDEX IF NOT EXISTS idx_jobs_repo_id ON proof_jobs(repo_id);
            "#,
        )
        .execute(&self.pool)
        .await?;

        sqlx::query(
            r#"
            CREATE INDEX IF NOT EXISTS idx_jobs_status ON proof_jobs(status);
            "#,
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }
}

#[async_trait]
impl Store for SqliteStore {
    async fn create_repository(&self, repo: &Repository) -> Result<()> {
        let enabled_provers = serde_json::to_string(&repo.enabled_provers)?;

        sqlx::query(
            r#"
            INSERT INTO repositories (
                id, platform, owner, name, webhook_secret, enabled_provers,
                check_on_push, check_on_pr, auto_comment, enabled,
                last_checked_commit, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            "#,
        )
        .bind(repo.id.to_string())
        .bind(format!("{:?}", repo.platform))
        .bind(&repo.owner)
        .bind(&repo.name)
        .bind(&repo.webhook_secret)
        .bind(&enabled_provers)
        .bind(repo.check_on_push)
        .bind(repo.check_on_pr)
        .bind(repo.auto_comment)
        .bind(repo.enabled)
        .bind(&repo.last_checked_commit)
        .bind(repo.created_at.to_rfc3339())
        .bind(repo.updated_at.to_rfc3339())
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn get_repository(&self, id: Uuid) -> Result<Option<Repository>> {
        let row: Option<RepoRow> = sqlx::query_as(
            "SELECT * FROM repositories WHERE id = ?",
        )
        .bind(id.to_string())
        .fetch_optional(&self.pool)
        .await?;

        row.map(|r| r.try_into()).transpose()
    }

    async fn get_repository_by_name(
        &self,
        platform: Platform,
        owner: &str,
        name: &str,
    ) -> Result<Option<Repository>> {
        let row: Option<RepoRow> = sqlx::query_as(
            "SELECT * FROM repositories WHERE platform = ? AND owner = ? AND name = ?",
        )
        .bind(format!("{:?}", platform))
        .bind(owner)
        .bind(name)
        .fetch_optional(&self.pool)
        .await?;

        row.map(|r| r.try_into()).transpose()
    }

    async fn list_repositories(&self, platform: Option<Platform>) -> Result<Vec<Repository>> {
        let rows: Vec<RepoRow> = match platform {
            Some(p) => {
                sqlx::query_as("SELECT * FROM repositories WHERE platform = ? ORDER BY created_at DESC")
                    .bind(format!("{:?}", p))
                    .fetch_all(&self.pool)
                    .await?
            }
            None => {
                sqlx::query_as("SELECT * FROM repositories ORDER BY created_at DESC")
                    .fetch_all(&self.pool)
                    .await?
            }
        };

        rows.into_iter().map(|r| r.try_into()).collect()
    }

    async fn update_repository(&self, repo: &Repository) -> Result<()> {
        let enabled_provers = serde_json::to_string(&repo.enabled_provers)?;

        sqlx::query(
            r#"
            UPDATE repositories SET
                webhook_secret = ?,
                enabled_provers = ?,
                check_on_push = ?,
                check_on_pr = ?,
                auto_comment = ?,
                enabled = ?,
                last_checked_commit = ?,
                updated_at = ?
            WHERE id = ?
            "#,
        )
        .bind(&repo.webhook_secret)
        .bind(&enabled_provers)
        .bind(repo.check_on_push)
        .bind(repo.check_on_pr)
        .bind(repo.auto_comment)
        .bind(repo.enabled)
        .bind(&repo.last_checked_commit)
        .bind(repo.updated_at.to_rfc3339())
        .bind(repo.id.to_string())
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn delete_repository(&self, id: Uuid) -> Result<()> {
        sqlx::query("DELETE FROM repositories WHERE id = ?")
            .bind(id.to_string())
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    async fn create_job(&self, job: &ProofJobRecord) -> Result<()> {
        let file_paths = serde_json::to_string(&job.file_paths)?;

        sqlx::query(
            r#"
            INSERT INTO proof_jobs (
                id, repo_id, commit_sha, prover, file_paths,
                status, priority, queued_at, started_at, completed_at, error_message
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            "#,
        )
        .bind(job.id.to_string())
        .bind(job.repo_id.to_string())
        .bind(&job.commit_sha)
        .bind(format!("{:?}", job.prover))
        .bind(&file_paths)
        .bind(format!("{:?}", job.status))
        .bind(job.priority as i32)
        .bind(job.queued_at.to_rfc3339())
        .bind(job.started_at.map(|t| t.to_rfc3339()))
        .bind(job.completed_at.map(|t| t.to_rfc3339()))
        .bind(&job.error_message)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn get_job(&self, id: JobId) -> Result<Option<ProofJobRecord>> {
        let row: Option<JobRow> = sqlx::query_as(
            "SELECT * FROM proof_jobs WHERE id = ?",
        )
        .bind(id.0.to_string())
        .fetch_optional(&self.pool)
        .await?;

        row.map(|r| r.try_into()).transpose()
    }

    async fn update_job(&self, job: &ProofJobRecord) -> Result<()> {
        sqlx::query(
            r#"
            UPDATE proof_jobs SET
                status = ?,
                started_at = ?,
                completed_at = ?,
                error_message = ?
            WHERE id = ?
            "#,
        )
        .bind(format!("{:?}", job.status))
        .bind(job.started_at.map(|t| t.to_rfc3339()))
        .bind(job.completed_at.map(|t| t.to_rfc3339()))
        .bind(&job.error_message)
        .bind(job.id.to_string())
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn list_jobs_for_repo(&self, repo_id: Uuid, limit: usize) -> Result<Vec<ProofJobRecord>> {
        let rows: Vec<JobRow> = sqlx::query_as(
            "SELECT * FROM proof_jobs WHERE repo_id = ? ORDER BY queued_at DESC LIMIT ?",
        )
        .bind(repo_id.to_string())
        .bind(limit as i64)
        .fetch_all(&self.pool)
        .await?;

        rows.into_iter().map(|r| r.try_into()).collect()
    }

    async fn list_pending_jobs(&self, limit: usize) -> Result<Vec<ProofJobRecord>> {
        let rows: Vec<JobRow> = sqlx::query_as(
            "SELECT * FROM proof_jobs WHERE status = 'Queued' ORDER BY priority DESC, queued_at ASC LIMIT ?",
        )
        .bind(limit as i64)
        .fetch_all(&self.pool)
        .await?;

        rows.into_iter().map(|r| r.try_into()).collect()
    }

    async fn save_result(&self, result: &ProofResultRecord) -> Result<()> {
        let verified_files = serde_json::to_string(&result.verified_files)?;
        let failed_files = serde_json::to_string(&result.failed_files)?;

        sqlx::query(
            r#"
            INSERT INTO proof_results (
                id, job_id, success, message, prover_output,
                duration_ms, verified_files, failed_files, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            "#,
        )
        .bind(result.id.to_string())
        .bind(result.job_id.to_string())
        .bind(result.success)
        .bind(&result.message)
        .bind(&result.prover_output)
        .bind(result.duration_ms)
        .bind(&verified_files)
        .bind(&failed_files)
        .bind(result.created_at.to_rfc3339())
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn get_result_for_job(&self, job_id: JobId) -> Result<Option<ProofResultRecord>> {
        let row: Option<ResultRow> = sqlx::query_as(
            "SELECT * FROM proof_results WHERE job_id = ?",
        )
        .bind(job_id.0.to_string())
        .fetch_optional(&self.pool)
        .await?;

        row.map(|r| r.try_into()).transpose()
    }

    async fn health_check(&self) -> Result<bool> {
        let result: (i32,) = sqlx::query_as("SELECT 1")
            .fetch_one(&self.pool)
            .await?;
        Ok(result.0 == 1)
    }
}

// =============================================================================
// Row types for sqlx
// =============================================================================

#[derive(sqlx::FromRow)]
struct RepoRow {
    id: String,
    platform: String,
    owner: String,
    name: String,
    webhook_secret: Option<String>,
    enabled_provers: String,
    check_on_push: bool,
    check_on_pr: bool,
    auto_comment: bool,
    enabled: bool,
    last_checked_commit: Option<String>,
    created_at: String,
    updated_at: String,
}

impl TryFrom<RepoRow> for Repository {
    type Error = Error;

    fn try_from(row: RepoRow) -> Result<Self> {
        let platform = match row.platform.as_str() {
            "GitHub" => Platform::GitHub,
            "GitLab" => Platform::GitLab,
            "Bitbucket" => Platform::Bitbucket,
            "Codeberg" => Platform::Codeberg,
            _ => return Err(Error::Internal(format!("Unknown platform: {}", row.platform))),
        };

        let enabled_provers: Vec<ProverKind> = serde_json::from_str(&row.enabled_provers)?;

        Ok(Repository {
            id: Uuid::parse_str(&row.id).map_err(|e| Error::Internal(e.to_string()))?,
            platform,
            owner: row.owner,
            name: row.name,
            webhook_secret: row.webhook_secret,
            enabled_provers,
            check_on_push: row.check_on_push,
            check_on_pr: row.check_on_pr,
            auto_comment: row.auto_comment,
            enabled: row.enabled,
            last_checked_commit: row.last_checked_commit,
            created_at: chrono::DateTime::parse_from_rfc3339(&row.created_at)
                .map_err(|e| Error::Internal(e.to_string()))?
                .with_timezone(&chrono::Utc),
            updated_at: chrono::DateTime::parse_from_rfc3339(&row.updated_at)
                .map_err(|e| Error::Internal(e.to_string()))?
                .with_timezone(&chrono::Utc),
        })
    }
}

#[derive(sqlx::FromRow)]
struct JobRow {
    id: String,
    repo_id: String,
    commit_sha: String,
    prover: String,
    file_paths: String,
    status: String,
    priority: i32,
    queued_at: String,
    started_at: Option<String>,
    completed_at: Option<String>,
    error_message: Option<String>,
}

impl TryFrom<JobRow> for ProofJobRecord {
    type Error = Error;

    fn try_from(row: JobRow) -> Result<Self> {
        use crate::scheduler::{JobPriority, JobStatus};

        let prover = parse_prover(&row.prover)?;
        let status = match row.status.as_str() {
            "Queued" => JobStatus::Queued,
            "Running" => JobStatus::Running,
            "Completed" => JobStatus::Completed,
            "Failed" => JobStatus::Failed,
            "Cancelled" => JobStatus::Cancelled,
            _ => return Err(Error::Internal(format!("Unknown status: {}", row.status))),
        };
        let priority = match row.priority {
            0 => JobPriority::Low,
            1 => JobPriority::Normal,
            2 => JobPriority::High,
            3 => JobPriority::Critical,
            _ => JobPriority::Normal,
        };
        let file_paths: Vec<String> = serde_json::from_str(&row.file_paths)?;

        Ok(ProofJobRecord {
            id: Uuid::parse_str(&row.id).map_err(|e| Error::Internal(e.to_string()))?,
            repo_id: Uuid::parse_str(&row.repo_id).map_err(|e| Error::Internal(e.to_string()))?,
            commit_sha: row.commit_sha,
            prover,
            file_paths,
            status,
            priority,
            queued_at: chrono::DateTime::parse_from_rfc3339(&row.queued_at)
                .map_err(|e| Error::Internal(e.to_string()))?
                .with_timezone(&chrono::Utc),
            started_at: row.started_at.map(|s| {
                chrono::DateTime::parse_from_rfc3339(&s)
                    .map(|t| t.with_timezone(&chrono::Utc))
            }).transpose().map_err(|e| Error::Internal(e.to_string()))?,
            completed_at: row.completed_at.map(|s| {
                chrono::DateTime::parse_from_rfc3339(&s)
                    .map(|t| t.with_timezone(&chrono::Utc))
            }).transpose().map_err(|e| Error::Internal(e.to_string()))?,
            error_message: row.error_message,
        })
    }
}

#[derive(sqlx::FromRow)]
struct ResultRow {
    id: String,
    job_id: String,
    success: bool,
    message: String,
    prover_output: String,
    duration_ms: i64,
    verified_files: String,
    failed_files: String,
    created_at: String,
}

impl TryFrom<ResultRow> for ProofResultRecord {
    type Error = Error;

    fn try_from(row: ResultRow) -> Result<Self> {
        let verified_files: Vec<String> = serde_json::from_str(&row.verified_files)?;
        let failed_files: Vec<String> = serde_json::from_str(&row.failed_files)?;

        Ok(ProofResultRecord {
            id: Uuid::parse_str(&row.id).map_err(|e| Error::Internal(e.to_string()))?,
            job_id: Uuid::parse_str(&row.job_id).map_err(|e| Error::Internal(e.to_string()))?,
            success: row.success,
            message: row.message,
            prover_output: row.prover_output,
            duration_ms: row.duration_ms,
            verified_files,
            failed_files,
            created_at: chrono::DateTime::parse_from_rfc3339(&row.created_at)
                .map_err(|e| Error::Internal(e.to_string()))?
                .with_timezone(&chrono::Utc),
        })
    }
}

fn parse_prover(s: &str) -> Result<ProverKind> {
    match s {
        "Agda" => Ok(ProverKind::Agda),
        "Coq" => Ok(ProverKind::Coq),
        "Lean" => Ok(ProverKind::Lean),
        "Isabelle" => Ok(ProverKind::Isabelle),
        "Z3" => Ok(ProverKind::Z3),
        "Cvc5" => Ok(ProverKind::Cvc5),
        "Metamath" => Ok(ProverKind::Metamath),
        "HolLight" => Ok(ProverKind::HolLight),
        "Mizar" => Ok(ProverKind::Mizar),
        "Pvs" => Ok(ProverKind::Pvs),
        "Acl2" => Ok(ProverKind::Acl2),
        "Hol4" => Ok(ProverKind::Hol4),
        _ => Err(Error::InvalidProver(s.to_string())),
    }
}
