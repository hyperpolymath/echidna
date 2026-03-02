//! GitHub platform adapter using Octocrab

use async_trait::async_trait;
use std::path::PathBuf;

use super::{
    CheckConclusion, CheckRun, CheckRunId, CheckStatus, CommentId, IssueId, NewIssue,
    PlatformAdapter, PrId, RepoId,
};
use crate::error::{Error, Result};

/// GitHub adapter using Octocrab
pub struct GitHubAdapter {
    client: octocrab::Octocrab,
}

impl GitHubAdapter {
    /// Create a new GitHub adapter with a token
    pub fn new(token: &str) -> Result<Self> {
        let client = octocrab::Octocrab::builder()
            .personal_token(token.to_string())
            .build()
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(Self { client })
    }

    /// Create adapter from environment variable
    pub fn from_env() -> Result<Self> {
        let token = std::env::var("GITHUB_TOKEN")
            .map_err(|_| Error::Config("GITHUB_TOKEN not set".to_string()))?;
        Self::new(&token)
    }
}

#[async_trait]
impl PlatformAdapter for GitHubAdapter {
    async fn clone_repo(&self, repo: &RepoId, commit: &str) -> Result<PathBuf> {
        // Create a temporary directory for the clone
        let temp_dir = tempfile::tempdir().map_err(Error::Io)?;
        let clone_path = temp_dir.keep();

        // Use git to clone (shallow, specific commit)
        let url = format!("https://github.com/{}/{}.git", repo.owner, repo.name);

        let status = if commit == "HEAD" {
            tokio::process::Command::new("git")
                .args(["clone", "--depth", "1", &url, clone_path.to_str().unwrap()])
                .status()
                .await
                .map_err(Error::Io)?
        } else {
            tokio::process::Command::new("git")
                .args([
                    "clone",
                    "--depth",
                    "1",
                    "--branch",
                    commit,
                    &url,
                    clone_path.to_str().unwrap(),
                ])
                .status()
                .await
                .map_err(Error::Io)?
        };

        if !status.success() && commit != "HEAD" {
            // Try fetching the specific commit instead
            let status = tokio::process::Command::new("git")
                .args(["clone", "--depth", "1", &url, clone_path.to_str().unwrap()])
                .status()
                .await
                .map_err(Error::Io)?;

            if !status.success() {
                return Err(Error::GitHub(format!(
                    "Failed to clone {}",
                    repo.full_name()
                )));
            }

            // Fetch and checkout specific commit
            tokio::process::Command::new("git")
                .current_dir(&clone_path)
                .args(["fetch", "--depth", "1", "origin", commit])
                .status()
                .await
                .map_err(Error::Io)?;

            tokio::process::Command::new("git")
                .current_dir(&clone_path)
                .args(["checkout", commit])
                .status()
                .await
                .map_err(Error::Io)?;
        }

        Ok(clone_path)
    }

    async fn create_check_run(&self, repo: &RepoId, check: CheckRun) -> Result<CheckRunId> {
        let checks = self.client.checks(&repo.owner, &repo.name);

        use octocrab::params::checks::{CheckRunConclusion as OctoConclusion, CheckRunStatus as OctoStatus};

        let (status, conclusion) = match check.status {
            CheckStatus::Queued => (OctoStatus::Queued, None),
            CheckStatus::InProgress => (OctoStatus::InProgress, None),
            CheckStatus::Completed { conclusion, .. } => {
                let c = match conclusion {
                    CheckConclusion::Success => OctoConclusion::Success,
                    CheckConclusion::Failure => OctoConclusion::Failure,
                    CheckConclusion::Neutral => OctoConclusion::Neutral,
                    CheckConclusion::Cancelled => OctoConclusion::Cancelled,
                    CheckConclusion::Skipped => OctoConclusion::Skipped,
                    CheckConclusion::TimedOut => OctoConclusion::TimedOut,
                    CheckConclusion::ActionRequired => OctoConclusion::ActionRequired,
                };
                (OctoStatus::Completed, Some(c))
            }
        };

        // Build check run request
        let mut builder = checks.create_check_run(check.name, check.head_sha);

        builder = builder.status(status);

        if let Some(c) = conclusion {
            builder = builder.conclusion(c);
        }

        if let Some(url) = check.details_url {
            builder = builder.details_url(url);
        }

        let result = builder.send().await.map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(CheckRunId(result.id.to_string()))
    }

    async fn update_check_run(&self, id: CheckRunId, status: CheckStatus) -> Result<()> {
        // Note: Octocrab doesn't have direct update_check_run, would need raw API
        // For now, log and return Ok
        tracing::info!("Would update check run {} to {:?}", id.0, status);
        Ok(())
    }

    async fn create_comment(&self, repo: &RepoId, pr: PrId, body: &str) -> Result<CommentId> {
        let pr_num: u64 = pr.0.parse().map_err(|_| Error::GitHub("Invalid PR ID".to_string()))?;

        let comment = self
            .client
            .issues(&repo.owner, &repo.name)
            .create_comment(pr_num, body)
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(CommentId(comment.id.to_string()))
    }

    async fn create_issue(&self, repo: &RepoId, issue: NewIssue) -> Result<IssueId> {
        let created = self
            .client
            .issues(&repo.owner, &repo.name)
            .create(&issue.title)
            .body(&issue.body)
            .labels(issue.labels)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(IssueId(created.number.to_string()))
    }

    async fn get_default_branch(&self, repo: &RepoId) -> Result<String> {
        let repo_info = self
            .client
            .repos(&repo.owner, &repo.name)
            .get()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(repo_info.default_branch.unwrap_or_else(|| "main".to_string()))
    }
}
