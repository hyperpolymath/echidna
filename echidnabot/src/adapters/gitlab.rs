// SPDX-License-Identifier: PMPL-1.0
//! GitLab platform adapter (minimal clone support)

use async_trait::async_trait;
use std::path::PathBuf;

use super::{
    CheckConclusion, CheckRun, CheckRunId, CheckStatus, CommentId, IssueId, NewIssue,
    PlatformAdapter, PrId, RepoId,
};
use crate::error::{Error, Result};

/// GitLab adapter (clone-only implementation)
pub struct GitLabAdapter {
    base_url: String,
    token: Option<String>,
    client: reqwest::Client,
}

impl GitLabAdapter {
    pub fn new(base_url: Option<&str>) -> Self {
        let base = base_url.unwrap_or("https://gitlab.com");
        Self {
            base_url: base.trim_end_matches('/').to_string(),
            token: std::env::var("GITLAB_TOKEN").ok(),
            client: reqwest::Client::new(),
        }
    }

    fn repo_url(&self, repo: &RepoId) -> String {
        format!("{}/{}/{}.git", self.base_url, repo.owner, repo.name)
    }

    fn api_url(&self) -> String {
        format!("{}/api/v4", self.base_url)
    }

    fn project_path(&self, repo: &RepoId) -> String {
        format!("{}/{}", repo.owner, repo.name)
    }
}

#[async_trait]
impl PlatformAdapter for GitLabAdapter {
    async fn clone_repo(&self, repo: &RepoId, commit: &str) -> Result<PathBuf> {
        let temp_dir = tempfile::tempdir().map_err(Error::Io)?;
        let clone_path = temp_dir.keep();

        let url = self.repo_url(repo);

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
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("GITLAB_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let encoded_project = urlencoding::encode(&project_path);
        let url = format!(
            "{}/projects/{}/statuses/{}",
            self.api_url(),
            encoded_project,
            check.head_sha
        );

        let (state, description) = match &check.status {
            CheckStatus::Completed { conclusion, summary } => {
                let state = match conclusion {
                    CheckConclusion::Success => "success",
                    CheckConclusion::Failure => "failed",
                    CheckConclusion::Cancelled => "canceled",
                    _ => "failed",
                };
                (state, summary.clone())
            }
            CheckStatus::InProgress => ("running", String::new()),
            CheckStatus::Queued => ("pending", String::new()),
        };

        let payload = serde_json::json!({
            "state": state,
            "name": check.name,
            "description": description,
        });

        let response = self
            .client
            .post(&url)
            .header("PRIVATE-TOKEN", token)
            .json(&payload)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(CheckRunId(
            data["id"]
                .as_u64()
                .map(|id| id.to_string())
                .ok_or_else(|| Error::GitHub("Missing id in response".to_string()))?,
        ))
    }

    async fn update_check_run(&self, _id: CheckRunId, _status: CheckStatus) -> Result<()> {
        // GitLab doesn't support updating commit statuses after creation
        Ok(())
    }

    async fn create_comment(&self, repo: &RepoId, pr: PrId, body: &str) -> Result<CommentId> {
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("GITLAB_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let encoded_project = urlencoding::encode(&project_path);
        let url = format!(
            "{}/projects/{}/merge_requests/{}/notes",
            self.api_url(),
            encoded_project,
            pr.0
        );

        let payload = serde_json::json!({
            "body": body,
        });

        let response = self
            .client
            .post(&url)
            .header("PRIVATE-TOKEN", token)
            .json(&payload)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(CommentId(
            data["id"]
                .as_u64()
                .map(|id| id.to_string())
                .ok_or_else(|| Error::GitHub("Missing id in response".to_string()))?,
        ))
    }

    async fn create_issue(&self, repo: &RepoId, issue: NewIssue) -> Result<IssueId> {
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("GITLAB_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let encoded_project = urlencoding::encode(&project_path);
        let url = format!(
            "{}/projects/{}/issues",
            self.api_url(),
            encoded_project
        );

        let payload = serde_json::json!({
            "title": issue.title,
            "description": issue.body,
            "labels": issue.labels.join(","),
        });

        let response = self
            .client
            .post(&url)
            .header("PRIVATE-TOKEN", token)
            .json(&payload)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(IssueId(
            data["iid"]
                .as_u64()
                .map(|id| id.to_string())
                .ok_or_else(|| Error::GitHub("Missing iid in response".to_string()))?,
        ))
    }

    async fn get_default_branch(&self, repo: &RepoId) -> Result<String> {
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("GITLAB_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let encoded_project = urlencoding::encode(&project_path);
        let url = format!(
            "{}/projects/{}",
            self.api_url(),
            encoded_project
        );

        let response = self
            .client
            .get(&url)
            .header("PRIVATE-TOKEN", token)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(data["default_branch"]
            .as_str()
            .ok_or_else(|| Error::GitHub("Missing default_branch in response".to_string()))?
            .to_string())
    }
}
