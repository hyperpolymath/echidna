// SPDX-License-Identifier: PMPL-1.0
//! Bitbucket platform adapter (minimal clone support)

use async_trait::async_trait;
use std::path::PathBuf;

use super::{
    CheckConclusion, CheckRun, CheckRunId, CheckStatus, CommentId, IssueId, NewIssue,
    PlatformAdapter, PrId, RepoId,
};
use crate::error::{Error, Result};

/// Bitbucket adapter (clone-only implementation)
pub struct BitbucketAdapter {
    base_url: String,
    token: Option<String>,
    client: reqwest::Client,
}

impl BitbucketAdapter {
    pub fn new(base_url: Option<&str>) -> Self {
        let base = base_url.unwrap_or("https://bitbucket.org");
        Self {
            base_url: base.trim_end_matches('/').to_string(),
            token: std::env::var("BITBUCKET_TOKEN").ok(),
            client: reqwest::Client::new(),
        }
    }

    fn repo_url(&self, repo: &RepoId) -> String {
        format!("{}/{}/{}.git", self.base_url, repo.owner, repo.name)
    }

    fn api_url(&self) -> String {
        "https://api.bitbucket.org/2.0".to_string()
    }

    fn project_path(&self, repo: &RepoId) -> String {
        format!("{}/{}", repo.owner, repo.name)
    }
}

#[async_trait]
impl PlatformAdapter for BitbucketAdapter {
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
                return Err(Error::Unsupported(format!(
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
            Error::Config("BITBUCKET_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let url = format!(
            "{}/repositories/{}/commit/{}/statuses/build",
            self.api_url(),
            project_path,
            check.head_sha
        );

        let (state, description) = match &check.status {
            CheckStatus::Completed { conclusion, summary } => {
                let state = match conclusion {
                    CheckConclusion::Success => "SUCCESSFUL",
                    CheckConclusion::Failure => "FAILED",
                    CheckConclusion::Cancelled => "STOPPED",
                    _ => "FAILED",
                };
                (state, summary.clone())
            }
            CheckStatus::InProgress => ("INPROGRESS", String::new()),
            CheckStatus::Queued => ("INPROGRESS", String::new()),
        };

        let payload = serde_json::json!({
            "state": state,
            "key": check.name,
            "description": description,
        });

        let response = self
            .client
            .post(&url)
            .bearer_auth(token)
            .json(&payload)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(CheckRunId(
            data["uuid"]
                .as_str()
                .unwrap_or("0")
                .to_string(),
        ))
    }

    async fn update_check_run(&self, _id: CheckRunId, _status: CheckStatus) -> Result<()> {
        // Bitbucket doesn't support updating build statuses after creation
        // To update, you would need to POST again with the same key
        Ok(())
    }

    async fn create_comment(&self, repo: &RepoId, pr: PrId, body: &str) -> Result<CommentId> {
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("BITBUCKET_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let url = format!(
            "{}/repositories/{}/pullrequests/{}/comments",
            self.api_url(),
            project_path,
            pr.0
        );

        let payload = serde_json::json!({
            "content": {
                "raw": body,
            },
        });

        let response = self
            .client
            .post(&url)
            .bearer_auth(token)
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
            Error::Config("BITBUCKET_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let url = format!(
            "{}/repositories/{}/issues",
            self.api_url(),
            project_path
        );

        let payload = serde_json::json!({
            "title": issue.title,
            "content": {
                "raw": issue.body,
            },
            "kind": "bug",  // Bitbucket requires a kind field
        });

        let response = self
            .client
            .post(&url)
            .bearer_auth(token)
            .json(&payload)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(IssueId(
            data["id"]
                .as_u64()
                .map(|id| id.to_string())
                .ok_or_else(|| Error::GitHub("Missing id in response".to_string()))?,
        ))
    }

    async fn get_default_branch(&self, repo: &RepoId) -> Result<String> {
        let token = self.token.as_ref().ok_or_else(|| {
            Error::Config("BITBUCKET_TOKEN not set".to_string())
        })?;

        let project_path = self.project_path(repo);
        let url = format!(
            "{}/repositories/{}",
            self.api_url(),
            project_path
        );

        let response = self
            .client
            .get(&url)
            .bearer_auth(token)
            .send()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        let data: serde_json::Value = response
            .json()
            .await
            .map_err(|e| Error::GitHub(e.to_string()))?;

        Ok(data["mainbranch"]["name"]
            .as_str()
            .ok_or_else(|| Error::GitHub("Missing mainbranch.name in response".to_string()))?
            .to_string())
    }
}
