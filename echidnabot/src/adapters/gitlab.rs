// SPDX-License-Identifier: PMPL-1.0-or-later
//! GitLab platform adapter (minimal clone support)

use async_trait::async_trait;
use std::path::PathBuf;

use super::{
    CheckRun, CheckRunId, CheckStatus, CommentId, IssueId, NewIssue, PlatformAdapter, PrId, RepoId,
};
use crate::error::{Error, Result};

/// GitLab adapter (clone-only implementation)
pub struct GitLabAdapter {
    base_url: String,
}

impl GitLabAdapter {
    pub fn new(base_url: Option<&str>) -> Self {
        let base = base_url.unwrap_or("https://gitlab.com");
        Self {
            base_url: base.trim_end_matches('/').to_string(),
        }
    }

    fn repo_url(&self, repo: &RepoId) -> String {
        format!("{}/{}/{}.git", self.base_url, repo.owner, repo.name)
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

    async fn create_check_run(&self, _repo: &RepoId, _check: CheckRun) -> Result<CheckRunId> {
        Err(Error::Unsupported(
            "GitLab check runs are not implemented".to_string(),
        ))
    }

    async fn update_check_run(&self, _id: CheckRunId, _status: CheckStatus) -> Result<()> {
        Err(Error::Unsupported(
            "GitLab check runs are not implemented".to_string(),
        ))
    }

    async fn create_comment(&self, _repo: &RepoId, _pr: PrId, _body: &str) -> Result<CommentId> {
        Err(Error::Unsupported(
            "GitLab comments are not implemented".to_string(),
        ))
    }

    async fn create_issue(&self, _repo: &RepoId, _issue: NewIssue) -> Result<IssueId> {
        Err(Error::Unsupported(
            "GitLab issues are not implemented".to_string(),
        ))
    }

    async fn get_default_branch(&self, _repo: &RepoId) -> Result<String> {
        Err(Error::Unsupported(
            "GitLab default branch lookup is not implemented".to_string(),
        ))
    }
}
