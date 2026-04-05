// SPDX-License-Identifier: PMPL-1.0
//! Platform adapters for GitHub, GitLab, Bitbucket

use serde::{Deserialize, Serialize};

pub mod github;
pub mod gitlab;
pub mod bitbucket;

use async_trait::async_trait;
use std::path::PathBuf;

use crate::error::Result;

/// Unique identifier for a repository
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RepoId {
    pub platform: Platform,
    pub owner: String,
    pub name: String,
}

impl RepoId {
    pub fn new(platform: Platform, owner: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            platform,
            owner: owner.into(),
            name: name.into(),
        }
    }

    pub fn full_name(&self) -> String {
        format!("{}/{}", self.owner, self.name)
    }
}

/// Platform enum
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Platform {
    GitHub,
    GitLab,
    Bitbucket,
    Codeberg,
}

/// Check run identifier
#[derive(Debug, Clone)]
pub struct CheckRunId(pub String);

/// Comment identifier
#[derive(Debug, Clone)]
pub struct CommentId(pub String);

/// Issue identifier
#[derive(Debug, Clone)]
pub struct IssueId(pub String);

/// Pull request identifier
#[derive(Debug, Clone)]
pub struct PrId(pub String);

/// Check run status
#[derive(Debug, Clone)]
pub enum CheckStatus {
    Queued,
    InProgress,
    Completed {
        conclusion: CheckConclusion,
        summary: String,
    },
}

/// Check run conclusion
#[derive(Debug, Clone)]
pub enum CheckConclusion {
    Success,
    Failure,
    Neutral,
    Cancelled,
    Skipped,
    TimedOut,
    ActionRequired,
}

/// Check run to create
#[derive(Debug, Clone)]
pub struct CheckRun {
    pub name: String,
    pub head_sha: String,
    pub status: CheckStatus,
    pub details_url: Option<String>,
}

/// Issue to create
#[derive(Debug, Clone)]
pub struct NewIssue {
    pub title: String,
    pub body: String,
    pub labels: Vec<String>,
}

/// Platform adapter trait
///
/// Abstracts operations across GitHub, GitLab, Bitbucket
#[async_trait]
pub trait PlatformAdapter: Send + Sync {
    /// Clone a repository to a local path
    async fn clone_repo(&self, repo: &RepoId, commit: &str) -> Result<PathBuf>;

    /// Create a check run (GitHub) or pipeline status (GitLab)
    async fn create_check_run(&self, repo: &RepoId, check: CheckRun) -> Result<CheckRunId>;

    /// Update a check run status
    async fn update_check_run(&self, id: CheckRunId, status: CheckStatus) -> Result<()>;

    /// Create a comment on a PR/MR
    async fn create_comment(&self, repo: &RepoId, pr: PrId, body: &str) -> Result<CommentId>;

    /// Create an issue
    async fn create_issue(&self, repo: &RepoId, issue: NewIssue) -> Result<IssueId>;

    /// Get the default branch name
    async fn get_default_branch(&self, repo: &RepoId) -> Result<String>;
}
