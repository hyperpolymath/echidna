//! Webhook handlers for GitHub, GitLab, and Bitbucket

use axum::{
    body::Bytes,
    extract::State,
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
    routing::post,
    Router,
};
use hmac::{Hmac, Mac};
use sha2::Sha256;
use std::sync::Arc;

use serde::Deserialize;

use crate::adapters::Platform;
use crate::config::Config;
use crate::error::Result;
use crate::scheduler::{JobPriority, JobScheduler, ProofJob};
use crate::store::{Store};
use crate::store::models::ProofJobRecord;

/// Application state shared across handlers
#[derive(Clone)]
pub struct AppState {
    pub config: Arc<Config>,
    pub store: Arc<dyn Store>,
    pub scheduler: Arc<JobScheduler>,
}

/// Create webhook router
pub fn webhook_router() -> Router<AppState> {
    Router::new()
        .route("/webhooks/github", post(handle_github_webhook))
        .route("/webhooks/gitlab", post(handle_gitlab_webhook))
        .route("/webhooks/bitbucket", post(handle_bitbucket_webhook))
}

/// GitHub webhook handler
async fn handle_github_webhook(
    State(state): State<AppState>,
    headers: HeaderMap,
    body: Bytes,
) -> impl IntoResponse {
    tracing::info!("Received GitHub webhook");

    // Verify signature if secret is configured
    if let Some(ref gh_config) = state.config.github {
        if let Some(ref secret) = gh_config.webhook_secret {
            if let Err(e) = verify_github_signature(&headers, &body, secret) {
                tracing::warn!("GitHub webhook signature verification failed: {}", e);
                return (StatusCode::UNAUTHORIZED, "Invalid signature");
            }
        }
    }

    // Parse event type
    let event_type = headers
        .get("X-GitHub-Event")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("unknown");

    tracing::info!("GitHub event type: {}", event_type);

    match event_type {
        "push" => {
            tracing::info!("Received push event");
            if let Ok(payload) = serde_json::from_slice::<GitHubPushPayload>(&body) {
                let (owner, name) = split_full_name(&payload.repository.full_name);
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::GitHub,
                    &owner,
                    &name,
                    &payload.after,
                    JobPriority::Normal,
                    RepoEventKind::Push,
                )
                .await;
            }
        }
        "pull_request" => {
            tracing::info!("Received pull_request event");
            if let Ok(payload) = serde_json::from_slice::<GitHubPullRequestPayload>(&body) {
                let (owner, name) = split_full_name(&payload.repository.full_name);
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::GitHub,
                    &owner,
                    &name,
                    &payload.pull_request.head.sha,
                    JobPriority::High,
                    RepoEventKind::PullRequest,
                )
                .await;
            }
        }
        "check_suite" => {
            tracing::info!("Received check_suite event");
            if let Ok(payload) = serde_json::from_slice::<GitHubCheckSuitePayload>(&body) {
                let (owner, name) = split_full_name(&payload.repository.full_name);
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::GitHub,
                    &owner,
                    &name,
                    &payload.check_suite.head_sha,
                    JobPriority::High,
                    RepoEventKind::PullRequest,
                )
                .await;
            }
        }
        "ping" => {
            tracing::info!("Received ping event - webhook configured correctly");
        }
        _ => {
            tracing::debug!("Ignoring event type: {}", event_type);
        }
    }

    (StatusCode::OK, "OK")
}

/// GitLab webhook handler
async fn handle_gitlab_webhook(
    State(state): State<AppState>,
    headers: HeaderMap,
    body: Bytes,
) -> impl IntoResponse {
    tracing::info!("Received GitLab webhook");

    // Verify token if configured
    if let Some(ref gl_config) = state.config.gitlab {
        if let Some(ref secret) = gl_config.webhook_secret {
            let token = headers
                .get("X-Gitlab-Token")
                .and_then(|v| v.to_str().ok())
                .unwrap_or("");

            if token != secret {
                tracing::warn!("GitLab webhook token mismatch");
                return (StatusCode::UNAUTHORIZED, "Invalid token");
            }
        }
    }

    // Parse event type
    let event_type = headers
        .get("X-Gitlab-Event")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("unknown");

    tracing::info!("GitLab event type: {}", event_type);

    match event_type {
        "Push Hook" => {
            tracing::info!("Received push hook");
            if let Ok(payload) = serde_json::from_slice::<GitLabPushPayload>(&body) {
                let (owner, name) = split_full_name(&payload.project.path_with_namespace);
                let commit = payload.checkout_sha.unwrap_or_else(|| payload.after);
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::GitLab,
                    &owner,
                    &name,
                    &commit,
                    JobPriority::Normal,
                    RepoEventKind::Push,
                )
                .await;
            }
        }
        "Merge Request Hook" => {
            tracing::info!("Received merge request hook");
            if let Ok(payload) = serde_json::from_slice::<GitLabMergeRequestPayload>(&body) {
                let (owner, name) = split_full_name(&payload.project.path_with_namespace);
                let commit = payload
                    .object_attributes
                    .last_commit
                    .map(|c| c.id)
                    .unwrap_or_else(|| payload.object_attributes.last_commit_id);
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::GitLab,
                    &owner,
                    &name,
                    &commit,
                    JobPriority::High,
                    RepoEventKind::PullRequest,
                )
                .await;
            }
        }
        _ => {
            tracing::debug!("Ignoring event type: {}", event_type);
        }
    }

    (StatusCode::OK, "OK")
}

/// Bitbucket webhook handler
async fn handle_bitbucket_webhook(
    State(state): State<AppState>,
    headers: HeaderMap,
    body: Bytes,
) -> impl IntoResponse {
    tracing::info!("Received Bitbucket webhook");

    let event_type = headers
        .get("X-Event-Key")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("unknown");

    tracing::info!("Bitbucket event type: {}", event_type);

    if event_type.starts_with("repo:push") {
        if let Ok(payload) = serde_json::from_slice::<BitbucketPushPayload>(&body) {
            let (owner, name) = split_full_name(&payload.repository.full_name);
            if let Some(commit) = payload
                .push
                .changes
                .first()
                .and_then(|c| c.new_target.as_ref())
                .map(|t| t.hash.clone())
            {
                let _ = enqueue_repo_jobs(
                    &state,
                    Platform::Bitbucket,
                    &owner,
                    &name,
                    &commit,
                    JobPriority::Normal,
                    RepoEventKind::Push,
                )
                .await;
            }
        }
    }

    (StatusCode::OK, "OK")
}

#[derive(Clone, Copy)]
enum RepoEventKind {
    Push,
    PullRequest,
}

async fn enqueue_repo_jobs(
    state: &AppState,
    platform: Platform,
    owner: &str,
    name: &str,
    commit: &str,
    priority: JobPriority,
    event_kind: RepoEventKind,
) -> Result<()> {
    let repo = match state
        .store
        .get_repository_by_name(platform, owner, name)
        .await?
    {
        Some(repo) => repo,
        None => {
            tracing::info!("Repository not registered: {}/{}", owner, name);
            return Ok(());
        }
    };

    if !repo.enabled {
        tracing::info!("Repository {} is disabled", repo.full_name());
        return Ok(());
    }

    let should_enqueue = match event_kind {
        RepoEventKind::Push => repo.check_on_push,
        RepoEventKind::PullRequest => repo.check_on_pr,
    };

    if !should_enqueue {
        return Ok(());
    }

    for prover in &repo.enabled_provers {
        let job = ProofJob::new(repo.id, commit.to_string(), *prover, Vec::new())
            .with_priority(priority);
        let record = ProofJobRecord::from(job.clone());
        state.store.create_job(&record).await?;
        let _ = state.scheduler.enqueue(job).await?;
    }

    Ok(())
}

fn split_full_name(full_name: &str) -> (String, String) {
    let mut parts = full_name.splitn(2, '/');
    let owner = parts.next().unwrap_or_default().to_string();
    let name = parts.next().unwrap_or_default().to_string();
    (owner, name)
}

#[derive(Deserialize)]
struct GitHubPushPayload {
    after: String,
    repository: GitHubRepo,
}

#[derive(Deserialize)]
struct GitHubPullRequestPayload {
    pull_request: GitHubPullRequest,
    repository: GitHubRepo,
}

#[derive(Deserialize)]
struct GitHubCheckSuitePayload {
    check_suite: GitHubCheckSuite,
    repository: GitHubRepo,
}

#[derive(Deserialize)]
struct GitHubRepo {
    full_name: String,
}

#[derive(Deserialize)]
struct GitHubPullRequest {
    head: GitHubHead,
}

#[derive(Deserialize)]
struct GitHubCheckSuite {
    head_sha: String,
}

#[derive(Deserialize)]
struct GitHubHead {
    sha: String,
}

#[derive(Deserialize)]
struct GitLabPushPayload {
    after: String,
    checkout_sha: Option<String>,
    project: GitLabProject,
}

#[derive(Deserialize)]
struct GitLabMergeRequestPayload {
    object_attributes: GitLabMergeAttributes,
    project: GitLabProject,
}

#[derive(Deserialize)]
struct GitLabMergeAttributes {
    last_commit_id: String,
    last_commit: Option<GitLabCommit>,
}

#[derive(Deserialize)]
struct GitLabCommit {
    id: String,
}

#[derive(Deserialize)]
struct GitLabProject {
    path_with_namespace: String,
}

#[derive(Deserialize)]
struct BitbucketPushPayload {
    repository: BitbucketRepo,
    push: BitbucketPush,
}

#[derive(Deserialize)]
struct BitbucketRepo {
    full_name: String,
}

#[derive(Deserialize)]
struct BitbucketPush {
    changes: Vec<BitbucketChange>,
}

#[derive(Deserialize)]
struct BitbucketChange {
    #[serde(rename = "new")]
    new_target: Option<BitbucketTarget>,
}

#[derive(Deserialize)]
struct BitbucketTarget {
    hash: String,
}

/// Verify GitHub webhook signature (HMAC-SHA256)
fn verify_github_signature(
    headers: &HeaderMap,
    body: &Bytes,
    secret: &str,
) -> std::result::Result<(), String> {
    let signature = headers
        .get("X-Hub-Signature-256")
        .and_then(|v| v.to_str().ok())
        .ok_or_else(|| "Missing X-Hub-Signature-256 header".to_string())?;

    // Signature format: "sha256=<hex>"
    let signature = signature
        .strip_prefix("sha256=")
        .ok_or_else(|| "Invalid signature format".to_string())?;

    let signature_bytes =
        hex::decode(signature).map_err(|_| "Invalid hex in signature".to_string())?;

    // Compute expected signature
    let mut mac = Hmac::<Sha256>::new_from_slice(secret.as_bytes())
        .map_err(|_| "Invalid secret key".to_string())?;
    mac.update(body);

    mac.verify_slice(&signature_bytes)
        .map_err(|_| "Signature mismatch".to_string())?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_github_signature() {
        let secret = "test-secret";
        let body = Bytes::from(r#"{"test": "payload"}"#);

        // Compute expected signature
        let mut mac = Hmac::<Sha256>::new_from_slice(secret.as_bytes()).unwrap();
        mac.update(&body);
        let expected = hex::encode(mac.finalize().into_bytes());

        let mut headers = HeaderMap::new();
        headers.insert(
            "X-Hub-Signature-256",
            format!("sha256={}", expected).parse().unwrap(),
        );

        assert!(verify_github_signature(&headers, &body, secret).is_ok());
    }
}
