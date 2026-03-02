//! echidnabot CLI and server entry point

use clap::{Parser, Subcommand};
use echidnabot::{Config, Result};
use echidnabot::adapters::{Platform, PlatformAdapter, RepoId};
use echidnabot::adapters::bitbucket::BitbucketAdapter;
use echidnabot::adapters::github::GitHubAdapter;
use echidnabot::adapters::gitlab::GitLabAdapter;
use echidnabot::api::graphql::GraphQLState;
use echidnabot::api::{create_schema, webhook_router};
use echidnabot::dispatcher::{EchidnaClient, ProverKind};
use echidnabot::dispatcher::echidna_client::ProverStatus;
use echidnabot::scheduler::{JobScheduler, ProofJob};
use echidnabot::store::{SqliteStore, Store};
use echidnabot::store::models::{ProofResultRecord, Repository as StoreRepository};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;
use tokio::fs;
use tokio::time::{sleep, Duration};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[derive(Parser)]
#[command(name = "echidnabot")]
#[command(about = "Proof-aware CI bot for theorem prover repositories")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Path to configuration file
    #[arg(short, long, default_value = "echidnabot.toml")]
    config: String,

    /// Enable verbose logging
    #[arg(short, long)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// Start the webhook server
    Serve {
        /// Host to bind to
        #[arg(short = 'H', long, default_value = "0.0.0.0")]
        host: String,

        /// Port to bind to
        #[arg(short, long, default_value = "8080")]
        port: u16,
    },

    /// Register a repository for monitoring
    Register {
        /// Repository in format owner/name
        #[arg(short, long)]
        repo: String,

        /// Platform (github, gitlab, bitbucket)
        #[arg(short, long, default_value = "github")]
        platform: String,

        /// Provers to enable (comma-separated)
        #[arg(long, default_value = "metamath")]
        provers: String,
    },

    /// Manually trigger a proof check
    Check {
        /// Repository in format owner/name
        #[arg(short, long)]
        repo: String,

        /// Commit SHA (defaults to HEAD)
        #[arg(short, long)]
        commit: Option<String>,

        /// Specific prover to use
        #[arg(short, long)]
        prover: Option<String>,
    },

    /// Show status of a repository or job
    Status {
        /// Repository in format owner/name, or job ID
        #[arg(short, long)]
        target: String,
    },

    /// Initialize the database
    InitDb,
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize tracing
    let filter = if cli.verbose { "debug" } else { "info" };
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()))
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Load config
    let config = Config::load(&cli.config)?;

    match cli.command {
        Commands::Serve { host, port } => {
            tracing::info!("Starting echidnabot server on {}:{}", host, port);
            serve(&config, &host, port).await
        }
        Commands::Register {
            repo,
            platform,
            provers,
        } => {
            tracing::info!(
                "Registering {} on {} with provers: {}",
                repo,
                platform,
                provers
            );
            register(&config, &repo, &platform, &provers).await
        }
        Commands::Check {
            repo,
            commit,
            prover,
        } => {
            tracing::info!("Triggering check for {} at {:?}", repo, commit);
            check(&config, &repo, commit.as_deref(), prover.as_deref()).await
        }
        Commands::Status { target } => {
            tracing::info!("Getting status for {}", target);
            status(&config, &target).await
        }
        Commands::InitDb => {
            tracing::info!("Initializing database");
            init_db(&config).await
        }
    }
}

async fn serve(config: &Config, host: &str, port: u16) -> Result<()> {
    use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
    use axum::{Extension, routing::get, routing::post, Router};

    let store = Arc::new(SqliteStore::new(&config.database.url).await?);
    let scheduler = Arc::new(JobScheduler::new(
        config.scheduler.max_concurrent,
        config.scheduler.queue_size,
    ));
    let echidna = Arc::new(EchidnaClient::new(&config.echidna));

    let graphql_state = GraphQLState {
        store: store.clone(),
        scheduler: scheduler.clone(),
        echidna: echidna.clone(),
    };
    let schema = create_schema(graphql_state);

    let app_state = echidnabot::api::webhooks::AppState {
        config: Arc::new(config.clone()),
        store: store.clone(),
        scheduler: scheduler.clone(),
    };

    let app = Router::new()
        .route("/health", get(health))
        .route("/", get(root))
        .route(
            "/graphql",
            post(
                |Extension(schema): Extension<echidnabot::api::graphql::EchidnabotSchema>,
                 req: GraphQLRequest| async move {
                    GraphQLResponse::from(schema.execute(req.into_inner()).await)
                },
            )
            .get(graphql_playground),
        )
        .merge(webhook_router())
        .layer(Extension(schema))
        .with_state(app_state.clone());

    tokio::spawn(run_scheduler_loop(
        scheduler.clone(),
        store.clone(),
        echidna.clone(),
        app_state.config.clone(),
    ));

    let listener = tokio::net::TcpListener::bind(format!("{}:{}", host, port)).await?;
    tracing::info!("Listening on http://{}:{}", host, port);

    axum::serve(listener, app).await?;
    Ok(())
}

async fn graphql_playground() -> &'static str {
    r#"<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8" />
    <title>echidnabot GraphQL</title>
    <link rel="stylesheet" href="https://unpkg.com/@graphql-playground/react/build/static/css/index.css" />
    <link rel="shortcut icon" href="https://raw.githubusercontent.com/graphql/graphql-playground/master/packages/graphql-playground-react/public/favicon.png" />
    <script src="https://unpkg.com/@graphql-playground/react/build/static/js/middleware.js"></script>
  </head>
  <body>
    <div id="root"></div>
    <script>
      window.addEventListener("load", function () {
        GraphQLPlayground.init(document.getElementById("root"), { endpoint: "/graphql" });
      });
    </script>
  </body>
</html>"#
}

async fn health() -> &'static str {
    "OK"
}

async fn root() -> &'static str {
    "echidnabot - Proof-aware CI bot\n\nEndpoints:\n  GET  /health\n  GET  /graphql\n  POST /graphql\n  POST /webhooks/github\n  POST /webhooks/gitlab\n  POST /webhooks/bitbucket"
}

async fn register(config: &Config, repo: &str, platform: &str, provers: &str) -> Result<()> {
    let store = SqliteStore::new(&config.database.url).await?;
    let platform = parse_platform(platform)?;
    let (owner, name) = split_repo_name(repo)?;

    let mut repo_record = StoreRepository::new(platform, owner, name);
    let enabled = parse_prover_list(provers)?;
    if !enabled.is_empty() {
        repo_record.enabled_provers = enabled;
    }

    store.create_repository(&repo_record).await?;
    tracing::info!(
        "Registered repository {} on {:?}",
        repo_record.full_name(),
        repo_record.platform
    );
    Ok(())
}

async fn check(config: &Config, repo: &str, commit: Option<&str>, prover: Option<&str>) -> Result<()> {
    let client = EchidnaClient::new(&config.echidna);
    let health = client.health_check().await?;
    tracing::info!("ECHIDNA health check: {}", if health { "ok" } else { "unhealthy" });

    if !health {
        tracing::warn!("ECHIDNA reported unhealthy; results may be unreliable");
    }

    let repo_path = Path::new(repo);
    let (proof_content, inferred_prover) = if repo_path.is_file() {
        let content = fs::read_to_string(repo_path).await?;
        let detected = detect_prover_from_filename(repo_path);
        (Some(content), detected)
    } else {
        (None, None)
    };

    let selected_prover = prover
        .and_then(parse_prover_arg)
        .or(inferred_prover);

    if let Some(kind) = selected_prover {
        let status = client.prover_status(kind).await?;
        tracing::info!(
            "Prover {} status: {}",
            kind.display_name(),
            format_prover_status(status)
        );
    }

    if let Some(content) = proof_content {
        let kind = selected_prover.unwrap_or(ProverKind::Metamath);
        let result = client.verify_proof(kind, &content).await?;
        tracing::info!(
            "Proof result: {:?} ({} ms)",
            result.status,
            result.duration_ms
        );
        tracing::info!("Message: {}", result.message);
        if !result.prover_output.trim().is_empty() {
            tracing::info!("Prover output:\n{}", result.prover_output.trim());
        }
        if !result.artifacts.is_empty() {
            tracing::info!("Artifacts: {}", result.artifacts.join(", "));
        }
        if let Some(commit) = commit {
            tracing::info!("Checked commit {}", commit);
        }
    } else {
        tracing::warn!(
            "Repo '{}' is not a proof file; pass a local proof file path to run verification",
            repo
        );
    }

    Ok(())
}

fn parse_prover_arg(prover: &str) -> Option<ProverKind> {
    match prover.to_lowercase().as_str() {
        "agda" => Some(ProverKind::Agda),
        "coq" | "rocq" => Some(ProverKind::Coq),
        "lean" | "lean4" => Some(ProverKind::Lean),
        "isabelle" | "isabelle-hol" | "isabelle_hol" => Some(ProverKind::Isabelle),
        "z3" => Some(ProverKind::Z3),
        "cvc5" => Some(ProverKind::Cvc5),
        "metamath" => Some(ProverKind::Metamath),
        "hol-light" | "hol_light" | "hol" => Some(ProverKind::HolLight),
        "mizar" => Some(ProverKind::Mizar),
        "pvs" => Some(ProverKind::Pvs),
        "acl2" => Some(ProverKind::Acl2),
        "hol4" => Some(ProverKind::Hol4),
        _ => None,
    }
}

fn detect_prover_from_filename(path: &Path) -> Option<ProverKind> {
    let filename = path.file_name()?.to_str()?.to_lowercase();
    ProverKind::all().find(|prover| {
        prover
            .file_extensions()
            .iter()
            .any(|ext| filename.ends_with(ext))
    })
}

fn format_prover_status(status: ProverStatus) -> &'static str {
    match status {
        ProverStatus::Available => "available",
        ProverStatus::Degraded => "degraded",
        ProverStatus::Unavailable => "unavailable",
        ProverStatus::Unknown => "unknown",
    }
}

fn parse_platform(platform: &str) -> Result<Platform> {
    match platform.to_lowercase().as_str() {
        "github" => Ok(Platform::GitHub),
        "gitlab" => Ok(Platform::GitLab),
        "bitbucket" => Ok(Platform::Bitbucket),
        "codeberg" => Ok(Platform::Codeberg),
        _ => Err(echidnabot::Error::Config(format!(
            "Unknown platform '{}'",
            platform
        ))),
    }
}

fn split_repo_name(repo: &str) -> Result<(String, String)> {
    let mut parts = repo.splitn(2, '/');
    let owner = parts.next().unwrap_or_default().to_string();
    let name = parts.next().unwrap_or_default().to_string();
    if owner.is_empty() || name.is_empty() {
        return Err(echidnabot::Error::Config(
            "Repo must be in owner/name format".to_string(),
        ));
    }
    Ok((owner, name))
}

fn parse_prover_list(provers: &str) -> Result<Vec<ProverKind>> {
    let mut results = Vec::new();
    for prover in provers.split(',').map(str::trim).filter(|p| !p.is_empty()) {
        match parse_prover_arg(prover) {
            Some(kind) => results.push(kind),
            None => {
                return Err(echidnabot::Error::InvalidProver(prover.to_string()));
            }
        }
    }
    Ok(results)
}

async fn status(config: &Config, target: &str) -> Result<()> {
    let store = SqliteStore::new(&config.database.url).await?;

    if let Ok(job_id) = uuid::Uuid::parse_str(target) {
        if let Some(job) = store.get_job(echidnabot::scheduler::JobId(job_id)).await? {
            tracing::info!(
                "Job {} repo={} commit={} prover={:?} status={:?}",
                job.id,
                job.repo_id,
                job.commit_sha,
                job.prover,
                job.status
            );
            return Ok(());
        }
    }

    if let Ok((owner, name)) = split_repo_name(target) {
        if let Some(repo) = store
            .get_repository_by_name(Platform::GitHub, &owner, &name)
            .await?
        {
            tracing::info!(
                "Repository {} enabled={} last_checked={:?}",
                repo.full_name(),
                repo.enabled,
                repo.last_checked_commit
            );
            let jobs = store.list_jobs_for_repo(repo.id, 20).await?;
            tracing::info!("Recent jobs: {}", jobs.len());
            return Ok(());
        }
    }

    tracing::warn!("No matching job or repository found for '{}'", target);
    Ok(())
}

async fn init_db(config: &Config) -> Result<()> {
    let _store = SqliteStore::new(&config.database.url).await?;
    tracing::info!("Database initialized");
    Ok(())
}

async fn run_scheduler_loop(
    scheduler: Arc<JobScheduler>,
    store: Arc<dyn Store>,
    echidna: Arc<EchidnaClient>,
    config: Arc<Config>,
) {
    loop {
        if let Some(job) = scheduler.try_start_next().await {
            if let Err(err) = mark_job_running(store.as_ref(), &job).await {
                tracing::warn!("Failed to mark job {} running: {}", job.id, err);
            }

            let result = match process_job(&job, store.as_ref(), echidna.as_ref(), &config).await {
                Ok(result) => result,
                Err(err) => {
                    tracing::error!("Job {} failed: {}", job.id, err);
                    echidnabot::scheduler::JobResult {
                        success: false,
                        message: err.to_string(),
                        prover_output: String::new(),
                        duration_ms: 0,
                        verified_files: vec![],
                        failed_files: vec![],
                    }
                }
            };

            if let Err(err) = finalize_job(store.as_ref(), &job, &result).await {
                tracing::warn!("Failed to finalize job {}: {}", job.id, err);
            }

            scheduler
                .complete_job(job.id, result.success, result.message.clone())
                .await;
        } else {
            sleep(Duration::from_millis(250)).await;
        }
    }
}

async fn mark_job_running(store: &dyn Store, job: &ProofJob) -> Result<()> {
    let mut record = store
        .get_job(job.id)
        .await?
        .ok_or_else(|| echidnabot::Error::JobNotFound(job.id.0))?;
    record.status = echidnabot::scheduler::JobStatus::Running;
    record.started_at = Some(chrono::Utc::now());
    store.update_job(&record).await?;
    Ok(())
}

async fn finalize_job(
    store: &dyn Store,
    job: &ProofJob,
    result: &echidnabot::scheduler::JobResult,
) -> Result<()> {
    let mut record = store
        .get_job(job.id)
        .await?
        .ok_or_else(|| echidnabot::Error::JobNotFound(job.id.0))?;
    record.status = if result.success {
        echidnabot::scheduler::JobStatus::Completed
    } else {
        echidnabot::scheduler::JobStatus::Failed
    };
    record.completed_at = Some(chrono::Utc::now());
    record.error_message = if result.success {
        None
    } else {
        Some(result.message.clone())
    };
    store.update_job(&record).await?;

    let result_record = ProofResultRecord::new(job.id, result);
    store.save_result(&result_record).await?;

    if let Some(mut repo) = store.get_repository(job.repo_id).await? {
        repo.last_checked_commit = Some(job.commit_sha.clone());
        repo.updated_at = chrono::Utc::now();
        store.update_repository(&repo).await?;
    }
    Ok(())
}

async fn process_job(
    job: &ProofJob,
    store: &dyn Store,
    echidna: &EchidnaClient,
    config: &Config,
) -> Result<echidnabot::scheduler::JobResult> {
    let start = Instant::now();
    let healthy = echidna.health_check().await?;
    if !healthy {
        return Err(echidnabot::Error::Echidna(
            "ECHIDNA core reported unhealthy status".to_string(),
        ));
    }

    let status = echidna.prover_status(job.prover).await?;
    if status != ProverStatus::Available {
        return Err(echidnabot::Error::Echidna(format!(
            "Prover {} not available (status: {})",
            job.prover.display_name(),
            format_prover_status(status)
        )));
    }

    let repo = store
        .get_repository(job.repo_id)
        .await?
        .ok_or_else(|| echidnabot::Error::RepoNotFound(job.repo_id.to_string()))?;

    let repo_id = RepoId::new(repo.platform, repo.owner.clone(), repo.name.clone());
    let repo_path = clone_repo(config, &repo_id, &job.commit_sha).await?;

    let mut file_paths = job.file_paths.clone();
    if file_paths.is_empty() {
        let extensions: Vec<String> = job
            .prover
            .file_extensions()
            .iter()
            .map(|s| s.to_string())
            .collect();
        let repo_path_clone = repo_path.clone();
        file_paths = tokio::task::spawn_blocking(move || {
            collect_files_by_extension(&repo_path_clone, &extensions)
        })
        .await
        .unwrap_or_default()
        .into_iter()
        .map(|p| p.to_string_lossy().to_string())
        .collect();

        if let Some(mut record) = store.get_job(job.id).await? {
            record.file_paths = file_paths.clone();
            store.update_job(&record).await?;
        }
    }

    if file_paths.is_empty() {
        return Ok(echidnabot::scheduler::JobResult {
            success: false,
            message: "No proof files found for prover".to_string(),
            prover_output: String::new(),
            duration_ms: start.elapsed().as_millis() as u64,
            verified_files: vec![],
            failed_files: vec![],
        });
    }

    let mut verified = Vec::new();
    let mut failed = Vec::new();
    let mut prover_output = String::new();

    for path in &file_paths {
        let full_path = if Path::new(path).is_absolute() {
            PathBuf::from(path)
        } else {
            repo_path.join(path)
        };
        let content = fs::read_to_string(&full_path).await?;
        let result = echidna.verify_proof(job.prover, &content).await?;
        if result.status == echidnabot::dispatcher::ProofStatus::Verified {
            verified.push(path.to_string());
        } else {
            failed.push(path.to_string());
        }
        if !result.prover_output.trim().is_empty() {
            prover_output.push_str(&result.prover_output);
            prover_output.push('\n');
        }
    }

    let success = failed.is_empty();
    let message = if success {
        format!("Verified {} file(s)", verified.len())
    } else {
        format!("Failed {} file(s)", failed.len())
    };

    Ok(echidnabot::scheduler::JobResult {
        success,
        message,
        prover_output,
        duration_ms: start.elapsed().as_millis() as u64,
        verified_files: verified,
        failed_files: failed,
    })
}

async fn clone_repo(config: &Config, repo: &RepoId, commit: &str) -> Result<PathBuf> {
    match repo.platform {
        Platform::GitHub => {
            if let Some(ref gh) = config.github {
                if let Some(ref token) = gh.token {
                    let adapter = GitHubAdapter::new(token)?;
                    return adapter.clone_repo(repo, commit).await;
                }
            }
            clone_repo_via_git("https://github.com", repo, commit).await
        }
        Platform::GitLab => {
            let adapter = GitLabAdapter::new(config.gitlab.as_ref().map(|g| g.url.as_str()));
            adapter.clone_repo(repo, commit).await
        }
        Platform::Bitbucket => {
            let adapter = BitbucketAdapter::new(None);
            adapter.clone_repo(repo, commit).await
        }
        Platform::Codeberg => clone_repo_via_git("https://codeberg.org", repo, commit).await,
    }
}

async fn clone_repo_via_git(base_url: &str, repo: &RepoId, commit: &str) -> Result<PathBuf> {
    let temp_dir = tempfile::tempdir()?;
    let clone_path = temp_dir.keep();
    let url = format!("{}/{}/{}.git", base_url.trim_end_matches('/'), repo.owner, repo.name);

    let status = if commit == "HEAD" {
        tokio::process::Command::new("git")
            .args(["clone", "--depth", "1", &url, clone_path.to_str().unwrap()])
            .status()
            .await?
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
            .await?
    };

    if !status.success() && commit != "HEAD" {
        let status = tokio::process::Command::new("git")
            .args(["clone", "--depth", "1", &url, clone_path.to_str().unwrap()])
            .status()
            .await?;

        if !status.success() {
            return Err(echidnabot::Error::Internal(format!(
                "Failed to clone {}",
                repo.full_name()
            )));
        }

        tokio::process::Command::new("git")
            .current_dir(&clone_path)
            .args(["fetch", "--depth", "1", "origin", commit])
            .status()
            .await?;

        tokio::process::Command::new("git")
            .current_dir(&clone_path)
            .args(["checkout", commit])
            .status()
            .await?;
    }

    Ok(clone_path)
}

fn collect_files_by_extension(root: &Path, extensions: &[String]) -> Vec<PathBuf> {
    let mut results = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return results;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if let Some(name) = path.file_name().and_then(|s| s.to_str()) {
                if name == ".git" || name == "target" {
                    continue;
                }
            }
            results.extend(collect_files_by_extension(&path, extensions));
        } else if let Some(name) = path.file_name().and_then(|s| s.to_str()) {
            if extensions.iter().any(|ext| name.ends_with(ext)) {
                results.push(path);
            }
        }
    }
    results
}
