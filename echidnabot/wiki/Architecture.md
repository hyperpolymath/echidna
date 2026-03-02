# Architecture

echidnabot is designed as a modular, async Rust application that orchestrates proof verification between code platforms and the ECHIDNA theorem proving backend.

## System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    CODE PLATFORMS                            │
│    GitHub          GitLab          Bitbucket       Codeberg  │
└──────────┬────────────┬───────────────┬──────────────┬──────┘
           │            │               │              │
           │  webhooks  │               │              │
           ▼            ▼               ▼              ▼
┌─────────────────────────────────────────────────────────────┐
│                      ECHIDNABOT                              │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                  Webhook Server (Axum)                  ││
│  │  POST /webhooks/github   POST /webhooks/gitlab    ...   ││
│  └─────────────────────────────────────────────────────────┘│
│                            │                                 │
│                            ▼                                 │
│  ┌─────────────────────────────────────────────────────────┐│
│  │              Platform Adapters                          ││
│  │  ┌─────────┐  ┌─────────┐  ┌───────────┐  ┌──────────┐ ││
│  │  │ GitHub  │  │ GitLab  │  │ Bitbucket │  │ Codeberg │ ││
│  │  │(Octocrab)│  │         │  │           │  │          │ ││
│  │  └─────────┘  └─────────┘  └───────────┘  └──────────┘ ││
│  └─────────────────────────────────────────────────────────┘│
│                            │                                 │
│                            ▼                                 │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                 Job Scheduler (Tokio)                   ││
│  │  Priority Queue │ Concurrency Control │ Retry Logic    ││
│  └─────────────────────────────────────────────────────────┘│
│                            │                                 │
│                            ▼                                 │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                Proof Dispatcher                         ││
│  │  File Detection │ Prover Selection │ Result Parsing    ││
│  └─────────────────────────────────────────────────────────┘│
│                            │                                 │
│         ┌──────────────────┼──────────────────┐             │
│         ▼                  ▼                  ▼             │
│  ┌───────────┐      ┌───────────┐      ┌───────────┐       │
│  │  GraphQL  │      │   Store   │      │   Cache   │       │
│  │    API    │      │(SQLx/PG)  │      │           │       │
│  └───────────┘      └───────────┘      └───────────┘       │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ GraphQL/HTTP
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                     ECHIDNA CORE                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                    Prover Backends                      ││
│  │  ┌─────┐ ┌─────┐ ┌──────┐ ┌─────────┐ ┌────┐ ┌───────┐ ││
│  │  │ Coq │ │Lean4│ │ Agda │ │Isabelle │ │ Z3 │ │Metamath│ ││
│  │  └─────┘ └─────┘ └──────┘ └─────────┘ └────┘ └───────┘ ││
│  └─────────────────────────────────────────────────────────┘│
│  ┌─────────────────────────────────────────────────────────┐│
│  │              Julia ML (Tactic Suggestions)              ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Webhook Server (`src/api/webhooks.rs`)

Receives HTTP webhooks from code platforms. Validates signatures (HMAC-SHA256), parses payloads, and routes to appropriate handlers.

```rust
// Simplified flow
async fn handle_github_webhook(
    signature: HeaderValue,
    payload: Bytes,
) -> Result<Response, Error> {
    verify_signature(&signature, &payload, &secret)?;
    let event: GitHubEvent = serde_json::from_slice(&payload)?;

    match event {
        GitHubEvent::Push(push) => handle_push(push).await,
        GitHubEvent::PullRequest(pr) => handle_pr(pr).await,
        _ => Ok(StatusCode::OK),
    }
}
```

### 2. Platform Adapters (`src/adapters/`)

Abstract the differences between code platforms. Each adapter implements a common trait:

```rust
#[async_trait]
pub trait PlatformAdapter: Send + Sync {
    async fn create_check_run(&self, repo: &Repo, sha: &str) -> Result<CheckRun>;
    async fn update_check_run(&self, run: &CheckRun, result: &JobResult) -> Result<()>;
    async fn post_comment(&self, pr: &PullRequest, body: &str) -> Result<()>;
    async fn get_file_content(&self, repo: &Repo, path: &str, sha: &str) -> Result<String>;
}
```

### 3. Job Scheduler (`src/scheduler/`)

Manages the proof verification queue with:

- **Priority queue** — PRs prioritized over pushes
- **Concurrency control** — Configurable parallel job limit
- **Retry logic** — Exponential backoff for transient failures
- **Timeout handling** — Jobs killed after configurable timeout

```rust
pub struct JobScheduler {
    queue: PriorityQueue<ProofJob>,
    workers: Vec<JoinHandle<()>>,
    max_concurrent: usize,
    semaphore: Arc<Semaphore>,
}
```

### 4. Proof Dispatcher (`src/dispatcher/`)

Communicates with ECHIDNA Core:

```rust
pub struct EchidnaClient {
    endpoint: Url,
    client: reqwest::Client,
}

impl EchidnaClient {
    pub async fn verify_proof(
        &self,
        prover: ProverKind,
        content: &str,
    ) -> Result<VerificationResult> {
        let query = r#"
            mutation VerifyProof($prover: Prover!, $content: String!) {
                verifyProof(prover: $prover, content: $content) {
                    success
                    message
                    errors { line, column, message }
                }
            }
        "#;
        // ...
    }
}
```

### 5. GraphQL API (`src/api/graphql.rs`)

Exposes query and mutation endpoints for external control:

```graphql
type Query {
    repository(platform: Platform!, owner: String!, name: String!): Repository
    job(id: ID!): ProofJob
    availableProvers: [ProverInfo!]!
}

type Mutation {
    registerRepository(input: RegisterRepoInput!): Repository!
    triggerCheck(repoId: ID!, commitSha: String!): ProofJob!
}
```

### 6. Data Store (`src/store/`)

SQLx-based persistence supporting SQLite (dev) and PostgreSQL (prod):

```rust
pub struct Repository {
    pub id: Uuid,
    pub platform: Platform,
    pub owner: String,
    pub name: String,
    pub enabled_provers: Vec<ProverKind>,
    pub webhook_secret: Option<String>,
    pub created_at: DateTime<Utc>,
}

pub struct ProofJob {
    pub id: Uuid,
    pub repo_id: Uuid,
    pub commit_sha: String,
    pub prover: ProverKind,
    pub status: JobStatus,
    pub priority: JobPriority,
    pub queued_at: DateTime<Utc>,
    pub started_at: Option<DateTime<Utc>>,
    pub completed_at: Option<DateTime<Utc>>,
    pub result: Option<JobResult>,
}
```

## Technology Stack

| Component | Technology | Why |
|-----------|------------|-----|
| Language | Rust | Memory safety, performance, async |
| Async Runtime | Tokio | Best-in-class async ecosystem |
| HTTP Framework | Axum 0.7 | Modern, tower-based, type-safe |
| GraphQL | async-graphql | Native async, great DX |
| Database | SQLx | Compile-time checked queries |
| GitHub API | Octocrab | Native Rust, well-maintained |
| HTTP Client | Reqwest | De facto standard |
| Crypto | sha2, hmac | Audited, pure Rust |

## Data Flow

### Webhook to Verification

```
1. GitHub sends POST /webhooks/github
2. Webhook handler validates HMAC signature
3. Event parsed, proof files identified
4. ProofJob created with appropriate priority
5. Job enqueued to scheduler
6. Scheduler assigns to worker when capacity available
7. Worker sends to ECHIDNA via dispatcher
8. Result received, Check Run updated
9. Job marked complete in database
```

### API to Verification

```
1. Client sends GraphQL mutation triggerCheck
2. Repository looked up, commit SHA validated
3. ProofJob created (high priority for manual triggers)
4. Same flow as webhook from step 4
5. Job ID returned immediately
6. Client can poll job query for status
```

## Scaling Considerations

### Horizontal Scaling

- Stateless webhook handlers
- Database-backed job queue
- Multiple worker instances with semaphore coordination

### Caching

- Proof result caching by content hash
- Repository metadata caching
- Prover availability caching

### Rate Limiting

- Per-repository job limits
- Platform API rate limit respect
- ECHIDNA Core request throttling

## Security Model

### Webhook Verification

All incoming webhooks verified with HMAC-SHA256 before processing.

### Secret Management

- Webhook secrets: environment variables
- Database credentials: environment variables
- GitHub App private keys: file path in config

### Network Security

- HTTPS only for all external communication
- mTLS optional for ECHIDNA Core communication
- No HTTP URLs permitted per RSR policy
