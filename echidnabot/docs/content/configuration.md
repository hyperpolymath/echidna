---
title: Configuration Reference
date: 2025-01-01
template: default
---

# Configuration Reference

echidnabot is configured via TOML files and environment variables.

## Configuration Files

### echidnabot.toml

The main configuration file, located in your repository root or at `~/.config/echidnabot/config.toml`.

```toml
# Server configuration
[server]
host = "0.0.0.0"
port = 8080
workers = 4

# Database configuration
[database]
# SQLite (development)
url = "sqlite://echidnabot.db"

# PostgreSQL (production)
# url = "postgres://user:pass@localhost/echidnabot"

# ECHIDNA Core connection
[echidna]
endpoint = "https://echidna.example.com/graphql"
rest_endpoint = "https://echidna.example.com"
mode = "auto" # auto, graphql, rest
timeout_seconds = 300
retry_attempts = 3

# Logging
[logging]
level = "info"  # trace, debug, info, warn, error
format = "json" # json, pretty

# Job scheduler
[scheduler]
max_concurrent_jobs = 5
job_timeout_seconds = 600
queue_size = 100

# GitHub adapter
[github]
app_id = 12345
private_key_path = "/path/to/private-key.pem"
webhook_secret = "${GITHUB_WEBHOOK_SECRET}"

# GitLab adapter
[gitlab]
token = "${GITLAB_TOKEN}"
webhook_secret = "${GITLAB_WEBHOOK_SECRET}"
```

## Environment Variables

| Variable | Description | Required |
|----------|-------------|----------|
| `ECHIDNABOT_CONFIG` | Path to config file | No |
| `ECHIDNABOT_DATABASE_URL` | Database connection URL | Yes |
| `ECHIDNABOT_ECHIDNA_ENDPOINT` | ECHIDNA Core GraphQL endpoint | Yes |
| `ECHIDNABOT_ECHIDNA_REST_ENDPOINT` | ECHIDNA Core REST endpoint | No |
| `ECHIDNABOT_ECHIDNA_MODE` | ECHIDNA API mode (auto/graphql/rest) | No |
| `GITHUB_WEBHOOK_SECRET` | GitHub webhook secret | For GitHub |
| `GITHUB_APP_ID` | GitHub App ID | For GitHub |
| `GITHUB_PRIVATE_KEY` | GitHub App private key (PEM) | For GitHub |
| `GITLAB_TOKEN` | GitLab access token | For GitLab |
| `GITLAB_WEBHOOK_SECRET` | GitLab webhook secret | For GitLab |
| `RUST_LOG` | Log level override | No |

## Repository Configuration

Per-repository configuration in `.echidnabot.toml`:

```toml
# Enabled provers for this repository
[provers]
enabled = ["coq", "lean4", "agda"]

# Prover-specific settings
[provers.coq]
flags = ["-R", ".", "MyProject"]
timeout = 120

[provers.lean4]
lake = true

[provers.agda]
flags = ["--safe"]

# File patterns
[files]
include = ["src/**/*.v", "proofs/**/*.lean"]
exclude = ["vendor/**", "test/**"]

# Auto-check settings
[autocheck]
on_push = true
on_pull_request = true
branches = ["main", "develop"]

# Notifications
[notify]
on_failure = true
on_success = false
```

## CLI Configuration

```bash
# Set config path
export ECHIDNABOT_CONFIG=/path/to/config.toml

# Or pass directly
echidnabot --config /path/to/config.toml serve
```

## Docker Configuration

```yaml
version: "3.8"
services:
  echidnabot:
    image: ghcr.io/hyperpolymath/echidnabot:latest
    environment:
      - ECHIDNABOT_DATABASE_URL=postgres://user:pass@db/echidnabot
      - ECHIDNABOT_ECHIDNA_ENDPOINT=http://echidna:8080/graphql
      - GITHUB_WEBHOOK_SECRET=${GITHUB_WEBHOOK_SECRET}
    ports:
      - "8080:8080"
    volumes:
      - ./config:/etc/echidnabot
```
