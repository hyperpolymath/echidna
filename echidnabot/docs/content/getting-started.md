---
title: Getting Started
date: 2025-01-01
template: default
---

# Getting Started with echidnabot

This guide walks you through setting up echidnabot for your repository.

## Prerequisites

- A GitHub, GitLab, or Bitbucket repository
- Proof files in a supported format (Coq, Lean, Agda, etc.)
- Access to an ECHIDNA Core instance

## Installation

### From Cargo

```bash
cargo install echidnabot
```

### From Source

```bash
git clone https://github.com/hyperpolymath/echidnabot
cd echidnabot
cargo build --release
```

### Using Guix

```bash
guix install echidnabot
```

## Configuration

Create an `echidnabot.toml` in your repository root:

```toml
[repository]
platform = "github"
owner = "your-org"
name = "your-repo"

[provers]
enabled = ["coq", "lean4", "agda"]

[webhook]
secret = "${ECHIDNABOT_WEBHOOK_SECRET}"

[echidna]
endpoint = "https://echidna.example.com/graphql"
rest_endpoint = "https://echidna.example.com"
mode = "auto"
```

## Setting Up Webhooks

### GitHub

1. Go to Repository Settings → Webhooks
2. Add webhook URL: `https://your-echidnabot-instance/webhooks/github`
3. Content type: `application/json`
4. Secret: Your configured webhook secret
5. Events: Push, Pull Request

### GitLab

1. Go to Settings → Webhooks
2. URL: `https://your-echidnabot-instance/webhooks/gitlab`
3. Secret token: Your configured webhook secret
4. Triggers: Push events, Merge request events

## Verifying Setup

```bash
# Check echidnabot status
echidnabot status

# Trigger a test verification
echidnabot check --commit HEAD --dry-run
```

## Next Steps

- [Configuration Reference](./configuration.md)
- [API Documentation](./api.md)
- [Prover Setup](./provers.md)
