# Getting Started with echidnabot

This guide walks you through installing, configuring, and using echidnabot for your repositories.

## Prerequisites

- A repository on GitHub, GitLab, or Bitbucket
- Proof files in a supported format (Coq, Lean, Agda, etc.)
- Either:
  - Access to an ECHIDNA Core instance, or
  - Local installation of theorem provers

## Installation

### Option 1: From Cargo (Recommended)

```bash
cargo install echidnabot
```

### Option 2: From Source

```bash
git clone https://github.com/hyperpolymath/echidnabot
cd echidnabot
cargo build --release
sudo cp target/release/echidnabot /usr/local/bin/
```

### Option 3: Using Guix

```bash
guix install echidnabot
```

### Option 4: Using Nix

```bash
nix profile install github:hyperpolymath/echidnabot
```

### Option 5: Docker/Podman

```bash
podman pull ghcr.io/hyperpolymath/echidnabot:latest
podman run -p 8080:8080 ghcr.io/hyperpolymath/echidnabot:latest
```

## Quick Start

### 1. Create Configuration

Create `echidnabot.toml` in your repository root:

```toml
[repository]
platform = "github"
owner = "your-org"
name = "your-repo"

[provers]
enabled = ["coq", "lean4"]

[echidna]
# Use public instance or self-host
endpoint = "https://echidna.hyperpolymath.dev/graphql"
```

### 2. Set Up Webhook

#### GitHub

1. Go to **Settings → Webhooks → Add webhook**
2. Payload URL: `https://your-echidnabot-instance/webhooks/github`
3. Content type: `application/json`
4. Secret: Generate and save securely
5. Events: Select **Pushes** and **Pull requests**

#### GitLab

1. Go to **Settings → Webhooks**
2. URL: `https://your-echidnabot-instance/webhooks/gitlab`
3. Secret token: Generate and save
4. Triggers: Push events, Merge request events

### 3. Test It

Push a commit with a proof file:

```bash
# Create a simple Coq proof
cat > test.v << 'EOF'
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.
EOF

git add test.v
git commit -m "Add commutativity proof"
git push
```

Check your PR or commit status — you should see echidnabot verification results!

## Configuration Options

### Repository Settings

```toml
[repository]
platform = "github"  # github, gitlab, bitbucket, codeberg
owner = "org-name"
name = "repo-name"
default_branch = "main"
```

### Prover Settings

```toml
[provers]
enabled = ["coq", "lean4", "agda", "z3"]

[provers.coq]
timeout = 120
flags = ["-R", ".", "MyProject"]

[provers.lean4]
lake = true  # Use lake build system

[provers.agda]
flags = ["--safe"]
```

### File Patterns

```toml
[files]
include = [
  "src/**/*.v",
  "proofs/**/*.lean",
  "specs/**/*.agda"
]
exclude = [
  "vendor/**",
  "test/fixtures/**"
]
```

### Auto-Check Settings

```toml
[autocheck]
on_push = true
on_pull_request = true
branches = ["main", "develop"]
require_passing = true  # Block merge on failure
```

## Bot Modes

echidnabot can operate in different modes:

| Mode | Behavior |
|------|----------|
| `verifier` | Silent pass/fail, minimal output |
| `advisor` | Suggestions on failing proofs |
| `consultant` | Answers questions about proof state |
| `regulator` | Blocks merges on proof failures |

Set the mode in configuration:

```toml
[bot]
mode = "advisor"
```

## CLI Commands

```bash
# Start webhook server
echidnabot serve --port 8080

# Register a repository
echidnabot register --platform github --repo owner/name

# Manually trigger verification
echidnabot check --commit HEAD

# Check status
echidnabot status --repo owner/name

# List available provers
echidnabot provers list
```

## Environment Variables

| Variable | Description |
|----------|-------------|
| `ECHIDNABOT_CONFIG` | Path to config file |
| `ECHIDNABOT_DATABASE_URL` | Database connection string |
| `ECHIDNABOT_ECHIDNA_ENDPOINT` | ECHIDNA Core GraphQL URL |
| `GITHUB_WEBHOOK_SECRET` | GitHub webhook secret |
| `GITLAB_TOKEN` | GitLab access token |

## Next Steps

- [[Configuration Reference]] — Full configuration options
- [[Supported Provers]] — Prover-specific setup
- [[Platform Integration]] — Detailed platform guides
- [[Troubleshooting]] — Common issues
