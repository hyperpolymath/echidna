# Frequently Asked Questions

## General

### What is echidnabot?

echidnabot is a proof-aware CI bot that automatically verifies formal proofs in your code repositories. It integrates with GitHub, GitLab, and Bitbucket to check proofs on every push and pull request.

### Why is it called echidnabot?

It's the bot interface to [ECHIDNA](https://github.com/hyperpolymath/echidna), the theorem proving platform. Echidnas are thorough, methodical creatures — like a good proof checker.

### What's the difference between echidnabot and ECHIDNA?

- **ECHIDNA Core** — The theorem proving platform with actual prover backends
- **echidnabot** — The CI integration layer that connects platforms to ECHIDNA

### Is echidnabot free?

Yes! echidnabot is open source under PMPL-1.0-or-later. You can:
- Self-host your own instance
- Use the public instance at echidna.hyperpolymath.dev
- Modify and distribute under the same license

## Setup

### Do I need to run ECHIDNA Core?

For basic verification, no. echidnabot can run provers directly in CI workflows. For advanced features (ML suggestions, caching), you'll want an ECHIDNA Core instance.

### Which platforms are supported?

- **GitHub** — Full support (Check Runs, PR comments, status)
- **GitLab** — Full support (pipelines, MR comments)
- **Bitbucket** — Basic support (build status)
- **Codeberg** — Planned

### How do I set up the webhook?

See [[Getting Started]] for platform-specific instructions. The basic flow is:
1. Add a webhook pointing to your echidnabot instance
2. Set a secret for signature verification
3. Select push and pull request events

### Can I use echidnabot without webhooks?

Yes! Use the CLI for manual verification:
```bash
echidnabot check --commit HEAD
```

Or trigger via the GraphQL API.

## Usage

### How do I know which provers are enabled?

Check your configuration or run:
```bash
echidnabot provers list
```

### Can I verify only specific files?

Yes, use file patterns:
```toml
[files]
include = ["src/**/*.v", "proofs/**/*.lean"]
exclude = ["test/fixtures/**"]
```

### How long do verifications take?

Depends on the proof complexity. Simple proofs: seconds. Large Coq developments: minutes. Set appropriate timeouts:
```toml
[provers.coq]
timeout = 300  # 5 minutes
```

### What happens if a proof fails?

echidnabot will:
1. Mark the Check Run as failed
2. Post error details with line numbers
3. Optionally suggest fixes (in Advisor mode)
4. Block merge (in Regulator mode)

### Can I retry a failed verification?

Yes:
- Re-push the commit
- Use the GitHub Check Run "Re-run" button
- Call the API: `triggerCheck(repoId, commitSha)`

## Configuration

### Where do I put the configuration?

Options (in priority order):
1. `echidnabot.toml` in repository root
2. `.echidnabot.toml` in repository root
3. `~/.config/echidnabot/config.toml`
4. Environment variables

### How do I configure different settings per branch?

```toml
[autocheck]
branches = ["main", "develop"]

[branches.main]
require_passing = true
mode = "regulator"

[branches.develop]
require_passing = false
mode = "advisor"
```

### How do I pass prover flags?

```toml
[provers.coq]
flags = ["-R", "src", "MyProject", "-Q", "theories", "Theories"]
```

## Troubleshooting

### Webhook not triggering

1. Check webhook delivery in platform settings
2. Verify signature secret matches
3. Check echidnabot logs for errors
4. Ensure webhook URL is accessible

### Prover not found

Ensure the prover is:
1. Enabled in configuration: `enabled = ["coq", "lean4"]`
2. Installed in the CI environment
3. Available in PATH

### Timeout errors

Increase timeout in configuration:
```toml
[scheduler]
job_timeout_seconds = 600
```

Or per-prover:
```toml
[provers.coq]
timeout = 300
```

### Database connection errors

Check `ECHIDNABOT_DATABASE_URL`:
```bash
# SQLite (development)
ECHIDNABOT_DATABASE_URL="sqlite://echidnabot.db"

# PostgreSQL (production)
ECHIDNABOT_DATABASE_URL="postgres://user:pass@localhost/echidnabot"
```

## Security

### Is my code sent anywhere?

Only if using ECHIDNA Core. In local mode, provers run in your CI environment. With ECHIDNA Core, proof content is sent for verification (no storage by default).

### How are webhook secrets stored?

In environment variables or encrypted configuration. Never in code or logs.

### Can echidnabot access my repository?

Only the files you configure. echidnabot needs read access to proof files. It never modifies your code.

## Advanced

### Can I run multiple echidnabot instances?

Yes, for load distribution:
1. Use PostgreSQL for shared state
2. Point all instances to same database
3. Use a load balancer for webhooks

### How do I add a custom prover?

1. Implement prover in ECHIDNA Core
2. Add file extension mapping
3. Configure in echidnabot

### Can echidnabot work with monorepos?

Yes, use file patterns to verify only changed paths:
```toml
[files]
include = ["packages/math/**/*.v"]
```

### Is there a size limit?

Default limits:
- 10MB per file
- 100 files per job
- 10 minute timeout

Override in configuration if needed.

## Getting Help

- **Issues:** [GitHub Issues](https://github.com/hyperpolymath/echidnabot/issues)
- **Discussions:** [GitHub Discussions](https://github.com/hyperpolymath/echidnabot/discussions)
- **Wiki:** You're reading it!
- **Code:** [hyperpolymath/echidnabot](https://github.com/hyperpolymath/echidnabot)
