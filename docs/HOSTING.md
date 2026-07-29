<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Hosting and deployment topology

Where each public-facing piece of ECHIDNA runs, how it is published, and what
state each piece is currently in. This is the human-facing companion to
[`.machine_readable/deployment.a2ml`](../.machine_readable/deployment.a2ml);
keep the two in step.

## The three surfaces

| Surface | Host | Built by | Source |
|---|---|---|---|
| `nesy-prover.dev` — website | **Cloudflare Pages** | `.github/workflows/pages.yml` (Ddraig SSG) | [`site/`](../site) + [`echidna-playground/`](../echidna-playground) |
| `api.nesy-prover.dev` — HTTP API | **Hetzner**, rootless podman behind Caddy | `ghcr-publish.yml` → `ghcr.io/hyperpolymath/echidna` | [`deploy/hetzner/`](../deploy/hetzner) |
| `sudo@nesy-prover.dev` — contact | **Cloudflare Email Routing** (forwarder) | n/a — DNS only | n/a |

DNS for the zone is on Cloudflare.

## Website

Content lives in [`site/`](../site) as Markdown and is rendered by **Ddraig
SSG** (an Idris2 static site generator) inside `pages.yml`. The playground is
copied in as static assets afterwards.

Two properties of the generator matter when editing:

- It **hard-fails the build** on any accessibility violation — more than one
  `<h1>` per page, a skipped heading level, or a missing `alt`. A page that
  fails prints `[a11y FAIL]` and the workflow exits non-zero. Every page must
  print `[a11y ok]`.
- Its internal `copyTree` is **text-only and corrupts binary files**. Anything
  binary must be copied with `cp` in the workflow, never placed where the SSG
  will walk it. This is why the playground has its own copy step.

Build it locally exactly as CI does:

```bash
ddraig build site _site https://nesy-prover.dev
```

Links between pages are authored with `.html` extensions, because the SSG
renders `foo.md` to `foo.html` at the same path and does not rewrite link
targets.

### Publishing target

The apex is served by **Cloudflare Pages**. The build must stay in GitHub
Actions because it requires Idris2, which managed build images do not provide;
CI produces `_site` and publishes that directory.

> **Current state:** the content is merged and `pages.yml` is enabled, but the
> site is not yet live — see *Known issues* below.

## API

The deployed service is the `echidna` binary's `server` subcommand. Its routes,
request shapes and response shapes are documented in
[`site/docs/api/core.md`](../site/docs/api/core.md), which was written from the
route table and types in `src/rust/server.rs` — **that page is the accurate
one**. The separate REST, GraphQL and gRPC interface binaries are optional and
documented alongside it.

The full deployment procedure, including preflight gates, is
[`deploy/hetzner/README.adoc`](../deploy/hetzner/README.adoc). In outline:

- `echidna` and `caddy` run as **rootless podman systemd quadlets** on a shared
  network; the API publishes **no host port** and is reachable only through Caddy
- Caddy terminates TLS and applies a **30 req/min per-IP rate limit** and a
  **1 MB request body cap**
- the container is capped at `--memory=1500m --pids-limit=512`, with a tmpfs
  `/tmp` and `NoNewPrivileges`
- `AutoUpdate=registry` plus `HealthOnFailure=kill` means a new release rolls
  out unattended and an unhealthy container **fails the unit**, which is what
  makes rollback actually fire

### Why the caging matters

The API has **no authentication** and executes prover binaries on
user-supplied input. Rate limiting bounds how *many* requests arrive; it does
not bound the cost of a single one, and Lean accepts `#eval` — arbitrary code
at elaboration time. A per-request server-side prover timeout is outstanding
work (`src/rust/server.rs` spawns provers with no deadline).

## Known issues

1. **Repository Actions are failing at startup.** Every workflow in this
   repository currently returns `startup_failure`, including `pages.yml`. This
   is repo-level, not a fault in any workflow file — a minimal probe workflow
   containing a single SHA-pinned `actions/checkout` fails identically. Until
   it is resolved, nothing builds or deploys and **no gate verifies anything**.
2. **The apex has no origin yet.** `nesy-prover.dev` resolves to Cloudflare
   proxy addresses; the TLS handshake completes and the request then hangs,
   because Cloudflare is proxying to an origin that does not exist. The DNS
   records are likely already correct — what is missing is the Pages project
   behind them.

### Diagnosing "the board is green but nothing ran"

A workflow that fails at startup registers **no check run at all**, so it
cannot show up as missing or failing. `gh pr checks` will report success while
every real gate is dead. Always confirm with:

```bash
gh run list --branch main --json workflowName,conclusion
```

A related tell: when `gh run list` shows a workflow by its **path**
(`.github/workflows/x.yml`) instead of its **name**, that file has never been
parsed successfully. Confirm with
`gh api repos/OWNER/REPO/actions/runs/<id>/jobs --jq '.jobs|length'` returning `0`.

## Retired

**fly.io** — the `echidna-nesy` app is no longer used, for cost reasons.
Any remaining `fly.toml` or `fly-deploy.yml` is dead weight and should be
removed; the Fly deploy action was never on the repository's permitted-actions
list in any case.
