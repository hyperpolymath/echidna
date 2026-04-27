<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# S4 Loop-Closure Runbook

This runbook describes how to verify, locally and in CI, that ECHIDNA's
cross-prover learning loop (Roadmap stage 3a/3b — "S4") is closing.

## What is the loop?

```
ProverDispatcher::verify_proof  ──fire-and-forget──►
   VeriSimDBClient::record_proof_attempt
       └─►  POST /api/v1/proof_attempts
              └─►  ClickHouse proof_attempts row
                     └─►  mv_prover_success_by_class (materialised view)
                            └─►  GET /api/v1/mv_prover_success_by_class
                                   └─►  VeriSimAdvisor::suggest_prover
                                          └─►  next dispatch routes smarter
```

Three echidna-side wirings carry the loop:

| Wiring                 | Module                          | Wired in commit |
|------------------------|---------------------------------|-----------------|
| Write at dispatch exit | `dispatch::spawn_record_attempt`| `60d2e75`       |
| Class threading        | `dispatch::verify_proof_with_class` | `cf94b49`   |
| Cross-prover read      | `vcl_ut::cross_prover_search_names` | `cf94b49`   |

## What actually has to be standing up

Just **verisim-api** on a known port. The test never touches Elixir
orchestration, Svalinn, federation, drift monitor, or the seven backing
databases — it talks directly to the rust-core HTTP endpoints
`/api/v1/proof_attempts` and `/api/v1/mv_prover_success_by_class`.

## Local verification

### 1. Start verisim-api

The canonical way is `selur-compose up rust-core` from the verisimdb
checkout, but for a smoke run any of these work:

```bash
# Option A — selur-compose (preferred)
cd ~/Documents/hyperpolymath-repos/verisimdb
selur-compose up rust-core --detach

# Option B — podman-compose fallback
cd ~/Documents/hyperpolymath-repos/verisimdb
podman-compose -f container/compose.toml up rust-core --detach

# Option C — bare cargo run (development only)
cd ~/Documents/hyperpolymath-repos/verisimdb/rust-core
cargo run --release --bin verisim-api
```

Wait for `/health` to respond:

```bash
until curl -sf http://localhost:8080/health >/dev/null; do sleep 1; done
echo "verisim-api ready"
```

### 2. Run the loop-closure test

```bash
cd ~/Documents/hyperpolymath-repos/echidna
just test-s4-loop
```

Expected output (success):

```
running 2 tests
test s4_record_then_read_back_by_goal_hash ... ok
test s4_class_aggregation_visible_in_mv ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured
```

Expected output (verisim-api not running — graceful skip):

```
skip: VeriSimDB at http://localhost:8080 is unreachable —
      set VERISIM_URL or start verisim-api
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured
```

The skip path is intentional: the test is a no-op rather than a failure
when the dependency is absent, so the same `cargo test` command works on
machines without verisim-api in the loop.

### 3. Override the URL

```bash
VERISIM_URL=http://verisim.staging.example:9090 just test-s4-loop
```

## CI wiring

A workflow that brings up verisim-api and runs `test-s4-loop` is
**not yet committed**. The blocker is that no published
`ghcr.io/hyperpolymath/verisimdb-api` image exists yet — every CI run
would have to build verisim-api from a sibling checkout, which is too
heavy for `on: pull_request`.

When that image is published (verisim's `ghcr-publish.yml` is the
expected channel — currently absent from
`verification-ecosystem/verisimdb/.github/workflows/`), the workflow
becomes:

```yaml
name: S4 Loop Closure
on:
  workflow_dispatch:
  schedule: [{ cron: '0 4 * * 1' }]   # Mondays 04:00 UTC

jobs:
  s4-loop:
    runs-on: ubuntu-latest
    services:
      verisim:
        image: ghcr.io/hyperpolymath/verisimdb-api:latest
        ports: ['8080:8080']
        options: >-
          --health-cmd "curl -sf http://localhost:8080/health"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 12
    env:
      VERISIM_URL: http://localhost:8080
    steps:
      - uses: actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd  # v6.0.2
      - uses: dtolnay/rust-toolchain@4be9e76fd7c4901c61fb841f559994984270fce7
      - uses: Swatinem/rust-cache@779680da715d629ac1d338a641029a2f4372abb5
      - run: just test-s4-loop
```

This workflow is left as an unfiled artefact in this runbook precisely
to avoid landing it as a perpetually-skipping no-op. File it the same
day verisim publishes its image.

## What "loop closing in production" looks like

In a production deployment with both echidna and verisim-api running:

1. Run any successful `verify_proof_verisim_guided(..., obligation_class="…")`.
2. Within the verisim writer's HTTP timeout (default 10s) the row appears in
   the `proof_attempts` table.
3. ClickHouse refreshes `mv_prover_success_by_class` on the next interval.
4. Subsequent calls to `verify_proof_verisim_guided` with the same class
   start receiving a non-default routing decision (look for
   `VeriSimAdvisor: obligation_class=… → SomeProver` at INFO level in
   echidna's logs).

If step 4 never observes a non-default routing for a class that has
genuinely accumulated rows, the breakdown is one of:

- **MV not refreshing** → ClickHouse-side problem, check the MV definition.
- **Writer silently dropping** → look for `VeriSim record_proof_attempt failed`
  warnings in echidna logs.
- **Class string mismatch** → confirm the dispatch caller passes the same
  `obligation_class` the read path queries (the `cf94b49` threading fix
  closed the most common version of this).

## Future work tracked elsewhere

- Verisim image publish: `verification-ecosystem/verisimdb` repo, not echidna.
- Workflow filing once image is available: `.github/workflows/s4-loop.yml`.
- Tier-3 weekly cadence so it doesn't gate every PR.
