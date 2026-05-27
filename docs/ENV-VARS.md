<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# ECHIDNA Environment Variables

**Status**: canonical reference. Last revised: 2026-05-26.

Every environment variable the system reads, with type, default, and the
files that consume it. If you add a new env var, update this table in the
same PR.

## Core runtime

| Variable | Type | Default | Used by | Purpose |
|---|---|---|---|---|
| `ECHIDNA_ML_API_URL` | URL | `http://127.0.0.1:8090` | `src/rust/server.rs:71` | Julia ML sidecar HTTP endpoint (GNN, suggest, training/update) |
| `VERISIM_URL` | URL | `http://localhost:8080` | `src/rust/dispatch.rs`, `src/rust/learning/daemon.rs`, `src/julia/retrain_from_verisim.jl` | VeriSimDB REST endpoint for proof-attempt writes and history reads. **Canonical name** — older surfaces using `VERISIMDB_URL` are stale and being migrated. |
| `ECHIDNA_GNN_URL` | URL | falls back to `ECHIDNA_ML_API_URL` | (planned C5 — see Stage 3c fix list) | Specifically the GNN endpoint; separate from the ML server only when the GNN runs on a different host. |

## Training & evaluation (Julia)

| Variable | Type | Default | Used by | Purpose |
|---|---|---|---|---|
| `ECHIDNA_MAX_PROOF_STATES` | int | 0 (all) | `src/julia/run_training.jl`, `run_training_cpu.jl` | Cap corpus size for fast smoke runs. `just train-cpu` sets this to 2000. |
| `ECHIDNA_NUM_EPOCHS` | int | implementation default | same | Number of training epochs. `just train-cpu` sets this to 2. |
| `ECHIDNA_NUM_NEGATIVES` | int | 20 | same | Negative-sample count per training step. |
| `ECHIDNA_MODELS_DIR` | path | `models/` | `src/julia/api/server.jl`, `src/julia/eval_held_out.jl` | Where trained Flux model artefacts live. |

## CI & supply-chain

| Variable | Type | Default | Used by | Purpose |
|---|---|---|---|---|
| `FARM_DISPATCH_TOKEN` | secret | unset | `.github/workflows/instant-sync.yml` | Push notifications to dependent forks. |
| `VERISIMDB_PAT` | secret | unset | `.github/workflows/security-scan.yml` | Reusable panic-attack workflow auth. Note: name is `VERISIMDB_PAT` not `VERISIM_PAT` — secret-name compatibility with upstream. |

## Build flags (not env vars but related)

| Cargo feature | Default? | Enables |
|---|---|---|
| `verisim` | no (target: yes after Stage 3c C4 lands) | VeriSimDB writer + advisor + entity-type emission |
| `chapel` | no | Chapel parallel-search bridge via Zig FFI shim |

## Container & secrets

In `.containerization/Containerfile.full`, the following are expected to be
mounted or built into the image rather than passed as env:

- Solver binaries — paths in `config/solver-manifest.toml` (with SHAKE3-512 hashes)
- Guix manifest — `manifests/live-provers.scm`
- TLS material — none in default container; HTTPS terminated by reverse proxy

## Deprecated / soon-removed

| Variable | Note |
|---|---|
| `VERISIMDB_URL` | Old name for `VERISIM_URL`. Still read by `tests/live_prover_suite.rs:118` and enforced by `k9iser.toml:47`. Migration tracked in Stage 3c fix C3. |

## Reading order for new contributors

1. Set `ECHIDNA_ML_API_URL` and `VERISIM_URL` for any local dev session that
   touches dispatch or ML paths.
2. Set the `ECHIDNA_*` training caps only when running `just train-cpu` or
   `just eval` on a constrained host.
3. CI secrets (`FARM_DISPATCH_TOKEN`, `VERISIMDB_PAT`) are repository-level —
   no local action needed.
