# Guides

## Adding a new prover backend

1. Create `src/rust/provers/your_prover.rs` implementing the `ProverBackend` trait. See [`src/rust/provers/z3.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/z3.rs) or [`src/rust/provers/coq.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/coq.rs) for templates.
2. Add a variant to `ProverKind` in `src/rust/provers/mod.rs`.
3. Wire it into `ProverFactory::create`.
4. Add test fixtures under `tests/fixtures/your_prover/`.
5. If the prover has a binary, add the SHAKE3-512 + BLAKE3 hashes to `config/solver-manifest.toml`.
6. If the prover should ship with the project, add it to `manifests/live-provers.scm` (Guix) or to `.containerization/Containerfile.wave3` (sealed container).
7. Update [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md) with the new tier assignment.
8. Run `just check && just test`.

## Using the API

```bash
# Start the API server
just serve

# REST: POST /api/verify
curl -X POST http://localhost:8000/api/verify \
  -H 'Content-Type: application/json' \
  -d '{"prover": "z3", "content": "(declare-const x Int) (assert (= (* x x) 4)) (check-sat)"}'

# GraphQL: port 8000/graphql
# gRPC:    port 50051
```

API surface and schemas: see [`src/interfaces/`](https://github.com/hyperpolymath/echidna/tree/main/src/interfaces).

## Training the GNN

The Julia ML sidecar trains from `training_data/` (553 MB corpus, ~67k proofs / ~180k tactics across 16 prover systems).

```bash
# CPU smoke run (~5 min)
just train-cpu

# Full GPU run (1–4h depending on hardware)
just train

# Evaluate against the held-out 20% validation split
just eval
```

Trained weights land in `models/neural/gnn_ranker/`. The Julia server hot-loads them on startup; a planned `POST /reload` endpoint will allow hot-swap without restart. See [`docs/handover/S5-VERIFICATION-RUNBOOK.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/S5-VERIFICATION-RUNBOOK.md).

## Configuring trust thresholds

Trust pipeline parameters live in `DispatchConfig` (`src/rust/dispatch.rs`). Adjust:

- `generate_certificates` — request DRAT/LRAT/TSTP certificates where supported
- `timeout` — per-prover wall-clock budget
- `cross_check_required` — minimum portfolio agreement
- `min_trust_level` — refuse below this Bayesian tier

Per-(prover, domain) timeout estimates come from `StatisticsTracker::estimate_timeout` once the learning loop has accumulated evidence. See [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md).

## Working with the learning loop

The loop flows: prover runs → outcome → VeriSimDB `proof_attempts` table → `mv_prover_success_by_class` materialised view → `VeriSimAdvisor` reads in dispatch / Julia `/training/update` pushes weights. Closing this loop is **Stage 3c** on the roadmap; current status and dead-wire findings are in [`docs/handover/STATE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/STATE.md).

## Environment variables

Every env var the system reads is enumerated in [`docs/ENV-VARS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ENV-VARS.md).

## Following the roadmap

[`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) is the canonical 8-stage map. [`docs/handover/HANDOVER-INDEX.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/HANDOVER-INDEX.md) navigates the prompt-and-runbook suite that drives each stage.
