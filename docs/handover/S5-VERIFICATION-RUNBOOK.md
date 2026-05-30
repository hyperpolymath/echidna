# S5 Verification Runbook: Trained-Weights Verification Flow

## Purpose

This runbook proves end-to-end that once `just train-cpu` produces real weights
in `models/neural/`, (a) the Julia GNN server picks them up and stops using cosine
similarity, (b) the Rust backends that call `gnn_augment_tactics` receive
model-derived scores via the `/gnn/rank` wire format, and (c) MRR on a held-out
validation split can be measured and compared against the 0.66 cosine baseline.
Steps 1 and 2 can run before training has finished; only Step 3 requires weights.

---

## Prerequisite

`just train-cpu` (or `just train` on GPU) has completed and
`models/neural/gnn_ranker/` (or `best_model/` or `final_model/`) exists.

---

## Step 1 — Confirm wire format (no training needed)

```bash
cargo test --test gnn_augment_integration
```

Spawns an in-process mock HTTP server and asserts:

- `GnnClient::health_status()` returns the richer payload (model_path, vocab_size,
  training_records_received).
- For each of rocq, lean, agda, isabelle, z3 (the S5 pilot), idris2, fstar,
  cvc5, vampire, dafny (the Tier-1 extension), altergo, eprover (the Tier-1
  finisher), and the 33 Tier-2 backends (acl2, agsyhol, aprove, athena,
  cameleer, cbmc, chuffed, csi, dreal, glpk, HOL4, hol_light, imandra, iprover,
  key, lash, leo3, metamath, metitarski, minizinc, minlog, mizar, nuprl,
  ortools, princess, PVS, satallax, scip, spass, tlaps, twee, twelf, why3):
  `suggest_tactics` returns `Tactic::Custom { command: "apply", args: ["lemma_foo"] }`
  as the first tactic, proving the `/gnn/rank` wire format is consumed
  correctly by every backend.

Expected output: `test result: ok. 46 passed; 0 failed`.

---

## Step 2 — Confirm model load

Start the Julia GNN server:

```bash
julia --project=src/julia src/julia/api_server.jl
```

(or however you normally start it — check `src/julia/run_server.jl` for args).
Then query health:

```bash
curl -s http://localhost:8090/gnn/health | jq .
```

Expected response when weights are loaded:

```json
{
  "status": "ok",
  "gnn_model_loaded": true,
  "model_path": "/absolute/path/to/models/neural/gnn_ranker",
  "vocab_size": <non-zero>,
  "training_records_received": 0,
  "num_gnn_layers": 4,
  "service": "echidna-gnn",
  "version": "2.1.0"
}
```

`gnn_model_loaded: true` and `vocab_size > 0` confirm the server picked up real weights
and is no longer falling back to cosine similarity.

---

## Step 3 — Measure lift

```bash
just eval
```

Loads the trained model, runs `compute_metrics` on the held-out validation split
(20% of `training_data/`), and appends one JSONL row to
`training_data/eval_results.jsonl`.  Read the result:

```bash
tail -1 training_data/eval_results.jsonl | jq '{mrr, top1, top5, top10, val_size}'
```

---

## Acceptance

| Result | Action |
|--------|--------|
| MRR ≥ 0.66 | Baseline met. Log the row. Run `just train` on GPU for full training. |
| MRR < 0.66 | **STOP.** File a bug. Do not paper over it — this signals architecture mismatch, label leakage, or vocabulary miss. |

---

## Troubleshooting

| Symptom | Check |
|---------|-------|
| `gnn_model_loaded: false` after `just train-cpu` | Confirm `models/neural/gnn_ranker/` exists and contains `model.bson`, `vocabulary.bson`, `config.bson`. Restart the Julia server. |
| Integration test fails on `connection refused` | Re-run: `cargo test --test gnn_augment_integration`. The mock binds `127.0.0.1:0`; transient OS port exhaustion is extremely rare but retry once. |
| `just eval` errors with `No trained model found` | Run `just train-cpu` first. |
| `just eval` errors on a missing solver method | File a bug in the `EchidnaML` Julia module. Do not patch the eval script to bypass. |
| MRR unchanged from 0.66 after training | Check `models/model_metadata.txt` — if it still reads `0 words, 0 classes` the training run did not write weights. Check training logs. |
