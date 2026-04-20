# ECHIDNA metrics suite

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

Measures the cross-prover corpus along eight axes that together bound
the vocabulary horizon and triangulation capacity. Every metric
writes its result to VeriSimDB via `POST /api/v1/metrics`; the local
JSONL file is a cache, not the source of truth.

## Axes

| Module | Metric | Target |
|---|---|---|
| `triangulation_rate.jl` | % of theorems proved in ≥3 provers | ≥ 15 % |
| `alignment_rate.jl` | RDF-triples linking named theorems across provers | ≥ 30 % |
| `oov_rate.jl` | tokens in corpus not in CANON | ≤ 3 % |
| `heaps_beta.jl` | β from V ≈ k · N^β | 0.55 – 0.70 |
| `tactic_cluster_purity.jl` | per-prover n-gram distinctiveness | ≥ 0.65 |
| `msc_taxonomy_coverage.jl` | MSC categories with ≥ 10 proofs | ≥ 40 % |
| `prover_floor.jl` | proofs in least-represented prover | ≥ 5 000 |
| `zipf_s.jl` | Zipf slope on theorem-name frequencies | 0.9 – 1.1 |

## Running

```bash
julia --project=src/julia metrics/run_all.jl
```

Environment: `VERISIM_URL` (default `http://localhost:8080`),
`METRIC_RUN_ID` (default `metrics-<timestamp>`).

## Design

- Single loader in `corpus_loader.jl` — reads all `proof_states_*.jsonl`
  once per run and hands per-prover slices to each metric.
- Sink in `verisim_sink.jl` POSTs metric rows to VeriSimDB. If the API
  is unreachable, the row still lands in
  `training_data/metrics_<run_id>.jsonl` so no measurement is lost.
- Targets in the table above come from
  `Desktop/ECHIDNA-VERISIM-STRATEGY-2026-04-17.md`.
