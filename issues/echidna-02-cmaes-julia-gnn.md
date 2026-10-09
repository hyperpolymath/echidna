<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# ECH-02: feat(ml): black-box hyperparameter & temperature calibration for GNN premise rankers via CMA-ES / EDO

- **Repository:** hyperpolymath/echidna
- **Labels:** enhancement, area:ml, julia, tuning
- **Area:** Julia / Neurosymbolic ML

## Summary

Premise rankers used by ECHIDNA's guided search have hyperparameters (learning rate, weight decay, dropout, embedding size, message-passing depth) and a softmax/contrastive **temperature** that are currently set by hand or by grid search. Add a black-box optimiser based on CMA-ES (and, as a comparison baseline, an estimation-of-distribution variant, "EDO") to tune these values against a held-out ranking metric.

## Context

- `src/julia/training/train.jl` defines `contrastive_loss(scores, relevant_indices; temperature=0.1f0)`. The temperature is a keyword default with no calibration path.
- `src/julia/run_training.jl`, `run_training_cpu.jl` and `eval_held_out.jl` already contain the training and evaluation entry points. Reuse them; do not fork a second training loop.
- `src/julia/Project.toml` is the dependency manifest, and `src/julia/Manifest.toml` is tracked in git. Adding the optimiser dependency therefore requires updating both files together. The root-level `/Manifest.toml` is git-ignored, but that does not cover `src/julia/`.
- On the Rust side, `src/rust/gnn/guided_search.rs` consumes the ranker scores. Calibrated temperature affects score scale, so calibration must be evaluated on the same score path the Rust side uses.
- The root-level `metrics/` directory (e.g. `MetricsSuite.jl`) contains existing Julia metric code, and `src/chapel/bench_mrr.chpl` computes MRR on the Chapel side. Use the same metric definitions.

## Proposed Work

- Add a tuning module (e.g. `src/julia/training/calibration.jl`) with:
  - A parameter-space encoding with explicit bounds and log-scale handling for learning rate, weight decay and temperature.
  - A CMA-ES objective: validation MRR (or top-k recall) at a fixed budget, with the seed, budget and wall-clock recorded.
  - A baseline EDO/univariate EDA optimiser, with the same interface, for comparison.
- Temperature calibration as a separate, cheap, post-hoc step: fit temperature on a validation split by minimising negative log-likelihood of relevant premises, with the ranker frozen.
- Write results (best parameters, trial history, seed, data hash) to a JSON file under `reports/` or a path set by the caller. Do not commit large trial logs.
- Add a `Justfile` recipe for the tuning run, consistent with existing recipes.

## Acceptance Criteria

- [ ] Tuning runs end to end on the CPU path with a small budget, from a clean checkout after instantiating the Julia project.
- [ ] Same seed → same best parameters (deterministic given the same data split).
- [ ] Temperature calibration reduces validation NLL relative to the default `0.1f0`, or the issue documents that it does not.
- [ ] Improvement is reported against a fixed-budget random-search baseline, using the same validation split.
- [ ] Held-out test set is never used during tuning; this is checked in code, not only by convention.
- [ ] No change to the default training behaviour unless the tuned config is explicitly loaded.
- [ ] `src/julia/Project.toml` and `src/julia/Manifest.toml` are updated together and the project instantiates cleanly.

## Out of Scope

- Changing the GNN architecture or the Rust graph construction.
- Distributed or parallel trial execution (see ECH-03).
- Claims of general accuracy gains beyond the evaluated split.

## Open Questions

- Which validation metric is authoritative for the proof-search use case: MRR, top-k recall at the dispatcher's budget, or time-to-proof?
- Is CMA-ES available as a maintained Julia package that is acceptable under the repository's licence policy? Check before adding the dependency.
