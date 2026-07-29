<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Saturation Lane — Prover/Corpus/Vocab/Synonyms/Arbitration

**Branch**: `prover-corpus-saturation` (worktree at `/tmp/echidna-saturation`)
**Base**: `origin/main` @ `88cd8dc`
**Started**: 2026-06-01
**Driver**: secondary Claude instance, owner-directed "max out / until marginal benefit gone"
**Sibling lane**: `wave3/161-162-bench-telemetry-corpus` (primary Claude — chapel bench + telemetry)

## Why this exists

The owner directive: push solvers / corpuses / vocab / synonyms / verisim E-R / learning / arbitration to their respective marginal-benefit limits, dispatching agents in parallel.
This document declares the lane so the wave3 branch can avoid collisions.

## Lane scope — what this branch DOES touch

NEW FILES ONLY where possible. Where existing files must be edited, the file is listed below with the specific functions/symbols I am extending.

### Corpus adapters (new files)

- `src/rust/corpus/isabelle.rs` — Isabelle/HOL AFP `.thy`
- `src/rust/corpus/metamath.rs` — set.mm
- `src/rust/corpus/mizar.rs` — MML `.miz` / `.abs`
- `src/rust/corpus/hol_light.rs` — Multivariate / Core
- `src/rust/corpus/hol4.rs` — HOL4 Script files
- `src/rust/corpus/dafny.rs` — `.dfy`
- `src/rust/corpus/why3.rs` — TOCCATA gallery `.mlw`
- `src/rust/corpus/fstar.rs` — F\* examples `.fst`
- `src/rust/corpus/tptp.rs` — TPTP problem library
- `src/rust/corpus/smtlib.rs` — SMT-LIB benchmarks
- `src/rust/corpus/acl2_books.rs` — ACL2 community books
- `src/rust/corpus/proofnet.rs` — ProofNet
- `src/rust/corpus/minif2f.rs` — MiniF2F
- `src/rust/corpus/naproche.rs` — Naproche libraries
- `src/rust/corpus/mathcomp.rs` — Coq MathComp (separate from coq.rs heuristic)
- `src/rust/corpus/iris.rs` — Coq Iris
- `src/rust/corpus/cubical_agda.rs` — Cubical Agda stdlib

### Corpus mod registration (existing file, additive only)

- `src/rust/corpus/mod.rs` — append `pub mod isabelle;` etc. No reordering of existing `pub mod` lines. No edits to existing functions.

### Synonyms data (new files)

- `data/synonyms/hol_light.toml`
- `data/synonyms/hol4.toml`
- `data/synonyms/metamath.toml`
- `data/synonyms/mizar.toml`
- `data/synonyms/dafny.toml`
- `data/synonyms/fstar.toml`
- `data/synonyms/why3.toml`
- `data/synonyms/acl2.toml`
- `data/synonyms/pvs.toml`
- `data/synonyms/tlaps.toml`
- `data/synonyms/imandra.toml`
- `data/synonyms/_msc2020.toml` — MSC2020 cross-prover dictionary
- `data/synonyms/_wordnet_math.toml` — WordNet math entries
- `data/synonyms/_conceptnet_seed.toml` — pre-fetched ConceptNet seeds (offline-resilient)

### Exchange bridges (new files)

- `src/rust/exchange/tptp.rs` — universal first-order ATP exchange
- `src/rust/exchange/smtlib.rs` — SMT-LIB exchange / round-trip
- `src/rust/exchange/smtcoq.rs` — SMT proofs into Coq
- `src/rust/exchange/lambdapi.rs` — Dedukti's successor

### Portfolio expansion (existing file)

- `src/rust/verification/portfolio.rs` — extend `default()` to include DReal, OpenSmt, SmtRat, MathSat, SPASS, Princess, iProver, Twee, Princess in their respective tiers. Pure additive — no semantic changes to existing solver entries.

### New arbitration mechanisms (new files)

- `src/rust/verification/bayesian_arbiter.rs` — posterior over verdict given evidence stream
- `src/rust/verification/dempster_shafer.rs` — belief mass combination
- `src/rust/verification/pareto_arbiter.rs` — multi-objective Pareto frontier voting

### Vocab/Synonyms wiring (existing files, surgical edits)

- `src/rust/suggest/synonyms.rs` — add `SynonymTable::with_msc2020()` method; add `merge_external()` for cross-prover dictionaries. Existing `load()` / `alternatives()` UNCHANGED.
- `src/rust/integrations/conceptnet.rs` — add `prefetch_to_cache()` method using `_conceptnet_seed.toml`. Existing `related_concepts()` UNCHANGED.

### E-R schema formalization (new files)

- `docs/architecture/VERISIM-ER-SCHEMA.md` — formal entity + relationship definitions
- `crates/echidna-wire/schemas/verisim_er.capnp` — Cap'n Proto schema (if compatible)

### Documentation (new files)

- `docs/decisions/2026-06-01-saturation-campaign.md` — ADR
- `docs/CORPUS-ADAPTERS.md` — index of all corpus adapters with their parsing strategy + canonical source URL
- `docs/handover/PROVER-CORPUS-SATURATION-LANE.md` — this file

## Lane scope — what this branch DOES NOT touch

**Hard exclusion list** (collision avoidance with wave3):

- `src/chapel/**` — entirely wave3
- `benches/**` — wave3 telemetry hooks
- `src/rust/diagnostics/corpus_monitor.rs` — wave3 per-prover telemetry
- `src/rust/diagnostics/gnn_training.rs` — wave3 training health hooks
- `training_data/premises_*.jsonl` — wave3 benches against these
- `training_data/floor_progress.{md,jsonl}` — wave3 progress file
- `training_data/metrics_baseline.jsonl` — wave3 baseline reference
- `src/rust/learning/{daemon,curriculum,mcts,self_play}.rs` — risk of telemetry collision
- `models/**` — first GNN training run risks deleting `models/neural/`; defer
- `src/julia/run_training.jl`, `train.jl`, `eval_held_out.jl` — deferred (would touch model artefacts)
- `.github/workflows/*` — CI changes go through the wave3 lane
- `Justfile` — `just train` / `just chapel-*` are wave3 territory
- Any file the wave3 branch has shown as modified in its working tree (~300 files; the staged set will land via #161/#162 merges, do not pre-empt)

## Contact protocol

- Each commit will use prefix `feat(corpus):` / `feat(vocab):` / `feat(exchange):` / `feat(arbiter):` / `docs(er):` so wave3 can grep.
- If a file outside this lane needs touching, I file an issue first and link it here.
- Final merge order: this branch rebases onto `main` AFTER wave3 lands (or at minimum, after #161/#162 are merged). No competing merge race.

## Marginal-benefit termination criteria

I stop the saturation push when:

1. All 14+ corpus adapters land with at least a smoke-test fixture each, OR
2. Each adapter blocks on an upstream binary/source absent from the environment, OR
3. Synonyms TOML files exceed ~5,000 lines total (current 863) and ConceptNet/MSC2020/WordNet dictionaries land, OR
4. Exchange bridges land for TPTP + SMT-LIB at minimum, OR
5. New arbiter trio (Bayesian / Dempster-Shafer / Pareto) compiles with tests against the existing portfolio results, OR
6. The compile-test loop slows below ~5 PRs/hour or fixture-fetch latency dominates,

whichever fires first.

## Progress log

- 2026-06-01 — branch created, handover doc landed, scoping agents reported.
- (subsequent entries added as work lands)
