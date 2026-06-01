<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
-->

# Chapel ↔ Saturation Campaign Integration Hooks

**Status**: hook spec, not implementation.
**Last revised**: 2026-06-01.
**Why this file exists separately**: the saturation campaign (commits
`f73ee00..cb8caff` on `prover-corpus-saturation`) lands in a lane that
deliberately excludes `src/chapel/**` — that tree is owned by
`wave3/161-162-bench-telemetry-corpus`. This file specifies how the
Chapel parallel-proof-search layer SHOULD integrate with the campaign's
new surface AFTER wave3 lands, without pre-empting wave3's edits.

## What changed that Chapel can benefit from

Three new surfaces are now first-class in the Rust core:

1. **17 corpus adapters** (`src/rust/corpus/{agda,coq,lean,idris2,isabelle,metamath,mizar,hol_light,hol4,dafny,why3,fstar,acl2_books,tptp,smtlib,proofnet,minif2f}.rs`). Each emits a `Corpus` value with structured `CorpusEntry` rows + dependency edges.
2. **4-mechanism arbitration stack** (`src/rust/verification/{portfolio,bayesian_arbiter,dempster_shafer,pareto_arbiter}.rs`). Replaces the prior single-mechanism majority-vote.
3. **Cross-prover semantic index** via `data/synonyms/_msc2020.toml`, `_wordnet_math.toml`, `_conceptnet_seed.toml` plus the per-prover tables. Resolved via `SynonymTable::merge_external()` (`src/rust/suggest/synonyms.rs`).

The Chapel parallel-proof-search dispatcher
(`src/chapel/parallel_proof_search.chpl`) currently:
- Spawns N prover invocations in parallel across locales.
- Aggregates outcomes via `parallelProofSearch` (best-of) or
  `parallelProofSearchSpeculative` (first-success-wins atomic-CAS).
- L2.3 (cancel-token preemption) lands in the wave3 branch.

## Integration topology (proposed)

```
   ┌─────────────────────────────────────────────────────────┐
   │  Saturation campaign surface (this branch)              │
   │                                                          │
   │  Corpus adapters → Corpus JSON                          │
   │  Synonym tables   → SynonymTable + CrossProverDicts     │
   │  Arbiters         → bayesian / dempster_shafer / pareto │
   └────────────────────┬────────────────────────────────────┘
                        │
                        ▼  (Zig FFI shim)
   ┌─────────────────────────────────────────────────────────┐
   │  Chapel parallel proof search (wave3)                   │
   │                                                          │
   │  parallelProofSearch(goals[, arbiter_kind])             │
   │  parallelProofSearchSpeculative(goals)                  │
   │  + new: cross_prover_query(goal, semantic_class)        │
   └─────────────────────────────────────────────────────────┘
```

## Three concrete hook points

### Hook A — corpus-driven goal injection

**What it enables**: instead of Chapel benching against the existing
`training_data/premises_<adapter>.jsonl` files only, Chapel can pull a
fresh batch of goals from any of the 17 adapters via the Rust C FFI.

**Surface contract** (Rust-side, already present):
```rust
// src/rust/corpus/<adapter>.rs
pub fn ingest(root: &Path) -> Result<Corpus>;
// src/rust/corpus/mod.rs
impl Corpus {
    pub fn save_json(&self, path: &Path) -> Result<()>;
    pub fn load_json(path: &Path) -> Result<Self>;
}
```

**Chapel-side wiring** (TODO post-wave3):
```chapel
// src/chapel/corpus_bridge.chpl  (NEW FILE — DEFERRED)
extern proc echidna_corpus_load_json(path: c_string): c_voidptr;
extern proc echidna_corpus_entries_count(c: c_voidptr): c_int;
extern proc echidna_corpus_entry_qualified(c: c_voidptr, i: c_int): c_string;
```

**Wave3 collision check**: `src/chapel/corpus_bridge.chpl` does NOT
exist on wave3; safe to add post-merge.

### Hook B — arbitration kind selection

**What it enables**: Chapel callers pick which arbiter aggregates the
N parallel outcomes. Currently hard-coded to "best-of".

**Surface contract** (Rust-side, already present):
```rust
// src/rust/verification/bayesian_arbiter.rs
pub fn BayesianArbiter::new(prior_p_true: f64) -> Self;
pub fn BayesianArbiter::combine(&self, evidence: &[ProverEvidence]) -> PosteriorVerdict;

// src/rust/verification/dempster_shafer.rs
pub fn DempsterShaferArbiter::new() -> Self;
pub fn DempsterShaferArbiter::submit(&mut self, prover: ProverKind, mass: MassFunction);
pub fn DempsterShaferArbiter::combine_all(&self) -> Result<BeliefPlausibility, ArbiterError>;

// src/rust/verification/pareto_arbiter.rs
pub fn ParetoArbiter::new() -> Self;
pub fn ParetoArbiter::arbitrate(&self, outcomes: &[AttemptOutcome]) -> ParetoDecision;
```

**Chapel-side wiring** (TODO post-wave3):

The signature of `parallelProofSearch` becomes:
```chapel
proc parallelProofSearch(goals: [] Goal, kind: ArbiterKind = .BestOf): Outcome;

enum ArbiterKind {
  BestOf,           // current behaviour
  Bayesian,         // call into bayesian_arbiter
  DempsterShafer,   // call into dempster_shafer
  Pareto            // call into pareto_arbiter (multi-objective)
}
```

The aggregator on the Rust side picks the right arbiter based on
`kind`. **Wave3 collision check**: `parallelProofSearch` is currently
modified in wave3 — this hook lands AFTER wave3 merges, in a separate
PR scoped to "arbiter kind selection".

### Hook C — cross-prover semantic indexing

**What it enables**: parallel proof search across provers that have
distinct names for the same mathematical object (e.g. Coq `Nat.add_comm`
and Lean `Nat.add_comm` and Agda `+-comm`). Chapel can pick which
prover to invoke based on `cross_prover_identity_key` (E6 in the E-R
schema).

**Surface contract** (Rust-side, already present):
```rust
// src/rust/corpus/mod.rs (cross-prover identity is part of GraphPayload)
pub struct GraphPayload {
    pub cross_prover_identity_key: Option<String>,
    // ...
}
// src/rust/suggest/synonyms.rs
pub fn SynonymTable::by_semantic_class(&self, class: &str) -> Vec<&SynonymEntry>;
```

**Chapel-side wiring** (TODO post-wave3):
```chapel
// src/chapel/cross_prover_dispatch.chpl  (NEW FILE — DEFERRED)
proc dispatchToAllProversForConcept(
  semanticClass: string,
  goal: Goal
): [] Outcome {
  // for each prover with at least one entry tagged `semanticClass`,
  // invoke in parallel and arbitrate.
}
```

## Hand-off contract

When the wave3 branch is merged, the next chapel-side PR can take this
file as the integration spec:

1. Add `src/chapel/corpus_bridge.chpl` (Hook A) — ~50 LoC.
2. Extend `src/chapel/parallel_proof_search.chpl` signature with the
   `ArbiterKind` parameter (Hook B) — ~30 LoC plus ~50 LoC of
   per-kind aggregator stubs that call out via Zig FFI to the Rust
   arbiters.
3. Add `src/chapel/cross_prover_dispatch.chpl` (Hook C) — ~80 LoC.
4. Update `src/chapel/parallel_proof_search.chpl` callers in
   `dispatch.rs::verify_proof_parallel` to pick the arbiter kind based
   on config (`SaturationConfig`).
5. Add `chapel-saturation` feature to `Cargo.toml` gating the new
   bridge files.

Estimated total: ~200 LoC chapel, ~50 LoC Rust glue. No wave3 file
modified.

## What NOT to do

- Do NOT pre-write any chapel file under `src/chapel/` in this branch.
- Do NOT modify `dispatch.rs::verify_proof_parallel` in this branch.
- Do NOT touch the existing Zig FFI shim (`src/zig_ffi/chapel_bridge.zig`).
- Do NOT add the `ArbiterKind` enum in this branch — it goes in the
  follow-up PR so the spec lives next to the implementation.

The integration is deferred, not abandoned. This doc IS the spec.

## Cross-references

- E-R schema (consumed by Hook C): `docs/architecture/VERISIM-ER-SCHEMA.md`
- Corpus adapters (consumed by Hook A): `docs/CORPUS-ADAPTERS.md`
- Saturation ADR: `docs/decisions/2026-06-01-saturation-campaign.md`
- Handover (collision-avoidance contract): `docs/handover/PROVER-CORPUS-SATURATION-LANE.md`
- Existing chapel rehabilitation ADR: `docs/decisions/2026-05-30-chapel-rehabilitation.md`
- Existing chapel cancel-token ADR: `docs/decisions/2026-05-30-chapel-l23-cancel-token.md`
