# Echidna L2 — Chapel Maximum Integration — Continuation Prompt

**Context**: Echidna has a 420-LoC Chapel POC (`chapel_poc/parallel_proof_search.chpl`) that implements
30-prover parallel portfolio dispatch but is **not wired into `src/rust/dispatch.rs`**. User directive
(2026-04-19): "expand Chapel to do EVERYTHING it can — no point investing in hard Chapel code and not
using it to maximum value."

**Master plan**: `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
**Prerequisites**: L3 Tier-1+Tier-2 green; L1 Cap'n Proto schemas stable.
**Scope**: ~5–6 weeks, broken into 7 sub-waves.

---

## What Chapel is actually good at (the full opportunity)

1. **Task parallelism** (`coforall`, `cobegin`, `begin`) — parallel prover dispatch, speculative tactic branches
2. **Data parallelism** (`forall`) — corpus-wide premise scoring, tactic mining
3. **Distributed PGAS** (locales, on-clauses) — multi-node proof search with sharded corpus
4. **Domains & distributions** — data-dependent workload partitioning
5. **Atomics** — first-wins racing, lock-free coordination
6. **Reductions** — parallel statistics, confidence aggregation
7. **GPU support** — Chapel-on-NVIDIA for embedding batches
8. **NUMA awareness** — locale-aware dispatch on multi-socket machines

## Sub-wave breakdown

### L2.1 — Portfolio dispatch (promote POC) ~1 week
- `src/chapel/portfolio.chpl` — migrate + adapt from `chapel_poc/parallel_proof_search.chpl`
- Input: Cap'n Proto `ProverInvocation` batch (from L1)
- Output: Cap'n Proto `TrustedOutcome[]`
- Race semantics: atomic first-wins, SIGKILL losers, cancellation within `timeout`
- Wire into `src/rust/dispatch.rs` behind `--chapel` feature flag via Zig FFI
- Default: feature-off; default-on flip after L2.7 benchmarks

### L2.2 — Speculative tactic search ~1 week
- `src/chapel/tactic_search.chpl`
- Parallel beam search (k parallel beams)
- Parallel MCTS over tactic trees (UCB1 selection with `coforall` rollouts)
- Speculative branch execution + cancellation on winner commit
- Consumes `TacticSuggestion` stream from GNN (L1 schemas)

### L2.3 — Corpus-parallel ops ~1 week
- `src/chapel/corpus.chpl`
- `forall` over 66,674-proof corpus
- Parallel proof replay (re-verify corpus)
- Parallel premise scoring (vs GNN rankings)
- Parallel tactic mining + inverted index build
- Locality-aware: `forall ... with (ref corpusShard)` to avoid cross-locale traffic

### L2.4 — Mutation testing parallelism ~3 days
- `src/chapel/mutation.chpl`
- Fan out 1000s of mutants across all cores/locales
- Integrate with existing Rust `verification/mutation.rs` (consume its mutant stream, run in Chapel)

### L2.5 — Multi-locale distributed ~1.5 weeks
- PGAS-sharded corpus across locales (`Block` or `Cyclic` distribution)
- Locale-aware prover dispatch: heavy backends on dedicated locales
- GPU-locale offload: embedding batches on NVIDIA locale if present
- Reproducibility: locale seed propagation
- Single-locale covers 80% of value; multi-locale proven on dev hardware

### L2.6 — Numeric hot paths ~4 days
- `src/chapel/numeric.chpl`
- Parallel GNN embedding pre-processing (batch pack + pad)
- Parallel Pareto frontier computation (`forall` + atomic minimum tracking)
- Parallel confidence statistics / Bayesian timeout updates

### L2.7 — CI + bench ~3 days
- `.github/workflows/chapel-live.yml` — runs Chapel-in-dispatch tests
- Criterion benchmarks: Chapel portfolio vs Rust+Rayon baseline
- Must show measurable speedup on 8+ core machines to flip default-on

## Acceptance criteria

- Chapel on hot path by default after benchmarks prove it
- `src/chapel/` has 6+ modules wired via Zig FFI + Cap'n Proto
- `chapel_poc/` archived (or deleted) with redirect note in its README
- Multi-locale path proven on at least one dev-hardware config
- Benchmarks show ≥1.5× speedup for portfolio solving on 8-core machines (or Chapel stays feature-flagged)
- No Rust code duplicates what Chapel does best (avoid double-paths)

---

## Rules active

- `feedback_wire_everything` — no stubs; POC promoted fully, not re-implemented
- `feedback_meander_resource_costs` — Chapel builds slow; cache Chapel artefacts in CI, clean after
- `feedback_rust_means_rust_spark` — Rust side admits SPARK/Ada; Chapel doesn't change that
- `feedback_verisimdb_policy` — Chapel-dispatched runs still emit VeriSimDB records (via Cap'n Proto
  back-channel to Rust)
- `feedback_full_battery_before_claims` — before claiming speedup, full battery: tests + benches +
  panic-attack + causality + verifiable I/O

## Key files to read first

1. `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
2. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/chapel_poc/parallel_proof_search.chpl` (420-LoC POC to promote)
3. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/zig_ffi/chapel_bridge.zig` (existing Zig FFI stub)
4. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/rust/dispatch.rs` (integration target)
5. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/.github/workflows/chapel-ci.yml` (current Chapel CI for compile-only)
6. `schemas/echidna.capnp` (must exist from L1 — if not, L1 isn't done)
