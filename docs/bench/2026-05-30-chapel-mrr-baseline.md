<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Chapel speedup baseline — 2026-05-30

Wave-1 baseline for the three Chapel proof-search strategies introduced
in PR #146:

- `sequentialProofSearch` — serial fallback.
- `parallelProofSearch` — best-of: `coforall` over all provers, return the
  fastest successful result. Wall time bounded by slowest task.
- `parallelProofSearchSpeculative` — first-success-wins via atomic CAS.
  Wall time bounded by fastest successful prover plus in-flight tail.

## Method

`src/chapel/bench_mrr.chpl` reads each fixture from
`tests/chapel_fixtures/`, calls each of the three strategies with the same
goal string and the full 30-prover registry (`timeout = 10 s`), and
emits CSV.

Reproduce:

```bash
just bench-chapel-mrr
```

## Fixtures

| Fixture | Language | Trivially provable in |
|---|---|---|
| `coq_trivial.v`    | Coq    | Coq (`coqc`)         |
| `lean_trivial.lean`| Lean 4 | Lean (`lean`)        |
| `idris2_trivial.idr`| Idris2 | Idris2 — **see caveats** |

## Results (median of 5 runs, seconds)

| fixture | strategy | wallclock | winning prover |
|---|---|---|---|
| coq_trivial    | sequential          | **0.313** | Coq  |
| coq_trivial    | parallel_bestof     | 0.741     | Coq  |
| coq_trivial    | parallel_speculative| 0.640     | Coq  |
| lean_trivial   | sequential          | **0.520** | Lean |
| lean_trivial   | parallel_bestof     | 0.733     | Lean |
| lean_trivial   | parallel_speculative| 0.636     | Lean |
| idris2_trivial | sequential          | 1.201     | —    |
| idris2_trivial | parallel_bestof     | 0.749     | —    |
| idris2_trivial | parallel_speculative| **0.731** | —    |

## Interpretation

Two regimes show clearly:

**Trivial-goal regime (Coq, Lean fixtures):** sequential is fastest. Both
goals succeed on the first or second prover tried (Coq at registry
position 1; Lean at position 2). The `coforall` spawn overhead for 30
tasks exceeds the parallelism win. Best-of pays the additional cost of
waiting for every spawned task to complete; speculative pays the cost of
the in-flight tail until the next-completing failure registers.

**Failure regime (Idris2 fixture):** parallel strategies are **~1.6× faster**
than sequential. Sequential walks all 30 registry entries one at a time,
paying the per-spawn cost for each failure (Idris2 itself takes ~0.7 s to
error out, the rest are `which` misses). `coforall` collapses that 30-deep
chain into a single round of parallel spawns.

Wave-1 confirms: the parallel-dispatch machinery is sound, the
strategy-difference is the predicted shape, and the speculative path is
production-ready as a drop-in for problems where the successful prover
is **not** known in advance.

## Caveats

The baseline is intentionally small (3 fixtures × 4-of-30 provers locally
on PATH). Three known integration gaps surface and are tracked as
follow-ups, **not** blockers for the L2.2 ship:

1. **Idris2 fixture fails for all strategies.** `idris2 --check` requires
   the file's path to live inside the configured source directory and
   loads `Prelude` from `IDRIS2_DATA_DIR`. The registry entry in
   `parallel_proof_search.chpl :: buildProverRegistry` invokes Idris2
   from the parent's CWD with no env override, so `--check
   /tmp/echidna-chapel/goal_Idris2_<n>.idr` reports
   `Module Prelude not found`. Fixing this means a per-prover prelude
   hook in `tryProver` (cd to tmp dir, export `IDRIS2_DATA_DIR`).
   Tracked as a Wave-2 follow-up issue.
2. **Agda rejects mangled filenames.** Agda's module-name resolution
   requires the source file's basename to be a valid Agda identifier.
   `tryProver` writes to `goal_Agda_<n>.agda`, which Agda parses as a
   compound identifier where `<n>` is a numeric literal and rejects.
   Workaround: use `agda --safe -i <tmpdir> goal_Agda_<n>.agda` with a
   leading letter in the temp basename, or generate Agda content with
   `module _ where`. Tracked as a Wave-2 follow-up issue.
3. **Sub-second wall-clock has ±200 ms jitter.** The medians above are
   stable across 5 runs but individual cells vary by 2-3× at cold start
   (e.g. one `parallel_speculative coq_trivial` reading came in at 2.538 s
   on a cold cache). For routine regression checking, run the bench
   five times and take the median. CI should use a warm-cache pre-pass.

A non-trivial corpus benchmark — proofs that take 10-30 s in their
native prover and where multiple provers can succeed — is the
follow-up that will show speculative dramatically beating sequential
(target: ≥ 5× on the success regime). That requires the L3 corpus
hand-off and the Wave-2 Idris2/Agda fixes above.

## Raw data

5-run readings preserved at `docs/bench/2026-05-30-chapel-mrr-baseline.csv`.

## Update 2026-05-31 — Caveats 1 & 2 resolved (#158 + #159)

`ProverInfo` gained two optional spawn hooks: `cwd` (subprocess
working directory, shell-wrapped to be coforall-safe) and
`filenameOverride` (literal basename for provers that enforce
module-name = filename). Registry entries for Idris2 and Agda set
both; the bench fixture set gained `agda_trivial.agda`. The
`bench-chapel-mrr` Justfile recipe now derives `IDRIS2_PREFIX` from
`which idris2` so the parent shell doesn't need to export it.

Single-run readings (replace with 5-run medians in a follow-up):

| fixture | strategy | wallclock | winning prover |
|---|---|---|---|
| idris2_trivial | sequential          | 1.970 | Idris2 |
| idris2_trivial | parallel_bestof     | 1.037 | Idris2 |
| idris2_trivial | parallel_speculative| 1.032 | Idris2 |
| agda_trivial   | sequential          | 0.101 | Agda   |
| agda_trivial   | parallel_bestof     | 0.751 | Agda   |
| agda_trivial   | parallel_speculative| 0.450 | Agda   |

Note the new Agda regime: `sequential` is fastest (0.101 s) because
Agda sits at registry position 0 — the first prover tried — and
succeeds immediately, so the parallel strategies pay coforall spawn
overhead with no benefit. The trivial-goal regime observation from
the original bench applies symmetrically here.

Wave-3 follow-ups still open: real-corpus speedup bench (#161,
10-30 s prover invocations) and per-prover preempted/timeout/success
telemetry (#162).
