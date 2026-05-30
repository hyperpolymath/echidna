<!-- SPDX-License-Identifier: MPL-2.0 -->

# 2026-05-30 — L2.3 cancel-token preemption for speculative search

ADR-style addendum to [2026-05-30-chapel-rehabilitation.md][rehab].
Documents the L2.3 cancel-token plumbing that closes the
"speculative-search winner doesn't kill losers" gap explicitly carried
forward from Wave 1.

[rehab]: ./2026-05-30-chapel-rehabilitation.md

## Status

Accepted. Implemented in the PR that introduces this ADR.

## Context

PR #146's L2.2 `parallelProofSearchSpeculative` shipped with a clear
Wave-1 caveat (recorded in the function's docstring and in the rehab
ADR):

> Wave 1 scope deliberately stops short of the "kill in-flight losers"
> step. Once a prover has been spawned, `tryProver` runs it to its own
> per-prover timeout — coforall doesn't know how to cancel a child task
> that's blocked on subprocess I/O. L2.3 introduces a cancel token
> threaded through `tryProver` so the children can SIGKILL their own
> subprocesses when they observe a winner; that's a separate PR.

That separate PR is this one. The visible symptom Wave 1 left behind:
once a successful prover wins the CAS, the bench's wall-clock for
`parallel_speculative` was still bounded by the slowest in-flight
loser (because each one ran to its own `tryProver` timeout). The
`baseline.md` 5-run medians show this — speculative and best-of were
within noise on the success cases, instead of speculative dominating.

## Decision

Add a shared `CancelToken` instance to `parallelProofSearchSpeculative`,
thread an optional `borrowed CancelToken?` reference through
`tryProver`'s signature, and have the winner pair its CAS with a
write to the token. Each loser polls the token at every 100 ms tick
inside the existing bounded-wait loop; on observing `cancelled = true`
it SIGKILLs its own subprocess and returns a preempted result.

Why a `class` (not `record`) `CancelToken`:

- The token must be **shared by reference** across all `coforall`
  tasks so the winner's write is visible to every loser. Chapel
  records have value semantics; classes are passed by reference.
- Atomic-bool fields on a class have well-defined initial state
  (`false`) after `init this` commits field initialisation, so the
  init proc body is empty — no race-on-construction concern.
- The class is owned by the search function (`new owned`) and
  borrowed by each `tryProver` call, so its lifetime is exactly the
  search's lifetime and no extra liveness reasoning is needed.

Why exitCode = -5 for preempted losers:

- The existing failure codes are `-1` (not available / general failure),
  `-2` (temp file failure), `-3` (timeout), `-4` (subprocess error).
  Preemption is a distinct fourth-kind of failure — the prover did
  not get to run to completion, but neither did it time out nor crash;
  it was actively SIGKILLed by the portfolio. Reusing `-3` (timeout)
  would mis-categorise preemption as a slow-prover signal, polluting
  any later bench that tracks timeout rates.

## Soundness

The aggregation soundness proof in `proofs/agda/ParallelSoundness.agda`
already covers this case. Theorem `cancellation-safety` states:

```agda
cancellation-safety : {n : ℕ} (bs : Vec Bool n)
                    → IsTrue (speculative (true ∷ bs))
cancellation-safety _ = tt
```

i.e. **once a head witness is true, the verdict is true regardless of
the tail bs's contents**. In the L2.3 implementation the "head" is the
CAS-winner's `success = true` and the tail `bs` is every loser's
post-preemption result (which is now `success = false` with
exitCode = -5 instead of running to a possibly-true result). The
theorem says: the verdict over the whole result vector is unaffected
by this difference. The Agda module's header docstring is updated in
this PR to spell out the L2.3 cross-reference.

The CAS itself is the linearisation point: any prover whose poll
observes `cancelled = true` ran AFTER the winning CAS. The
happens-before edge from `winnerIdx.compareAndSwap(-1, i)` →
`cancelToken.cancelled.write(true)` → next-loser's
`cancelToken!.cancelled.read()` is exactly the atomic-bool semantics
Chapel inherits from the C11 memory model.

## Expected speedup

Wave-1 baseline (`docs/bench/2026-05-30-chapel-mrr-baseline.md`)
showed speculative ≈ best-of on the success cases because every
loser ran to its own per-prover timeout. After L2.3 the loser wall
is bounded by `pollInterval + SIGKILL latency ≈ 100-150 ms`. For the
trivial-success regime this is invisible because the winner itself
returns in 200-700 ms. For the realistic-corpus regime (10-30 s
real prover invocations) this is the difference between waiting
`max(losers)` and `min(winner) + ~150 ms`. The dramatic speedup the
bench writeup predicted is now structurally present.

A second baseline run (`docs/bench/`) is **not** included in this PR
— the trivial fixtures don't exercise the new code path enough to
show a meaningful number. A real-corpus bench run is the L2.4+
follow-up.

## Reproduce locally

```bash
just bench-chapel-mrr
# Watch the parallel_speculative wallclock vs parallel_bestof:
# trivial fixtures show no change; a follow-up corpus bench would
# show speculative << bestof.
```

## Risks / counter-arguments considered

1. **Premature cancellation race.** If two provers succeed at nearly
   the same instant, the late one might write `cancelled = true`
   between the early CAS and the early winner's exit. **Resolved:** the
   CAS is what selects the winner; whichever prover's `compareAndSwap`
   returns true wins regardless of token-write order. The late
   prover's `compareAndSwap` returns false (expected != -1 now), so
   it does NOT write to the token. Only ONE prover writes the token,
   and it's the same prover that wins the CAS.

2. **Self-cancellation.** Could a winning prover's poll race with its
   own success-detection and trigger preemption on itself? **No:**
   the cancellation poll happens INSIDE the `subproc.running` loop,
   which exits once the subprocess has terminated. A successful
   prover exits the loop via the `!subproc.running` edge before
   `cancelToken.cancelled.write(true)` is even called.

3. **Loser starvation.** What about provers whose first `tryProver`
   poll is delayed? **Resolved by 100 ms ceiling:** even the
   most-delayed prover observes the cancel within 100 ms of its
   first poll. Total preemption-observation latency is bounded by
   one pollInterval.

## Wave-3+ follow-ups

- A real-corpus bench (10-30 s prover invocations) to demonstrate
  the speculative >> bestof speedup quantitatively.
- A `--bench-chapel-mrr` `--strategy=speculative` flag that
  reports the per-prover preemption-vs-timeout-vs-success breakdown,
  so we can measure the wallclock improvement attributable to
  preemption specifically.
- Extend `CancelToken` to carry a reason string (winner-name,
  timeout-budget-exhausted, external-cancel, …) for future
  cooperative-cancellation flows beyond the speculative-search
  case.
