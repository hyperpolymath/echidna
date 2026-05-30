<!-- SPDX-License-Identifier: MPL-2.0 -->

# 2026-05-30 — Chapel metalayer rehabilitation: rewrite, not park

ADR-style record of the decision and rollout that closed issue #133
(Chapel CI has never been green) and re-enabled the parallel
proof-search layer as a load-bearing CI signal rather than a muted
red box.

## Status

Accepted. Implemented in the PR that introduces this ADR.

## Context

`chapel-ci.yml` (`Compile Chapel Metalayer` job) had **never passed**
in repository history at the point of this decision — the `.chpl`
sources mixed C++/Rust FFI syntax (`extern "C" { … }` blocks, octal
string escapes), used 1.x Chapel APIs that 2.x removed
(`createStringWithNewBuffer`, `send_signal`, `proc.stdout.reader`),
and had a single keyword-collision bug (`var proc = spawn(args)`
clashing with Chapel's `proc` keyword) that cascaded into ~12 reported
syntax sites. PR #131 had marked the affected jobs
`continue-on-error: true` so the workflow rendered green without the
underlying defect being fixed — a temporary unblock that became a
permanent blind spot for L2.

At the same time the wider L2 sub-waves (L2.2 speculative search,
L2.3 corpus-parallel, L2.4 mutation parallelism, L2.5 multi-locale,
L2.6 numeric hot paths, L2.7 bench) were documented in CLAUDE.md as
"not started and hard-gated on L1 Cap'n Proto" — the surface area was
parked behind a chain of upstream dependencies, so even fixing the
syntax wouldn't have unlocked downstream work without an explicit
choice about which sub-wave to target.

Two viable paths were on the table:

1. **Rewrite.** Replace the broken sources with real Chapel 2.x,
   accept that the apt-shipped Chapel runtime is `CHPL_LIB_PIC=none`
   only (forcing static-library distribution until a PIC runtime is
   available), and ship one sub-wave (L2.2 first-success-wins
   speculative search) to validate the path.
2. **Park.** Delete `src/chapel/`, drop the `chapel` Cargo feature,
   strike Chapel from the v2.2+ roadmap, and remove `chapel-ci.yml`.
   Treat parallel proof search as something a future Rust-native
   solution (rayon, async-portfolio) can deliver if the need
   re-emerges.

## Decision

**Rewrite (option 1).** The Chapel metalayer is the only existing
surface in the estate that (a) makes per-process parallelism explicit
at the language level rather than burying it in async runtimes, and
(b) already terminates at the Rust↔Zig↔Chapel triple-boundary that
the L1 Cap'n Proto plan presupposes. Parking would discard ~650 LOC
of staged work and would not actually save the work in the long run —
the parallel-dispatch row in `docs/ROADMAP.md` is a stage requirement,
not an accelerator we can drop without re-planning.

The specific commitments inside the rewrite decision:

- **Syntax + API rewrite.** Replace `extern "C" {…}` with module-level
  `const c_int` declarations + a `require "chapel_ffi_exports.h"` +
  `extern record CProofResult` pair that lets Chapel name the C type
  without needing LLVM/clang to parse the header. Rename the
  `var proc` keyword-collision to `var subproc`. Move from
  `createStringWithNewBuffer` to `string.createCopyingBuffer`, from
  `send_signal` to `sendPosixSignal`, and from
  `proc.stdout.reader(…)` to direct reading on `subproc.stdout`
  (`pipeStyle.pipe`).
- **Static, not dynamic.** Ship `libechidna_chapel.a` rather than
  `libechidna_chapel.so` because the apt-shipped 2.3.0 / 2.8.0
  Chapel only ships the `CHPL_LIB_PIC=none` runtime variant; the
  PIC runtime needed for shared-library output is not in the
  package and the linker rejects the non-PIC `libchpl.a` with
  `R_X86_64_TPOFF32 … can not be used when making a shared object`.
  Rebuilding Chapel from source with `CHPL_LIB_PIC=pic` in CI is
  a Wave-2 follow-up.
- **L2.2 lands now, L2.3+ defer.** This PR adds
  `parallelProofSearchSpeculative` (first-success-wins via atomic
  CAS, no mid-flight preemption) alongside the existing
  best-of `parallelProofSearch`. Preemption is L2.3 because it
  requires threading a cancellation token through `tryProver` so
  in-flight subprocesses can SIGKILL themselves on observing a
  winner; the cancel token, in turn, is a natural place to wire
  the L1 Cap'n Proto message that the worker tasks subscribe to.
- **CI flipped to strict.** `chapel-build` and `zig-ffi`
  drop `continue-on-error: true`; the rewrite means red checks here
  now indicate a genuine regression. `rust-chapel-real` stays
  allow-fail because the Rust-side link of the full Chapel runtime
  is a different scope (gated on the PIC-runtime work above and on
  the static-archive integration in `build.zig`).

## Rollout

Wave 1 (this PR, echidna only):
- `src/chapel/chapel_ffi_exports.chpl` + `parallel_proof_search.chpl`
  rewritten.
- `src/chapel/smoke.chpl` added — the toolchain-health signal that
  stays useful even when the metalayer is mid-refactor.
- `chapel-ci.yml` updated as described above.
- `proofs/agda/ParallelSoundness.agda` adds three theorems
  (soundness, completeness, cancellation-safety) about the
  speculative-search aggregation layer, with zero
  postulate/admit/believe_me (verified by `agda --safe`).
- `Justfile` recipes: `chapel-build`, `chapel-smoke`, `chapel-test`.

Wave 2 (separate PR, after Wave 1 green-on-main for ≥7 days):
- Rebuild Chapel from source with `CHPL_LIB_PIC=pic` runtime; revert
  the metalayer build to `--dynamic`; flip `rust-chapel-real` to
  strict. Recipe + tradeoffs:
  [2026-05-30-chapel-pic-rebuild.md](./2026-05-30-chapel-pic-rebuild.md).
  CI flip deferred — the ~30 min source build dominates the chapel-ci
  budget; a registry-pushed container image is the L2.5 prerequisite.
- Add the cancel-token thread through `tryProver` and switch the
  Chapel-side default to the speculative search.
- Wire the `proven` and `docudactyl` parallel-dispatch tracks
  off the same scaffold; breadcrumb issues filed in those repos
  on the PR landing.

Wave 3+ (longer term):
- L2.4 mutation parallelism, L2.5 multi-locale (requires cluster
  runtime; out of scope until we have one), L2.6 numeric hot
  paths, L2.7 bench.
- Idris2 ABI proof for the cross-FFI tactic-record (the GNN-ranked
  tactics consumed by the Chapel side); gated on a producer for
  the serialised record format.

## Consequences

**Positive.**

- Chapel CI becomes a real signal. A red `chapel-build` job now
  means a genuine regression, not a baseline-rot that future
  PRs paper over with `continue-on-error`.
- The L2 sub-waves have a concrete entry point — speculative
  search is in-tree and exercisable from Chapel-side benchmarks.
- The Agda layer formally documents the aggregation invariants,
  composable with the existing `SoundnessPreservation` proof.

**Negative.**

- Static-library distribution means the Rust-side link path
  (`rust-chapel-real`) remains allow-fail until the PIC-runtime
  CI image lands. Wave-2 work is non-trivial.
- `chapel-ci.yml`'s install step downloads a ~150 MB Chapel deb
  per run; this is unchanged from the prior state but matters
  more now that the job is strict (any apt mirror flake red-checks
  the workflow). Cacheability is on the Wave-2 todo list.

**Net.** The rewrite path is strictly better than parking: it
preserves option-value on the L2 → L1 → cluster sub-roadmap and
shifts the open work from "is Chapel even tenable here?" to
concrete, scoped engineering tasks.

## Toolchain version pinning

- `chpl 2.3.0` (CI) and `chpl 2.8.0` (local). The same source compiles
  under both — the `require` + `extern record` pair is stable across
  the range.
- `zig 0.14.0`. The `b.addLibrary(.{ … })` form used in
  `src/zig_ffi/build.zig` is the modern Build API, available since
  0.14.0 (the earlier comment in `chapel-ci.yml` claiming it was
  missing in 0.13.0 was stale relative to the workflow's own pin).
- `agda 2.6.3` against `agda-stdlib` (any 2.x compatible release).

These pins are re-stated in `chapel-ci.yml` and `Justfile`; see
also `.machine_readable/6a2/META.a2ml` for the canonical record.
