<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# ECH-03: feat(chapel): island-model asynchronous migration topologies & dynamic solver portfolio budget allocation

- **Repository:** hyperpolymath/echidna
- **Labels:** enhancement, area:parallel, chapel, concurrency
- **Area:** Chapel / Distributed PGAS

## Summary

Model parallel proof search as an island model: each island runs a search (a prover portfolio or a search configuration) and periodically migrates its best candidates to neighbouring islands according to a configurable topology. Add asynchronous migration and a dynamic budget allocator that moves compute time between solvers based on observed progress.

## Context

- `src/chapel/parallel_proof_search.chpl` is the existing parallel dispatch implementation. `bench_mrr.chpl` and `smoke.chpl` are the existing benchmark and smoke tests. `RESULTS.adoc` and `README.adoc` document current results.
- `src/zig_ffi/chapel_bridge.zig`, `chapel_ffi_exports.h` and `chapel_stubs.c` are the C-ABI boundary. Any new cross-language message type must go through this boundary, not through an ad hoc channel.
- The Rust side is built with `--features chapel` (see `CLAUDE.md`). The feature must still build when Chapel is absent.
- Portfolio logic on the Rust side (`src/rust/verification/portfolio.rs`, `PortfolioConfig`, `PortfolioSolver`) defines solver sets and timeouts. The Chapel budget allocator must not contradict those semantics. Decide which layer owns budgets before writing code.
- Results must be reproducible enough to compare. Record the topology, migration interval, seed and budget schedule with every run.

## Proposed Work

- Implement topology options as an enum: ring, 2-D torus, fully connected, and random-k neighbour. Each is a pure function from island id to neighbour set.
- Implement asynchronous migration with `begin`/`sync`-free message passing, or Chapel `sync`/`single` variables. Migration must not block the sending island. Document the chosen concurrency primitive and why.
- Migration policy: send top-k by a configured objective (proof time or trust level) at interval T, with a bounded inbox; drop oldest on overflow and count drops.
- Budget allocator: a bandit-style rule (e.g. successive halving or UCB over solver progress) that reallocates a fixed total budget among solvers. Budget changes are logged.
- Expose topology, interval, k and allocator settings as config fields, with defaults equal to the current single-island behaviour.

## Acceptance Criteria

- [ ] With one island (or migration disabled), results match the current `parallel_proof_search.chpl` output on the smoke test.
- [ ] All four topologies have unit tests checking neighbour sets for small N (including edge islands in the torus).
- [ ] Migration never blocks an island for longer than a documented bound in a benchmark run, and dropped-message counts are reported.
- [ ] Total budget is conserved by the allocator (sum of allocations equals the configured total, within a documented rounding rule).
- [ ] Benchmark reports wall-clock, solved count and budget trace for single-island vs. island configurations, on the same problem set.
- [ ] Rust build and tests pass without Chapel installed, and with `--features chapel` where Chapel is available.
- [ ] No new FFI symbols without matching entries in `chapel_ffi_exports.h`.

## Out of Scope

- Multi-node deployment and cluster scheduling.
- Changes to individual prover backends.
- Any claim of speed-up that is not backed by the benchmark above.

## Open Questions

- Which layer owns solver budgets: the Chapel allocator or `PortfolioConfig` on the Rust side?
- Is a fixed total budget the right model, or should islands also have per-island wall-clock caps?
