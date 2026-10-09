<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# ECH-01: feat(pareto): integrate exact hypervolume indicator and MOEO non-dominated sorting in verification/pareto.rs

- **Repository:** hyperpolymath/echidna
- **Labels:** enhancement, area:verification, rust, optimization
- **Area:** Rust / Multi-Objective Search

## Summary

`src/rust/verification/pareto.rs` currently computes the Pareto frontier with an O(n²) pairwise dominance check (`ParetoFrontier::compute`) and ranks candidates with a weighted sum (`ParetoFrontier::weighted_rank`). Add:

1. **Non-dominated sorting** (front-peeling, MOEO-style), so every candidate receives a front rank, not just a frontier/not-frontier flag.
2. **An exact hypervolume indicator** for the four proof-search objectives, so that portfolio results and strategy configurations can be compared by a single quality number that respects Pareto structure.

## Context

- `ProofObjective` holds four objectives: `proof_time_ms` (minimise), `trust_level` (maximise, via `TrustLevel::value()`), `memory_bytes` (minimise), `proof_steps` (minimise).
- `ProofCandidate.is_pareto_optimal` is a boolean. Front rank is not stored.
- `weighted_rank` uses inverse-scaled objectives, so it is sensitive to unit choice and to zero handling. Hypervolume requires a consistent minimisation transform, which should be defined in one place.
- `src/rust/verification/pareto_arbiter.rs` is the existing consumer of frontier results. It must be checked before any signature change.
- ParadisEO is referenced only in the roadmap; nothing in the repository depends on it yet. This issue is about the *algorithms* (non-dominated sorting, hypervolume), and does not require vendoring ParadisEO code.

## Proposed Work

- Define an explicit minimisation transform: `f = [proof_time_ms, -trust_level, memory_bytes, proof_steps]` (all minimised), with a documented reference point strictly worse than the observed worst on each axis.
- Add `ParetoFrontier::non_dominated_sort(candidates) -> Vec<Vec<usize>>` returning fronts F₁, F₂, … (O(MN²) acceptable; document complexity).
- Add `ParetoFrontier::hypervolume(points, reference) -> f64` as an **exact** computation:
  - 2-D: sweep-line.
  - ≥3-D: exact algorithm (e.g. WFG or HSO-style slicing). Monte Carlo estimates are out of scope and must not be labelled "exact".
- Add a `ParetoFrontier::hypervolume_contribution(...)` helper (exclusive hypervolume per candidate) for ranking within a front.
- Keep `compute` and `weighted_rank` public behaviour unchanged, or deprecate them with a note. Do not silently change existing test expectations.
- Keep the module free of network, FFI, or external crate dependencies beyond what `Cargo.toml` already provides.

## Acceptance Criteria

- [ ] Non-dominated sorting agrees with the existing `compute` result for front F₁ on the existing test fixtures.
- [ ] Hypervolume matches hand-computed values on known 2-D and 3-D fixtures, including degenerate cases (duplicate points, a point equal to the reference, empty set → 0.0).
- [ ] Property test: adding a non-dominated point never decreases hypervolume; adding a dominated point leaves it unchanged.
- [ ] Hypervolume is invariant under permutation of candidates.
- [ ] Reference point and transform are documented in rustdoc, and the exactness claim is stated precisely.
- [ ] `cargo test` and `cargo clippy` pass for the workspace; no new `unsafe`.
- [ ] Existing `pareto_arbiter.rs` behaviour is unchanged, verified by its tests.

## Out of Scope

- Changing the set of objectives or how `TrustLevel` is assigned.
- Wiring hypervolume into the dispatcher. That is a follow-up once the metric is validated.
- Any ParadisEO dependency.

## Open Questions

- Should the reference point be fixed (configurable constant) or derived per query? Per-query values make hypervolume values non-comparable across runs.
