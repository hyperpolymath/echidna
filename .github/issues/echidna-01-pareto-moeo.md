# ECH-01: feat(pareto): integrate exact hypervolume indicator and MOEO non-dominated sorting in verification/pareto.rs

**ID:** ECH-01  
**Target Repository:** hyperpolymath/echidna  
**Area:** Rust / Multi-Objective Search  
**Labels:** enhancement, area:verification, rust, optimization  
**Status:** Open  
**Roadmap:** [ParadisEO Metaheuristic Integration](../ROADMAP-PARADISEO.md)  

---

## Context & Motivation

ECHIDNA currently evaluates and ranks candidate proof outcomes across 4 objective dimensions (proof_time_ms, trust_level, memory_bytes, proof_size_nodes) in src/rust/verification/pareto.rs.

While the current implementation calculates simple non-dominated fronts, multi-prover portfolios often produce dense, high-dimensional candidate clouds (e.g. fast Level-2 SMT proofs vs. moderate Level-4 Isabelle proofs vs. slow Level-5 dual-kernel Coq/Lean certificates). Drawing principles from ParadisEO-moeo (Multi-Objective Evolutionary Optimization), we can enhance ECHIDNA's frontier selection with exact hypervolume indicators and active crowding-distance diversity metrics.

## Proposed Changes

- **Fast Non-Dominated Sorting (NSGA-II / SPEA2):** Implement efficient O(M·N²) non-dominated sorting algorithm from moeo to assign rank levels to candidate proofs. Introduce crowding distance / niching to preserve diversity when pruning candidate proof pools before presenting to the user or downstream consumers
- **Exact Hypervolume Indicator (HVC):** Implement dimension-bounded exact hypervolume contribution metrics to quantify the relative quality increase of a new proof candidate against the reference nadir point (worst case: max timeout, Trust Level 1, max memory, max proof size)
- **Multi-Objective Quality Metric in echidna.prove.result/1:** Expose the hypervolume contribution and front rank in the JCS-canonical I-JSON output receipt so downstream clients (such as echidnabot and proof-burrower) can make informed trade-off selections

## Technical Invariants & Verification

- **Total Order on Frontier Scores:** The Pareto ranking must satisfy strict anti-symmetry and transitivity under floating/fixed-point arithmetic
- **Trust-Level Monotonicity:** A proof candidate with strictly higher trust level must never be dominated by a lower-trust candidate unless explicitly disqualified by hard resource caps
- **Unit & Property Tests:** Add property-based tests in tests/pareto_tests.rs (using proptest) verifying that no candidate on Front k dominates any candidate on Front j where j<k. Benchmark hypervolume calculation overhead against synthetic proof sets of size N=1000

## Acceptance Criteria

- [ ] Pareto ranking satisfies strict anti-symmetry and transitivity
- [ ] Trust-Level Monotonicity verified
- [ ] Property-based tests in tests/pareto_tests.rs pass
- [ ] Hypervolume calculation benchmarked against N=1000 synthetic sets

## References

- [ParadisEO-moeo architecture](https://github.com/nojhan/paradiseo/tree/master/moeo) - moeo module
- [ECHIDNA trust specification](../docs/TRUST_LEVELS.adoc)

## Related Issues

- [ECH-02: GNN premise ranker calibration](echidna-02-cmaes-julia-gnn.md) - Also uses ParadisEO optimization principles
- [ECH-03: Chapel island model](echidna-03-chapel-island-migration.md) - Distributed portfolio optimization
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO integration
- [EB-01: echidnabot dispatcher](https://github.com/hyperpolymath/echidnabot/blob/main/.github/ISSUE_TEMPLATE/feature_request.yml) - CI portfolio scheduling (consumes pareto outputs)

---

**See Also:** [Full ParadisEO Roadmap](../ROADMAP-PARADISEO.md)  
**Repository:** [hyperpolymath/echidna](https://github.com/hyperpolymath/echidna)
