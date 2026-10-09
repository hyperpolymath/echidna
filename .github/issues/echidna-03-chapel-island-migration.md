# ECH-03: feat(chapel): island-model asynchronous migration topologies & dynamic solver portfolio budget allocation

**ID:** ECH-03  
**Target Repository:** hyperpolymath/echidna  
**Area:** Chapel / Distributed PGAS  
**Labels:** enhancement, area:parallel, chapel, concurrency  
**Status:** Open  
**Roadmap:** [ParadisEO Metaheuristic Integration](../ROADMAP-PARADISEO.md)  

---

## Context & Motivation

ECHIDNA leverages a Chapel parallel layer for distributed PGAS (Partitioned Global Address Space) operations across multiple computing locales, primarily executing parallel rank-merges across portfolio solvers.

Currently, multi-prover portfolios allocate static compute timeouts across backends (e.g., 5 seconds to Z3, 10 seconds to Vampire, 15 seconds to Isabelle). In large-scale distributed runs, this leads to idle compute cores and redundant search paths.

ParadisEO's parallel modules (smp and peo) model optimization as an Island Model with asynchronous migration topologies and dynamic parameter control. Applying these distributed metaheuristic topologies to Chapel will optimize CPU allocation and proof search diversity.

## Proposed Changes

- **Island-Model Proof Exploration on Chapel Locales:** Map each Chapel locale to a dedicated "proof island" exploring distinct tactic spaces or solver configurations. Implement asynchronous migration policies: periodically exchange promising intermediate lemmas, simplified sub-goals, and unprovability warrants between locales across PGAS channels
- **Dynamic Compute Budget Allocation:** Track early progress markers (clause generation rates in first-order ATPs, simplification step velocity in Isabelle/Lean). Use adaptive resource reallocation (inspired by ParadisEO's dynamic parameter adaptation) to divert CPU threads and memory limits from stalled prover processes toward converging solver branches
- **Diversity-Preserving Niching:** Incorporate fitness sharing / niching across locales to prevent worker tasks from redundantly exploring identical lemma combinations

## Acceptance Criteria

- [ ] Multi-locale Chapel execution (CHPL_COMM=gasnet or sockets) passes verification suite with zero data races
- [ ] Proof portfolio completes corpus benchmarks with measurable reduction in cumulative core-hours compared to static timeout scheduling
- [ ] Asynchronous migration across locales remains non-blocking and robust against single-backend worker crashes

## References

- [ParadisEO SMP/PEO modules](https://github.com/nojhan/paradiseo/tree/master/smp) - smp module
- [ParadisEO PEO modules](https://github.com/nojhan/paradiseo/tree/master/peo) - peo module
- [Chapel PGAS Distributed Architecture docs](https://chapel-lang.org/docs/)

## Related Issues

- [ECH-01: Pareto MOEO sorting](echidna-01-pareto-moeo.md) - Multi-objective ranking for portfolio selection
- [ECH-02: GNN calibration](echidna-02-cmaes-julia-gnn.md) - ML models that inform chapel distribution
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO SMP/PEO integration
- [EB-01: echidnabot dispatcher](https://github.com/hyperpolymath/echidnabot/blob/main/.github/ISSUE_TEMPLATE/feature_request.yml) - CI portfolio scheduling (consumes chapel results)

---

**See Also:** [Full ParadisEO Roadmap](../ROADMAP-PARADISEO.md)  
**Repository:** [hyperpolymath/echidna](https://github.com/hyperpolymath/echidna)
