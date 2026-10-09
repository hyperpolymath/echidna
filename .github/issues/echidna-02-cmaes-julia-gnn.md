# ECH-02: feat(ml): black-box hyperparameter & temperature calibration for GNN premise rankers via CMA-ES / EDO

**ID:** ECH-02  
**Target Repository:** hyperpolymath/echidna  
**Area:** Julia / Neurosymbolic ML  
**Labels:** enhancement, area:ml, julia, tuning  
**Status:** Open  
**Roadmap:** [ParadisEO Metaheuristic Integration](../ROADMAP-PARADISEO.md)  

---

## Context & Motivation

ECHIDNA's Julia ML subsystem uses Graph Neural Networks (GNNs) to embed formal terms and rank candidate lemmas/tactics for premise selection. The output probabilities are combined with Bayesian confidence posteriors and Dempster-Shafer belief combinations before being dispatched to backend provers.

Because end-to-end proof success is a non-differentiable step function (0/1 for timeout/fail/pass), standard backpropagation cannot optimize post-inference parameters such as:
- Softmax temperature scaling factors across heterogeneous prover kinds
- Bayesian prior weights for different mathematical domains (algebra, topology, logic)
- Cutoff thresholds for premise candidate truncation

ParadisEO's EDO (Estimation of Distribution Optimization) module implements adaptive normal distributions and Covariance Matrix Adaptation Evolution Strategies (CMA-ES), which excel at continuous black-box parameter calibration on non-smooth surfaces.

## Proposed Changes

- **Calibration Runner in Julia/Rust:** Create a parameter calibration harness that runs against benchmark corpora (e.g., Isabelle AFP subset, CoqHammer lemmas). Expose vector parameter inputs for (τ_temp, w_prior, k_cutoff, α_dempster)
- **CMA-ES / EDA Integration:** Adapt ParadisEO's edoNormalAdaptive / CMA-ES covariance update rule to search the parameter space. Objective function: Maximize cumulative proof closure rate within a fixed total wall-clock budget (multi-objective: closure rate vs. total CPU time)
- **Artifact Serialization:** Serialize calibrated parameter matrices to .machine_readable/ml_calibration.json with SHA-256 integrity verification at startup

## Acceptance Criteria

- [ ] Parameter search demonstrates a measurable increase (e.g., ≥5%) in single-shot proof closure rate across the standard regression corpus compared to default uniform heuristics
- [ ] Calibration harness operates deterministically given a fixed random seed
- [ ] Parameters load cleanly into Julia runtime with zero runtime overhead during standard echidna prove calls

## References

- [ParadisEO EDO Module](https://github.com/Alessandro624/paradiseo/tree/master/edo) - edo implementations
- [Hansen, N. "The CMA Evolution Strategy: A Tutorial" (2016)](https://arxiv.org/abs/1604.00772)

## Related Issues

- [ECH-01: Pareto MOEO sorting](echidna-01-pareto-moeo.md) - Multi-objective optimization foundation
- [ECH-03: Chapel island model](echidna-03-chapel-island-migration.md) - Distributed execution of calibrated models
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO EDO integration
- [PB-01: proof-burrower swarm](https://github.com/hyperpolymath/proof-burrower/issues/proof-burrower-01-combinatorial-tactic-synthesis.md) - Combinatorial tactic synthesis (consumes ML rankings)

---

**See Also:** [Full ParadisEO Roadmap](../ROADMAP-PARADISEO.md)  
**Repository:** [hyperpolymath/echidna](https://github.com/hyperpolymath/echidna)
