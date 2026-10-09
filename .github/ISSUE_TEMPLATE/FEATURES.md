# Feature Requests - Issues List

This document tracks high-priority feature requests for ECHIDNA development.

---

## Issues List

### High Priority

- **feat(ffi): C-ABI / Zig bridge specification for embedding ParadisEO metaheuristics engine with Idris2 contracts**
  - **Target Repository:** hyperpolymath/echidna
  - **Area:** src/abi/EchidnaABI/, ffi/zig/, crates/echidna-core-creusot
  - **Description:** To utilize ParadisEO's battle-tested C++17 metaheuristic engine (including mo, moeo, and edo) within ECHIDNA's Rust core without compromising memory safety or high-assurance trust guarantees, a formally specified and hardened FFI boundary is needed. ECHIDNA maintains strict type contracts using an Idris2 ABI layer (src/abi/EchidnaABI/) and Zig FFI glue.
  - **Proposed Changes:**
    - Zig C-ABI Shim (ffi/zig/paradiseo_bridge.zig): Provide extern "C" abstraction wrapping ParadisEO's core C++ template instantiations (paradiseo_moeo_nsga2_rank, paradiseo_edo_cmaes_step, paradiseo_mo_tabu_search) with clean allocation/deallocation lifetimes and zero memory leaks across the C++/Rust boundary
    - Idris2 ABI Specification & Proofs: Formalize parameter bounds, return value structs, and status codes in src/abi/EchidnaABI/OptimizationABI.idr with totality and non-divergence properties under %default total with 0 postulate / 0 believe_me
    - Rust Safe Bindings (crates/echidna-metaheuristics): Expose idiomatic, memory-safe Rust wrapper structs implementing the OptimizerBackend trait, guarded behind feature flags (--features paradiseo-opt) with safe fallbacks in pure Rust
  - **Acceptance Criteria:**
    - zig build test passes all FFI memory leak and lifetime checks (using Zig's GPA / GeneralPurposeAllocator)
    - idris2 --build src/abi/echidnaabi.ipkg compiles and verifies totality without warnings
    - cargo clippy --workspace --all-targets -D warnings and cargo test pass cleanly
  - **References:** ECHIDNA ABI documentation: docs/ABI_SPECIFICATION.adoc, ParadisEO C++ source: eo, mo, moeo, edo in Alessandro624/paradiseo
  - **Status:** Open

- **feat(chapel): island-model asynchronous migration topologies & dynamic solver portfolio budget allocation**
  - **Target Repository:** hyperpolymath/echidna
  - **Area:** src/chapel/, parallel/rank_merge.chpl, executor/portfolio.rs
  - **Description:** ECHIDNA leverages a Chapel parallel layer for distributed PGAS (Partitioned Global Address Space) operations across multiple computing locales, primarily executing parallel rank-merges across portfolio solvers. Currently, multi-prover portfolios allocate static compute timeouts across backends (e.g., 5 seconds to Z3, 10 seconds to Vampire, 15 seconds to Isabelle). In large-scale distributed runs, this leads to idle compute cores and redundant search paths. ParadisEO's parallel modules (smp and peo) model optimization as an Island Model with asynchronous migration topologies and dynamic parameter control. Applying these distributed metaheuristic topologies to Chapel will optimize CPU allocation and proof search diversity.
  - **Proposed Changes:**
    - Island-Model Proof Exploration on Chapel Locales: Map each Chapel locale to a dedicated "proof island" exploring distinct tactic spaces or solver configurations. Implement asynchronous migration policies: periodically exchange promising intermediate lemmas, simplified sub-goals, and unprovability warrants between locales across PGAS channels
    - Dynamic Compute Budget Allocation: Track early progress markers (clause generation rates in first-order ATPs, simplification step velocity in Isabelle/Lean). Use adaptive resource reallocation (inspired by ParadisEO's dynamic parameter adaptation) to divert CPU threads and memory limits from stalled prover processes toward converging solver branches
    - Diversity-Preserving Niching: Incorporate fitness sharing / niching across locales to prevent worker tasks from redundantly exploring identical lemma combinations
  - **Acceptance Criteria:**
    - Multi-locale Chapel execution (CHPL_COMM=gasnet or sockets) passes verification suite with zero data races
    - Proof portfolio completes corpus benchmarks with measurable reduction in cumulative core-hours compared to static timeout scheduling
    - Asynchronous migration across locales remains non-blocking and robust against single-backend worker crashes
  - **References:** ParadisEO SMP/PEO modules: smp, peo in nojhan/paradiseo, Chapel PGAS Distributed Architecture docs
  - **Status:** Open

- **feat(ml): black-box hyperparameter & temperature calibration for GNN premise rankers via CMA-ES / EDO**
  - **Target Repository:** hyperpolymath/echidna
  - **Area:** src/julia/, ml/premise_selection/, verification/confidence.rs
  - **Description:** ECHIDNA's Julia ML subsystem uses Graph Neural Networks (GNNs) to embed formal terms and rank candidate lemmas/tactics for premise selection. The output probabilities are combined with Bayesian confidence posteriors and Dempster-Shafer belief combinations before being dispatched to backend provers. Because end-to-end proof success is a non-differentiable step function (0/1 for timeout/fail/pass), standard backpropagation cannot optimize post-inference parameters such as: Softmax temperature scaling factors across heterogeneous prover kinds, Bayesian prior weights for different mathematical domains (algebra, topology, logic), Cutoff thresholds for premise candidate truncation. ParadisEO's EDO (Estimation of Distribution Optimization) module implements adaptive normal distributions and Covariance Matrix Adaptation Evolution Strategies (CMA-ES), which excel at continuous black-box parameter calibration on non-smooth surfaces.
  - **Proposed Changes:**
    - Calibration Runner in Julia/Rust: Create a parameter calibration harness that runs against benchmark corpora (e.g., Isabelle AFP subset, CoqHammer lemmas). Expose vector parameter inputs for (τ_temp, w_prior, k_cutoff, α_dempster)
    - CMA-ES / EDA Integration: Adapt ParadisEO's edoNormalAdaptive / CMA-ES covariance update rule to search the parameter space. Objective function: Maximize cumulative proof closure rate within a fixed total wall-clock budget (multi-objective: closure rate vs. total CPU time)
    - Artifact Serialization: Serialize calibrated parameter matrices to .machine_readable/ml_calibration.json with SHA-256 integrity verification at startup
  - **Acceptance Criteria:**
    - Parameter search demonstrates a measurable increase (e.g., ≥5%) in single-shot proof closure rate across the standard regression corpus compared to default uniform heuristics
    - Calibration harness operates deterministically given a fixed random seed
    - Parameters load cleanly into Julia runtime with zero runtime overhead during standard echidna prove calls
  - **References:** ParadisEO EDO Module: edo in Alessandro624/paradiseo, Hansen, N. "The CMA Evolution Strategy: A Tutorial" (2016)
  - **Status:** Open

- **feat(pareto): integrate exact hypervolume indicator and MOEO non-dominated sorting in verification/pareto.rs**
  - **Target Repository:** hyperpolymath/echidna
  - **Area:** verification/pareto.rs, src/rust/verification/
  - **Description:** ECHIDNA currently evaluates and ranks candidate proof outcomes across 4 objective dimensions (proof_time_ms, trust_level, memory_bytes, proof_size_nodes) in src/rust/verification/pareto.rs. While the current implementation calculates simple non-dominated fronts, multi-prover portfolios often produce dense, high-dimensional candidate clouds (e.g. fast Level-2 SMT proofs vs. moderate Level-4 Isabelle proofs vs. slow Level-5 dual-kernel Coq/Lean certificates). Drawing principles from ParadisEO-moeo (Multi-Objective Evolutionary Optimization), we can enhance ECHIDNA's frontier selection with exact hypervolume indicators and active crowding-distance diversity metrics.
  - **Proposed Changes:**
    - Fast Non-Dominated Sorting (NSGA-II / SPEA2): Implement efficient O(M·N²) non-dominated sorting algorithm from moeo to assign rank levels to candidate proofs. Introduce crowding distance / niching to preserve diversity when pruning candidate proof pools before presenting to the user or downstream consumers
    - Exact Hypervolume Indicator (HVC): Implement dimension-bounded exact hypervolume contribution metrics to quantify the relative quality increase of a new proof candidate against the reference nadir point (worst case: max timeout, Trust Level 1, max memory, max proof size)
    - Multi-Objective Quality Metric in echidna.prove.result/1: Expose the hypervolume contribution and front rank in the JCS-canonical I-JSON output receipt so downstream clients (such as echidnabot and proof-burrower) can make informed trade-off selections
  - **Technical Invariants & Verification:**
    - Total Order on Frontier Scores: The Pareto ranking must satisfy strict anti-symmetry and transitivity under floating/fixed-point arithmetic
    - Trust-Level Monotonicity: A proof candidate with strictly higher trust level must never be dominated by a lower-trust candidate unless explicitly disqualified by hard resource caps
    - Unit & Property Tests: Add property-based tests in tests/pareto_tests.rs (using proptest) verifying that no candidate on Front k dominates any candidate on Front j where j<k. Benchmark hypervolume calculation overhead against synthetic proof sets of size N=1000
  - **References:** ParadisEO-moeo architecture: moeo module in nojhan/paradiseo, ECHIDNA trust specification: docs/TRUST_LEVELS.adoc
  - **Status:** Open

### Medium Priority

### Low Priority

---

*Last updated: 2026-10-09*
