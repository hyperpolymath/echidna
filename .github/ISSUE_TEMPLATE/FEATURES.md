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

- **feat(swarm): combinatorial tactic playbook synthesis using delta/partial neighborhood evaluation (ParadisEO-mo)**
  - **Target Repository:** hyperpolymath/proof-burrower
  - **Area:** Rust / Search Engine
  - **Description:** The Proof Burrower system performs automated tactic selection and proof search. Currently, it uses heuristic-based selection which can miss optimal tactic combinations. ParadisEO-mo (Multi-Objective Optimization) provides delta/partial neighborhood evaluation capabilities that can intelligently explore combinatorial search spaces. Applying these to Proof Burrower's tactic playbook synthesis would enable more systematic exploration of tactic combinations.
  - **Proposed Changes:**
    - Delta Evaluation: Implement ParadisEO-mo delta evaluation to measure marginal improvement of adding/removing tactics from playbooks
    - Partial Neighborhood Search: Use mo's partial neighborhood evaluation to explore tactic combinations without full re-evaluation
    - Playbook Optimization: Apply multi-objective optimization to synthesize optimal tactic playbooks for different proof domains
  - **Acceptance Criteria:**
    - Delta evaluation reduces playbook synthesis time by at least 30%
    - Partial neighborhood search maintains proof success rate while exploring fewer combinations
    - Optimized playbooks outperform hand-crafted playbooks on benchmark corpus
  - **References:** ParadisEO-mo module in nojhan/paradiseo, Proof Burrower architecture documentation
  - **Status:** Open
  - **Cross-Repo Link:** [PB-01 Issue #108](https://github.com/hyperpolymath/proof-burrower/issues/108)

- **feat(ledger): anti-pattern mining and objective fitness formulation from burrow.jsonl for heuristic guidance**
  - **Target Repository:** hyperpolymath/proof-burrower
  - **Area:** Rust / Ledger & Indexing
  - **Description:** Proof Burrower maintains a ledger of proof attempts and outcomes in burrow.jsonl format. This historical data contains valuable patterns about which tactics succeed or fail in different contexts. Currently, this data is underutilized for guiding future proof attempts. ParadisEO's optimization frameworks can help extract anti-patterns and formulate fitness functions to guide heuristic search.
  - **Proposed Changes:**
    - Anti-Pattern Mining: Systematically extract failure patterns from burrow.jsonl using data mining techniques
    - Fitness Formulation: Develop objective fitness functions that score tactic applicability based on historical outcomes
    - Heuristic Guidance: Use mined patterns to guide tactic selection in future proof attempts
  - **Acceptance Criteria:**
    - Anti-pattern mining identifies at least 10 distinct failure modes
    - Fitness formulation improves proof success rate by at least 5%
    - Heuristic guidance reduces redundant proof attempts
  - **References:** ParadisEO data mining and optimization modules, Proof Burrower ledger documentation
  - **Status:** Open
  - **Cross-Repo Link:** [PB-02 Issue #109](https://github.com/hyperpolymath/proof-burrower/issues/109)

- **feat(dispatcher): adaptive portfolio timeout and solver selection scheduling for CI PR gates**
  - **Target Repository:** hyperpolymath/echidnabot
  - **Area:** Rust / CI Bot / Dispatcher
  - **Description:** echidnabot operates as a formal-verification CI bot, triggering ECHIDNA proof checks on GitHub/GitLab/Codeberg PRs. Currently, it dispatches verification jobs using static timeouts and fixed prover tiers. In continuous integration environments, resource constraints and wall-clock budgets are paramount. A PR touching small helper lemmas should not consume full multi-minute timeouts across all 12 core provers. Conversely, complex theorem changes need strategic, prioritized prover scheduling. Applying Automated Algorithm Selection and Parameter Tuning principles from ParadisEO enables echidnabot to dynamically schedule solver portfolios and allocate per-job timeouts based on PR diff complexity and historical confidence receipts.
  - **Proposed Changes:**
    - PR Diff Feature Extraction: Extract lightweight structural features from incoming proof diffs (number of modified lines/theorems, target formal language, dependency graph centrality)
    - Adaptive Solver Dispatcher: Implement dynamic schedule matrix optimizing multi-objective trade-off (Min Wall-Clock Time, Max CI Trust Level) with Tier-1 SAT/SMT backends for fast PR feedback and small-kernel provers (Coq, Isabelle, Lean 4) for merge gates
    - Circuit Breaker Tuning: Use adaptive sliding-window statistics to dynamically adjust circuit breaker trip thresholds based on repository-wide solver load
  - **Acceptance Criteria:**
    - Average CI turnaround time on non-breaking PRs decreases without reducing overall verification trust thresholds
    - Zero regressions in the 184-test test suite
    - Dynamic scheduling respects all explicit directives configured in .machine_readable/bot_directives/echidnabot.a2ml
  - **References:** Echidnabot Architecture: wiki/Architecture.md, ParadisEO Automated Algorithm Selection: Dreo et al. (2021) "Paradiseo: from a modular framework to automated design"
  - **Status:** Open
  - **Cross-Repo Link:** [EB-01 Issue #177](https://github.com/hyperpolymath/echidnabot/issues/177)

### Medium Priority

### Low Priority

---

*Last updated: 2026-10-09*
*Cross-repo links verified: PB-01→#108, PB-02→#109, EB-01→#177*
