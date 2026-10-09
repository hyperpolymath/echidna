# EB-01: feat(dispatcher): adaptive portfolio timeout and solver selection scheduling for CI PR gates

**ID:** EB-01  
**Target Repository:** hyperpolymath/echidnabot  
**Area:** Rust / CI Bot / Dispatcher  
**Labels:** enhancement, area:dispatcher, rust, ci-optimization  
**Status:** Draft (unverified)  

**Provenance:** Based on read-only look at echidnabot@ae5283323b815f82d2a556080b59e0bb648de62b  

---

## Context & Motivation

echidnabot operates as a formal-verification CI bot, triggering ECHIDNA proof checks on GitHub/GitLab/Codeberg PRs. Currently, it dispatches verification jobs using static timeouts and fixed prover tiers.

In continuous integration environments, resource constraints and wall-clock budgets are paramount. A PR touching small helper lemmas should not consume full multi-minute timeouts across all 12 core provers. Conversely, complex theorem changes need strategic, prioritized prover scheduling.

Applying Automated Algorithm Selection and Parameter Tuning principles from ParadisEO enables echidnabot to dynamically schedule solver portfolios and allocate per-job timeouts based on PR diff complexity and historical confidence receipts.

## Current State

Verified against echidnabot@ae5283323b815f82d2a556080b59e0bb648de62b:
- `enqueue_repo_jobs` in `src/api/webhooks.rs` creates one job per enabled prover (VERIFIED: iterates over `repo.enabled_provers`)
- `JobLimiter` defaults to 10 global / 3 per repo concurrent jobs (VERIFIED: in limiter.rs)
- Static 300 second timeouts are used as default (VERIFIED: `default_timeout()` returns 300 in config.rs)
- `manifest [provers.<slug>] timeout_seconds` is wired into dispatch (VERIFIED: accessed in manifest.rs, used in echidna_client.rs)
- `[scheduler] job_timeout_seconds` does NOT exist (CORRECTED: comment in manifest.rs claiming it exists is wrong)
- `proof_jobs`, `proof_results`, `tactic_outcomes` tables exist (VERIFIED: in migrations/20260602000001_initial_schema.sql)

## Proposed Changes

- **PR Diff Feature Extraction**: Extract lightweight structural features from incoming proof diffs (number of modified lines/theorems, target formal language, dependency graph centrality)
- **Adaptive Solver Dispatcher**: Implement dynamic schedule matrix optimizing multi-objective trade-off (Min Wall-Clock Time, Max CI Trust Level) with Tier-1 SAT/SMT backends for fast PR feedback and small-kernel provers (Coq, Isabelle, Lean 4) for merge gates
- **Circuit Breaker Tuning**: Use adaptive sliding-window statistics to dynamically adjust circuit breaker trip thresholds based on repository-wide solver load

## Acceptance Criteria

- [ ] Average CI turnaround time on non-breaking PRs decreases without reducing overall verification trust thresholds
- [ ] Zero regressions in the 184-test test suite
- [ ] Dynamic scheduling respects all explicit directives configured in .machine_readable/bot_directives/echidnabot.a2ml

## References

- Echidnabot Architecture: wiki/Architecture.md
- ParadisEO Automated Algorithm Selection: Dreo et al. (2021) "Paradiseo: from a modular framework to automated design"

---

**Related Issues:**
- [ECH-01: Pareto sorting](echidna-01-pareto-moeo.md) - Multi-objective optimization foundation
- [ECH-02: ML calibration](echidna-02-cmaes-julia-gnn.md) - Informs dispatcher decisions
- [ECH-03: Chapel distribution](echidna-03-chapel-island-migration.md) - Distributed execution backend
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO integration

**Repository:** [hyperpolymath/echidnabot](https://github.com/hyperpolymath/echidnabot)
