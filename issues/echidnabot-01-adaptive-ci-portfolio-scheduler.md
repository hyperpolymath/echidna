<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# EB-01: feat(dispatcher): adaptive portfolio timeout and solver selection scheduling for CI PR gates

- **Repository:** hyperpolymath/echidnabot
- **Labels:** enhancement, area:dispatcher, rust, ci-optimization
- **Area:** Rust / Scheduling / Algorithm Selection
- **Provenance:** Drafted from hyperpolymath/echidna. Claims about echidnabot are marked *[unverified]*: they come from a read-only look at `echidnabot@ae52833` and have not been built, run or checked by a maintainer. Claims about echidna were checked against echidna `main` at `7fd369d`.

## Summary

For each push or PR event, echidnabot enqueues one job per enabled prover, each with a static timeout. Add an **adaptive scheduler** that uses recorded run history to (1) choose per-prover timeouts from observed runtime distributions and (2) order or select solvers for a PR gate, so the gate reaches a verdict faster within a fixed compute budget. The verdict rules and trust semantics stay the same.

## Context

- *[unverified]* `src/api/webhooks.rs::enqueue_repo_jobs` loops over `repo.enabled_provers` and creates one `ProofJob` per prover with the event's `JobPriority` (`High` for PR checks). There is no per-prover ordering and no selection.
- *[unverified]* `src/scheduler/` contains `JobScheduler` (a priority-ordered queue), `JobLimiter` (global limit 10 and per-repo limit 3 by default) and `retry.rs` (exponential backoff and a circuit breaker for transient errors). None of these use historical runtimes.
- *[unverified]* Timeouts are static: `EchidnaConfig.timeout_secs` (default 300), `ExecutorConfig.timeout_secs` (default 300) and the Podman executor default of 300 s.
- *[unverified]* `src/modes/manifest.rs` parses a per-prover `timeout_seconds` (`[provers.<slug>]`). Its doc comment says it falls back to `[scheduler] job_timeout_seconds`, but `SchedulerConfig` has only `max_concurrent` and `queue_size`. In the source examined, the per-prover value appears only in manifest parsing and tests. Confirm whether it is wired into dispatch before building on it.
- *[unverified]* History is already stored. In SQLite, `proof_jobs` holds prover, status and timestamps, `proof_results` holds `duration_ms` and success, and `tactic_outcomes` holds prover, goal fingerprint, tactic, success and `duration_ms`.
- *[unverified]* Regulator mode gates merges on a coverage percentage (`regulator_coverage_threshold`). Verified in echidna: `.machine_readable/bot_directives/echidnabot.a2ml` sets `mode = "regulator"` and `coverage-threshold = 90`, and `.echidnabot.toml` sets `[verification] timeout_secs = 300` with per-prover `priority` hints (`idris2` high, `z3`/`cvc5` medium, `coq`/`lean` low).
- Verified in echidna: `src/rust/verification/portfolio.rs` (`PortfolioConfig`) already models solver sets per problem class (SMT / ATP / ITP), a per-solver timeout (300 s) and a `wait_factor` (2.0) for cross-checking. echidnabot's scheduler should use compatible terminology and must not contradict these semantics. ECH-03 (#422) covers budget allocation on the echidna side. Decide which layer owns which budget before implementing.
- Verified in echidna: a `timeout` status in `echidna.prove.result/1` means "budget ran out; retry with a larger `--timeout`". It is not a failure, and the scheduler must keep that distinction.

## Proposed Work

- **Runtime model.** For each `(repo, prover)` (optionally also per file-path bucket), keep an empirical runtime distribution of successful runs from `proof_results` / `proof_jobs`. Use a robust quantile estimate (for example P90 or P95) with a minimum sample count, and fall back to the static timeout when history is too short.
- **Adaptive timeout.** `timeout = clamp(q_p * margin, floor, ceiling)`, where `ceiling` is the configured static timeout, so adaptation can only **shorten** waiting on known-fast provers and never makes an existing gate stricter. A timeout under the adaptive limit triggers one retry at the static ceiling before it is reported, so tightening never creates a new failure.
- **Solver ordering and selection for PR gates.** Order jobs by expected time-to-verdict (success probability ÷ expected runtime, from history). Where the repo's config marks provers as interchangeable for a goal class, allow "first verified wins" with cancellation of the rest. Otherwise run all required provers, because coverage gating needs them. Default: ordering only, with no skipping.
- **Exploration.** Use a small, configurable exploration rate (for example ε-greedy or UCB) so that rarely chosen provers keep current statistics. It is off by default for regulator-mode repos.
- **Config.** Add a new `[scheduler.adaptive]` section (enabled, quantile, margin, floor, min_samples, exploration). It is disabled by default. Also fix or wire up the `job_timeout_seconds` doc/code mismatch noted above.
- **Observability.** Log the chosen timeout, its source (adaptive or static) and the ordering rationale in the job record and the check-run summary.

## Acceptance Criteria

- [ ] With `[scheduler.adaptive]` disabled, job creation, timeouts and verdicts are unchanged (existing tests pass without modification).
- [ ] An adaptive timeout never exceeds the configured static timeout, and never goes below `floor` (property test).
- [ ] A job that times out under an adaptive timeout is retried once at the static ceiling before a `timeout` verdict is reported. The test uses a stub executor.
- [ ] With fewer than `min_samples` history rows, the static timeout is used, and the reported source says so.
- [ ] Regulator-mode coverage percentages are computed over the same set of required provers as before. Ordering changes never change which provers count towards coverage.
- [ ] Replaying a recorded job history in a simulation shows lower median time-to-verdict, with an identical verdict on every replayed job. Attach the simulation script and results to the PR.
- [ ] `cargo test` and `cargo clippy` pass for the workspace; no new `unsafe`; no new external service dependency.

## Out of Scope

- Changing echidna's prover backends, the `echidna.prove.result/1` contract, or echidna-side portfolio reconciliation.
- Learned (neural) algorithm selection. Start with statistics only.
- Changing regulator thresholds or mode resolution.
- Multi-tenant fairness across repositories beyond what `JobLimiter` already does *[unverified]*.

## Open Questions

- Which layer owns per-solver budgets: echidnabot's scheduler, echidna's `PortfolioConfig`, or the ECH-03 Chapel allocator? One owner is needed to avoid conflicting timeouts.
- Is "first verified wins" ever acceptable under regulator mode, or must every enabled prover always run?
- Should runtime history be keyed by file-path bucket, or by goal fingerprint (`tactic_outcomes.goal_fingerprint` *[unverified]*)? Fingerprints are more precise but sparser.
