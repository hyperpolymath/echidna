<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# PB-01: feat(swarm): combinatorial tactic playbook synthesis using delta/partial neighborhood evaluation (ParadisEO-mo)

- **Repository:** hyperpolymath/proof-burrower
- **Labels:** enhancement, area:swarm, rust, search-tactics
- **Area:** Rust / Local Search over Tactic Scripts
- **Provenance:** Drafted from hyperpolymath/echidna. Claims about proof-burrower are marked *[unverified]*: they come from a read-only look at `proof-burrower@be897dd` and have not been built, run or checked by a maintainer. Claims about echidna were checked against echidna `main` at `7fd369d`.

## Summary

Today each specialist's playbook is a fixed, hand-written list of single tactic scripts that is tried in order. Add a **local-search synthesiser** that builds composite tactic scripts (sequences and combinators of existing `TacticTemplate`s) by exploring a neighbourhood of moves. Use the ParadisEO-MO idea of **delta (incremental) evaluation**: score a neighbour from cached ledger outcomes and cheap partial checks wherever possible, and pay for a full `echidna prove` call only when that is unavoidable.

## Context

- *[unverified]* `crates/burrower-core/src/attempt.rs` defines `TacticTemplate { name, script, description }` and `Playbook { specialist, tactics: Vec<TacticTemplate> }`. `run_playbook` tries every tactic in order, writes one probe file per tactic (`generate_probe`, an Isabelle theory that `imports Main`), and runs `run_probe` for each.
- *[unverified]* `crates/burrower-core/src/specialist.rs` has three built-in specialists (`Algebraist`, `OrderTheorist`, `Combinatorialist`), each with a static `playbook()`. `Swarm::attempt_all` skips specialists below `SWARM_RELEVANCE_THRESHOLD` (0.02) and runs each remaining playbook in full. There is no early exit after the first success, no reordering and no composition.
- *[unverified]* Some playbook entries are already hand-made composites (for example `by (simp; linarith)` and `by (transfer, simp add: algebra_simps)`). This shows that combinators are useful, but they are not generated.
- *[unverified]* `AttemptResult` has the variants `Succeeded { duration_ms, receipt }`, `Failed { error, duration_ms }`, `Timeout` and `Skipped { reason }`. `Timeout` carries no duration.
- *[unverified]* `derive_learning` records successes as `positive` learnings and failures as `anti-pattern` learnings in the ledger. Failures are sorted into `undefined-reference`, `tactic-mismatch`, `structural-mismatch` and `generic-failure`. These classes can drive move selection.
- Verified in echidna: probes are checked by `echidna prove`, which can emit one `echidna.prove.result/1` JSON line (`docs/PROVE-RESULT-CONTRACT.adoc`). Its `status` is one of `verified`, `failed`, `error`, `timeout`, `unknown`, and it includes `duration_ms` and `trust.axioms`. The contract has **no partial-progress field** (for example, remaining subgoals). Any partial evaluation that needs subgoal counts would either need a new, additive contract field in echidna or have to parse prover output inside proof-burrower.
- ParadisEO is referenced only in the roadmap. This issue is about the *algorithms* (neighbourhoods, delta evaluation, local search). It does not require a C++ ParadisEO dependency.

## Proposed Work

- **Solution representation.** A candidate is a short sequence of tactic steps joined by combinators (`;`, `,`, `<|>`-style fallback where the prover supports it). Each step is drawn from the specialist's existing `TacticTemplate`s plus their simplifier-set variants. Cap the length (for example ≤ 3 steps) so the space stays small.
- **Neighbourhood moves.** Define these as pure functions: insert a step, delete a step, swap adjacent steps, replace a step's tactic, add or remove a simp-set argument. Each move must have a stable textual identity, so results can be cached.
- **Delta / partial evaluation, cheapest first:**
  1. *Ledger lookup:* if `(goal_id, script)` already has a recorded outcome, reuse it at no prover cost.
  2. *Anti-pattern pruning:* reject neighbours whose prefix matches a recorded `anti-pattern` learning for this specialist and goal shape.
  3. *Prefix evaluation (optional, behind a flag):* when a prefix's outcome is known to fail with `tactic-mismatch`, skip all extensions of that prefix.
  4. *Full evaluation:* run `run_probe` only for surviving neighbours, within a per-goal prover-call budget.
- **Search driver.** Use first-improvement hill climbing with a tabu list over move identities, plus an iteration cap and a prover-call cap. Stop on the first `Succeeded`. Make the driver deterministic for a given seed.
- **Fitness.** Lexicographic: (1) verified beats everything else; (2) fewer `trust.axioms`; (3) shorter script; (4) lower `duration_ms`. Treat `Timeout` and `Skipped` as the worst values and never count them as evidence that a tactic is wrong.
- **Ledger.** Record each synthesised attempt the same way `run_playbook` already does. Put the move trace in `extra` so that later runs can replay or prune it.
- **CLI.** Add an opt-in flag on `burrower attempt` (for example `--synthesise --budget N`). Default behaviour stays the same.

## Acceptance Criteria

- [ ] With `--synthesise` off, `burrower attempt` output and ledger records are byte-for-byte unchanged on the existing tests.
- [ ] Unit tests for every move operator, including empty-sequence and maximum-length edge cases.
- [ ] Delta evaluation is tested with a stub prover: a neighbour whose `(goal_id, script)` is already in the ledger triggers **no** prover call, and the stub's call count proves it.
- [ ] The prover-call budget is a hard limit: the stub prover is never called more than `N` times per goal.
- [ ] The search is deterministic for a fixed seed and a fixed ledger.
- [ ] `Timeout` and `Skipped` outcomes never create `anti-pattern` learnings through the synthesiser.
- [ ] On a fixed goal set where a known composite closes a goal that no single playbook tactic closes, the synthesiser finds it within the budget. Record the goal set and results in the PR.
- [ ] `cargo test` and `cargo clippy` pass for the workspace; no new `unsafe`; no new network dependency.

## Out of Scope

- Changing echidna's `echidna.prove.result/1` contract. If subgoal counts are needed, file a separate echidna issue for an additive field.
- Provers other than the ones proof-burrower already targets (Isabelle probes today *[unverified]*).
- Learned (neural) move selection. That belongs to the GNN/ranking roadmap.
- Any ParadisEO C++ dependency.

## Open Questions

- Should synthesised scripts that succeed be added back to the specialist's static playbook, or stay only in the ledger?
- What per-goal prover-call budget is acceptable in CI and locally? It drives the useful neighbourhood size.
- Is prefix evaluation sound for every combinator? (`;` applies to all subgoals and `,` sequences, so a failing prefix does not always mean a failing extension under fallback combinators.)
