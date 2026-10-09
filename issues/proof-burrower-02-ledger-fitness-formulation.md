<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# PB-02: feat(ledger): anti-pattern mining and objective fitness formulation from burrow.jsonl for heuristic guidance

- **Repository:** hyperpolymath/proof-burrower
- **Labels:** enhancement, area:ledger, rust, heuristics
- **Area:** Rust / Ledger Analytics / Search Heuristics
- **Provenance:** Drafted from hyperpolymath/echidna. Claims about proof-burrower are marked *[unverified]*: they come from a read-only look at `proof-burrower@be897dd` and have not been built, run or checked by a maintainer. Claims about echidna were checked against echidna `main` at `7fd369d`.

## Summary

The Burrow Ledger (`burrow.jsonl`, append-only JSON Lines) records every reading and attempt, but it is read only through simple filters (`recent`, `by-specialist`, `anti-patterns`, `digest`). Add (1) **anti-pattern mining**, which aggregates the raw per-attempt learnings into ranked, support-counted rules, and (2) a documented **objective fitness function** computed from ledger records. Together they give the swarm (and the PB-01 synthesiser) a single, consistent signal for ordering and pruning tactics.

## Context

- *[unverified]* `crates/burrower-core/src/ledger.rs` defines `LedgerRecord { id, timestamp, goal_hash, goal_id?, goal_excerpt, specialist, approach?, result?, learning?, extra }`. `Ledger` is a file handle with `append`, `read_all`, `query`, `recent`, `by_specialist`, `by_goal_hash` and `anti_patterns_for`.
- *[unverified]* `anti_patterns_for` returns every `Learning` with `pattern_kind == "anti-pattern"` that is visible to the specialist. There is no de-duplication, counting, recency weighting or confidence. One failure and a hundred failures look the same.
- *[unverified]* `RecordResult.status` is documented as `succeeded | failed | partial | abandoned | proposed`. However, `run_playbook` writes `AttemptResult::status_string()`, which also produces `timeout` and `skipped`. Those values are outside the documented set. A miner must handle every value that is actually written, and the doc comment should be fixed.
- *[unverified]* `Learning.pattern_kind` is documented as `positive | anti-pattern | specialisation | boundary`. The oracle path writes `oracle-counter-example` (`crates/burrower-core/src/oracle.rs` module docs), which is also outside the documented set.
- *[unverified]* `goal_hash` is a 16-hex-character non-cryptographic hash. `goal_id` (a UUIDv8 content id) is present only on records written since 2026-10-05. Grouping must prefer `goal_id` and fall back to `goal_hash`.
- *[unverified]* `read_all` skips malformed lines with a warning on stderr. Mining must keep that tolerance and report the skipped count.
- *[unverified]* Successful attempts may carry an `echidna.prove.result/1` receipt in `extra` (`receipt_extra`). Verified in echidna: that receipt's `trust.axioms` lists escape hatches (`sorry`, `Admitted`, ...), and `trust.confidence` is `null` unless it is receipt-backed (`docs/PROVE-RESULT-CONTRACT.adoc`, "Receipt, not warrant"). Fitness must not treat a `null` confidence as zero or as one.

## Proposed Work

- **Normalised view.** Add a pure function that maps a `LedgerRecord` to an `Observation { goal_key, specialist, tactic_script, outcome, failure_class?, duration_ms?, axioms?, timestamp }`. `outcome` covers every status that is actually written (`succeeded`, `failed`, `timeout`, `skipped`, plus the documented ones). Unknown values map to `Other(String)` and are never dropped silently.
- **Anti-pattern mining.** Aggregate observations into rules `(specialist, tactic_script, failure_class, goal-shape feature) → {failures, successes, last_seen}`. Rank them with a smoothed failure rate (for example a Beta prior, or a Wilson lower bound), with optional exponential recency decay. Expose `Ledger::mine_anti_patterns(&MiningConfig) -> Vec<MinedRule>`.
- **Goal-shape feature.** Start simple and deterministic: the specialist's domain plus the set of keyword hits already computed by `Specialist::read`/`relevance` *[unverified]*. Do not add learned embeddings in this issue.
- **Fitness formulation.** Document and implement `fitness(observations for (goal_key, script)) -> Fitness` as a lexicographic tuple, consistent with PB-01:
  1. verified (yes/no);
  2. axiom count from the receipt (fewer is better; unknown is ranked below known-zero);
  3. script length;
  4. median `duration_ms`.
  `Timeout` and `Skipped` count as "no information" for correctness and as worst-case for time. They must not raise the failure rate.
- **CLI.** Add `burrower ledger mine [--min-support K] [--decay HALF_LIFE]` and `burrower ledger fitness --goal <hash|id>`. Use human-readable output by default and add a `--json` option.
- **Doc fix.** Update the `RecordResult.status` and `Learning.pattern_kind` doc comments to list every value that is actually written.

## Acceptance Criteria

- [ ] The normaliser is tested against a fixture ledger that includes every status and pattern kind actually written, plus legacy records without `goal_id`, plus one malformed line.
- [ ] Mining is deterministic and order-independent: shuffling ledger lines gives the same rules in the same order (ties broken by a documented key).
- [ ] A rule with one failure never ranks above a rule with many failures and the same failure rate (support is respected).
- [ ] `Timeout` and `Skipped` observations do not change a rule's failure rate (property test).
- [ ] Fitness ordering matches hand-computed expectations on fixtures, including `null` confidence and missing receipts.
- [ ] The existing `ledger recent | by-specialist | anti-patterns | digest` output is unchanged.
- [ ] `cargo test` and `cargo clippy` pass for the workspace; no new `unsafe`; the ledger file format is unchanged (read-only analytics).

## Out of Scope

- Changing the on-disk ledger schema or rewriting existing records.
- Using mined rules to change playbooks automatically. PB-01 consumes them, and humans decide on promotion.
- Cross-repo ledger aggregation (for example with echidnabot's `tactic_outcomes` table *[unverified]*).
- ML-based pattern extraction.

## Open Questions

- Should mined rules be cached in a sidecar file, or recomputed on every run? This depends on typical ledger size, which is unknown.
- Which recency half-life is reasonable when prover versions change (for example Isabelle releases that rename facts)?
- Should `skipped` caused by a missing prover binary be filtered out completely rather than counted as "no information"?
