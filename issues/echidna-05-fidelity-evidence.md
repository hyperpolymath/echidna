<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# ECH-05: feat(arbitration): consume fidelity evidence, not N re-proofs — type the arbiter's input by alignment certificate and level its verdict

- **Repository:** hyperpolymath/echidna
- **Labels:** enhancement, area:arbitration, area:exchange, epistemic-types, residual-evidence-types, idris2
- **Area:** result arbitration / cross-prover exchange / Idris2 ABI
- **Depends on:** epistemic-types `6a68de3`; residual-evidence-types `97244f5`

## Summary

`ResultArbiter::arbitrate(&[ProverAttempt]) -> ArbitratedVerdict` (`src/rust/verification/result_arbiter.rs`), with `pareto_arbiter.rs` and `dempster_shafer.rs` beside it, fuses N backend outcomes for what it treats as one goal. Alignment between backends is lexical — per-prover synonym tables under `data/synonyms/` with MSC2020 / WordNet / ConceptNet — and the exchange layer (`src/rust/exchange/`, six formats) is the kernel-checked translation tier that ROADMAP stage 6 ("cross-prover semantics — translation actually works") says is not yet real. N re-proofs of N possibly different statements are N warrants for N propositions, not one sound warrant for the source claim.

What the arbiter should consume is fidelity evidence: per backend, a certificate that the formal statement denotes the source claim — a kernel-checked translation through the exchange layer, or a declared correspondence validated by consequence testing — and it fuses only attempts whose certificates agree. In epistemic-types' terms each prover is a standpoint (`K`); a proof is `Epi` for its formal statement; the source claim is `A`; the certificate is the `sound` map from the formal statement's evidence to `A`; without it the fused verdict is belief about the source claim (`no-receipt-reflection`), however many provers agree. Content in a formal statement with no counterpart in the source must not cross, and residual-evidence-types' coarsening gives the direction: a coarse claim transfers to the fine observation, not back (`coarsen-claim`).

Not claimed: a solution to autoformalisation (undecidable in general). Claimed: the arbiter's input and output types change, and a synonym collision can no longer fuse to `sound`. echo-types' order-type "fidelity" (Buchholz, OPEN) is a different object and is not used here.

## Context

Proof work that applies now (sibling artefacts checked at the pinned commits on 2026-10-14):

| ID   | Claim | Status | Artefact |
|------|-------|--------|----------|
| E-1  | `Warrant` / `Epi` / `SoundWarrant` / `sound-epi` | PROVEN | epistemic-types `EpistemicTypes.Warrant` |
| E-2  | agreement without a soundness map is belief | PROVEN | epistemic-types `EpistemicTypes.Applications.RapidNJSkip.no-receipt-reflection` |
| RE-K | composed claims never derive the composed case; `component-left/right` | PROVEN | residual-evidence-types `ResidualEvidence.Composition.compose-claims` |
| RE-D | coarsening transfers one way only | PROVEN | `ResidualEvidence.Composition.coarsen-candidate/case/claim` |
| RE-R | retracting a source retracts what rested on it | PROVEN | `ResidualEvidence.Revision.retract-*`, `dependent-holds` |
| EC-1 | arbiters exist (Rust): result, Pareto, Dempster–Shafer | TESTED | `src/rust/verification/`; `cargo test --lib result_arbiter` |
| EC-2 | exchange layer: OpenTheory, Dedukti, TPTP, SMT-LIB, SMTCoq, Lambdapi | DESIGNED → partial | ROADMAP stage 6a/6b |
| EC-3 | Idris2 ABI gate: zero `believe_me`, postulates, admits | TESTED | `idris2-abi-ci.yml` |

- `ProverAttempt { prover, outcome, elapsed_ms }` carries no statement identity beyond the goal it was handed; `ArbitratedVerdict` is scalar.
- `docs/design/ADVANCED_TYPING_GAP_ANALYSIS.adoc` and `TYPING_CAPABILITIES_COMPARISON.adoc` already compare backend type theories; they are the place to say which pairs can share a kernel-checked term.
- ECH-01..04 are filed (#420–#422, #424); their canonical text is undecided and is not reopened here.

## Proposed Work

1. **Input type.** `ProverAttempt` gains `fidelity: FidelityEvidence` = `KernelTranslation { format, checked_by, term_hash }` | `DeclaredCorrespondence { consequence_tests, failures }` | `None`. `ArbitratedVerdict` gains `level ∈ {sound, epi, belief}`. Policy: any `None` attempt caps the level at `belief`; `sound` requires every fused attempt to carry `KernelTranslation` to the same exchange-layer term (`term_hash` equality); `DeclaredCorrespondence` with zero failures yields `epi`. Existing numeric fusion is unchanged below the level.
2. **ABI.** `src/abi/EchidnaABI/Arbitration.idr`: the three-level verdict as a closed sum whose `Sound` constructor takes the hash-equality proof; total; passes the ABI gate.
3. **Tests.** `tests/arbitration_fidelity_test.rs`: two backends proving two lexically aligned but formally distinct statements (a synonym collision) must not fuse above `belief`; a MiniF2F-aligned pair (aligned across Lean, Isabelle, HOL Light, Metamath, Coq) with kernel-checked translations is the positive control for `sound`; a retracted backend (marked unsound) lowers every verdict that rested on it (RE-R).
4. **Docs.** ROADMAP stage 6 acceptance becomes "a `KernelTranslation` certificate is producible for pair X"; `issues/README.md` gains ECH-05; the gap-analysis documents name which backend pairs can share a term.

As the proofs progress:

- Bidirectional exchange (OpenTheory, 6a) → the forward-then-back translation check becomes a round trip, and a lossless round trip is a Loss-grade-𝟙 witness (resource-algebra `Instances/Loss.agda`) — the certificate gets a grade.
- choreographic-types standpoints → multi-prover protocols as choreographies, with K-CUT-WARRANT giving what each backend can know of the global verdict.
- VeriSimDB → certificates stored as first-class objects with the term hash as key.

## Acceptance Criteria

- [ ] `ProverAttempt` / `ArbitratedVerdict` type change compiles; `cargo test` green; existing arbitration numbers unchanged at level `belief` (regression fixture).
- [ ] `Arbitration.idr` passes `idris2-abi-ci.yml`.
- [ ] Synonym-collision test cannot reach `sound`; MiniF2F positive control reaches `sound`; retraction test lowers dependent verdicts.
- [ ] ROADMAP, gap-analysis docs and `issues/README.md` updated; the ECH-01..04 canonical-text question is not reopened here.
- [ ] CodeRabbit findings and CI anomalies addressed per the standing rule.

## Out of Scope

- Making the Dedukti/OpenTheory bridges real (stage 6 itself).
- GNN tactic suggestion.
- VeriSimDB standup.
- The Chapel island migration (ECH-03).

## Open Questions

- Is Dempster–Shafer fusion retained for same-encoding automated provers only, or across kernels under a certificate?
- Who runs consequence testing for `DeclaredCorrespondence`, and against which corpus beyond MiniF2F?
