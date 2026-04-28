<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# 2026-04-28 — Corpus, design-search, swarm, and the N-dim VeriSim plan

ADR-style record of the decisions made on 2026-04-28 while wiring
Echidna against echo-types' Buchholz / Brouwer programme. Two
threads: a forward push on the actual proof targets (Phase 1.3
`_≤_` redesign, unbudgeted `wf-<ᵇʳᶠ_`) and an underlying capability
campaign (corpus, simulated annealing over design space, swarm,
multi-axis query DSL).

## Origin

User asked to attack two open Agda proofs in `echo-types`:

1. **Phase 1.3** — monotonicity lemmas for `Ordinal.Brouwer.Arithmetic`,
   blocked because the current `data _≤_` axiomatisation makes
   `osuc-mono-≤ : x ≤ y → osuc x ≤ osuc y` non-trivial in the `≤-lim`
   case (premise `x ≤ f n` doesn't lift to `osuc x ≤ f n`).
2. **Unbudgeted `wf-<ᵇʳᶠ_`** — `RecursiveSurfaceBudget.agda` carries a
   `BudgetedBT = ℕ × BT` budget; goal is `WellFounded _<ᵇʳᶠ_` directly
   without it, under `--safe --without-K`.

Explicit framing from the user: *"the key thing is us learning about
echidna and making it amazing in the course of doing it — remember,
this is about solving it, but it is about doing so with echidna not
doing it all on your own"*. Capability-first.

## Decisions

### D1. The proof targets are first design problems, not tactic problems

Phase 1.3 isn't blocked on a tactic — it's blocked on the *shape of
the axiomatisation*. The fix lives in design space: should `_≤_` be a
`data` type or a recursive function? Which constructors should it
have? This is combinatorial design search, not proof search.

Same for unbudgeted `wf-<ᵇʳᶠ_`: the design knob is the rank function
`rank : BT → Ord`, and the choice between `psi-rank ν α` /
`ω-rank ν ⊕ α` / `osuc (ω-rank ν) ⊕ α` etc. determines how many
downstream lemmas are needed.

Echidna's existing `learning/mcts.rs` searches over tactic sequences
within a fixed signature. Both targets are outside that surface.

→ Built `learning/design_search.rs` with simulated annealing over
the *signature itself*. Energy is symbolic (no Agda recompile per
candidate), lex-ordered: (mono-blockers, K-elim hazards, ctor count,
style preference). Generic `DesignProblem` trait so future redesigns
plug in the same way.

### D2. SA, then a swarm of SAs

Single-chain SA confirms the design direction quickly (Recursive
style for `_≤_`; `psi-rank ν (rank α)` for the BT rank). Building a
swarm on top is the obvious next step:

* The 007 swarm choreography: N agents run independent SA chains,
  periodically broadcast best-so-far, peers may adopt strictly-better
  states. Cross-pollination via in-process `tokio::sync::mpsc`
  channels — protocol-shape compatible with the BoJ coord bus
  (`Heartbeat`, `Adopt` messages), so dispersed-process swarms reuse
  the same wire format.

→ Built `agent/swarm.rs`. Verified on `brouwer-leq` with 6 agents ×
800 iterations: all converge to the same `[0, 0, 1, 0]` energy.

### D3. Honest energy beats optimistic energy

First SA implementation modelled `data + LimBelow` as unblocking
`osuc-mono-≤`. Hand-traced and discovered this is wrong — in the
`≤-lim n q` case where `q : x ≤ f n` and goal is `osuc x ≤ osuc (olim
f)`:

* `≤-suc → ≤-lim k`: needs `osuc x ≤ f k`; recursive call only
  yields `osuc x ≤ osuc (f n)`, off by one.
* `LimBelow`: requires `∀ k. f k ≤ osuc (olim f)`; produces
  `olim f ≤ osuc (olim f)`, not `osuc x ≤ osuc (olim f)` — link to
  `x` is lost.

Only Recursive style or an explicit `≤-cong-suc` constructor truly
unblocks. Refined the energy in
`design_search::brouwer::mono_osuc_ok` accordingly.

→ Lesson: when the SA energy is symbolic, hand-trace the
predicates against actual proof goals before trusting them.

### D4. Capability-first, then apply

Built the recommendation infrastructure (corpus + SA + swarm + rank
search) before attempting the Agda translation. Reasoning:

* The recursive `_≤_` redesign is a non-trivial structural-induction
  proof exercise (`≤-step` case `α = osuc α', β = olim f` requires
  careful Σ-witness picking). Hand-writing it without Agda REPL
  would burn many compile cycles.
* The right next capability is wiring `provers/agda.rs` so Echidna
  can compile candidate proofs as part of the design loop.
* A handoff document in `echo-types/docs/echidna-design-search-2026-04-28.adoc`
  captures the recommendation graph + risks + repro commands so
  the actual Agda work can pick up cleanly in a later session.

### D5. The corpus needed N-dimensional indexing across provers

User pointed out the original 2-coord index (by_name, by_qualified) is
nowhere near what's needed. Reasoning followed: VeriSim's 8-modality
octad is the right substrate; cross-prover semantic classes are how
the 105 prover backends become a federation rather than 105 silos.

Plan landed in 6 commits:

| Step | Capability |
|---|---|
| 1 | Reverse-dep index — Graph octad (forward + reverse) |
| 2 | Coq + Lean 4 + Idris 2 adapters + `semantic_class` field |
| 3 | 8-modality octad emission as JSONL |
| 4 | Tensor metrics (proof_depth, fanin/out, recursive, K-elim risk, head_symbol) |
| 5 | Vector embeddings (hashing-trick offline; GNN-ready) |
| Capstone | Multi-axis query DSL |

### D6. Hashing-trick now, GNN later

The Vector octad needs embeddings, but Julia ML server at port 8090
is scaffold-only (per echidna's CLAUDE.md: `models/neural/` doesn't
exist; cosine fallback returns zeros). Building on a non-functional
backend = building on sand.

→ Used hashing-trick (FNV-1a → 32-dim L2-normalised feature vector)
as default `Embedder`. Offline, deterministic, free, dimension-
matched to the GNN's `FEATURE_DIM`. When the GNN server is primed,
swap one trait impl. Vector octad's `model` field reflects which
embedder produced each row — replays distinguish them.

### D7. Bennettian / Landauer caveat

User asked whether the design-search stack is near-Landauer, very
Bennettian, Shannon-violating. Honest answer: no. The corpus IS
provenance-preserving and content-addressed (a Bennettian flavour);
the SA annealer freely erases bits (Metropolis decisions, rejected
candidates, temperature updates). Real reversibility integration is
the next thread — `januskey/reversible-core`'s `ContentStore` is the
natural backing for the SA trace ledger.

**Adjacency to** `redeem(thermo): honest Landauer/Bennett bounds for
finite-domain echoes` (echo-types commit, branch
`agda/buchholz-shared-binder-psi-alpha`): that proof effort is the
*real* Landauer/Bennett work in this estate; the corpus stack is a
substrate that ought to align with it. Cross-reference noted; full
integration deferred.

## Recommended next moves (priority order)

1. **Wire SA energy in `learning/buchholz_rank.rs::blockers` to
   consume the new query DSL.** Energy becomes data-driven over the
   corpus, not hand-coded predicates. ~1-day refactor.
2. **Apply Phase 1.3 redesign in Agda.** Multi-session; needs Agda
   REPL. Recommendation document in echo-types is the starting
   point.
3. **Reversibility integration.** Move SA trace into `reversible-core`'s
   ContentStore; uncompute rejected candidates. Closes the
   Bennettian loop.
4. **GNN embeddings.** Prime the Julia ML pipeline against echo-types
   + jtv + eclexia corpora. Replaces the hashing-trick fallback.
5. **Write the unbudgeted `wf-<ᵇʳᶠ_` Agda proof** per
   `learning::buchholz_rank` recommendation. Three downstream
   blockers: rank-mono-<ᵇ (Phase 2.2), ⊕-mono-<-right (Phase 1.3,
   counted twice).

## Commits

11 in echidna (10 pushed today after rebase from origin):

```
8265f9b feat(corpus): multi-axis query DSL — N-dim plan capstone
4558e61 feat(corpus): vector-octad embeddings — Step 5 of N-dim plan
3148d14 feat(corpus): tensor-octad metrics — Step 4 of N-dim plan
8604909 feat(corpus): 8-modality octad emission — Step 3 of N-dim plan
572b9b7 feat(corpus): Coq + Lean 4 + Idris 2 adapters; cross-prover semantic classes
e599868 feat(corpus): reverse-dep index — Step 1 of N-dim VeriSim plan
ca56b96 feat(learning): rank-function search for unbudgeted wf-<ᵇʳᶠ_
fca18d5 feat(agent): swarm dispatcher + SA energy refinement
ae68579 feat(learning): SA design-search — proof-design space, not tactic space
85c2b55 feat(corpus): project-corpus indexer + Agda adapter + ordinal/WF synonyms
```

1 in echo-types:

```
12a9fea docs(buchholz): Echidna design-search handoff for Phase 1.3 + unbudgeted wf-<ᵇʳᶠ_
```

## Test posture

1059 lib tests pass (16 added).
36 corpus-specific tests; 3 echo-types fixtures verified (640 / 108 /
147 / 93 entries across Agda / Coq / Lean / Idris).
Cross-prover query end-to-end: `well-foundedness` joins WellFounded
(Agda/Lean/Idris) with well_founded (Coq).

## Open at end-of-session

Tasks #4 and #5 (Apply Echidna to Phase 1.3 / unbudgeted wf-<ᵇʳᶠ in
Agda) remain open by design. The framework is built; the Agda
translation is the next session's work.
