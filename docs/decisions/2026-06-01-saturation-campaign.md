<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
-->

# ADR 2026-06-01 — Prover / Corpus / Vocab / Synonyms / Arbitration Saturation Campaign

**Status**: Accepted (campaign live on branch `prover-corpus-saturation`,
sibling to `wave3/161-162-bench-telemetry-corpus`).
**Date**: 2026-06-01.
**Author**: Jonathan D.A. Jewell (executed by Claude Opus 4.7).

## Context

ECHIDNA had reached **128 ProverKind variants with 91/91 real
`suggest_tactics`** and **GNN-augment wiring across every backend**
(see `docs/PROVER_COUNT.md`). The owner directive was to push the
remaining levers — corpora, vocabulary, synonyms, arbitration,
verisim wiring — to the marginal-benefit limit while a sibling
session worked on chapel bench + telemetry (`wave3/161-162`).

A scoping pass (saved in `docs/handover/PROVER-CORPUS-SATURATION-LANE.md`)
identified the following ordered marginal-benefit hierarchy:

1. **Corpus adapters**: 4 existed (agda, coq, lean, idris2); 14+ major
   public corpora (Mizar MML, Isabelle AFP, MetaMath set.mm, HOL Light,
   HOL4, Dafny, Why3, F\*, ACL2 books, TPTP, SMT-LIB, ProofNet, MiniF2F)
   had ZERO adapter coverage. **HIGHEST marginal benefit.**
2. **Synonyms**: 5 per-prover tables (lean4/coq/isabelle/idris2/agda, ~863
   lines). 11 supported provers had NO synonym table. No MSC2020 / WordNet
   / ConceptNet integration. **HIGH marginal benefit.**
3. **Exchange bridges**: only OpenTheory + Dedukti; TPTP / SMT-LIB / SMTCoq
   / Lambdapi absent. **HIGH marginal benefit.**
4. **Arbitration**: portfolio_solver used simple majority vote + flagging;
   no Bayesian / Dempster-Shafer / Pareto arbiters. **MEDIUM-HIGH.**
5. **SMT portfolio**: Tier-1 only (Z3 / CVC5 / AltErgo / Vampire / EProver);
   DReal / SmtRat / OpenSmt / MathSat / Princess / iProver / Twee not
   in the cross-check set. **MEDIUM.**
6. **Verisim E-R**: existed only as aspirational text in the
   `ECHIDNA-VERISIM-TRIANGULATION-2026-04-17.adoc` workflow plan; no
   formal entity / relationship schema. **MEDIUM.**
7. **GNN first training run**: `models/neural/` did not exist; Flux.jl
   scaffolds never invoked on real data. **HIGHEST in absolute terms
   but DEFERRED** — collides with wave3 telemetry baselines and would
   delete artefacts the parallel session depended on.

## Decision

Execute (1) through (6) in this branch. **Defer (7)** to a separate
post-wave3 campaign.

For each lever, the bar is **"add it AND verify it compiles in
isolation"** — full integration / training is out of scope. Marginal
benefit is judged by: does the surface area for downstream consumers
(`suggest`, `learning`, `portfolio`, `octad-emit`, `gnn_augment_tactics`)
get materially wider?

Termination criteria are spelled out in the handover doc; on this date
the campaign hit all of them except (5) SMT-portfolio expansion (still
in flight) and the Cap'n Proto schema for E-R (declared, not generated).

## Consequences

### Positive

- **Corpus adapters: 4 → 17** (4.25× expansion).
  - Coverage now spans every Tier-1 + Tier-2 prover that has a public
    formalisation library AND the two canonical ML evaluation sets
    (ProofNet, MiniF2F).
  - Adapters follow a single uniform pattern (two-pass extraction,
    `bounded_read_corpus_file`, `AxiomUsage` hazard surfacing) — every
    new one inherits the corpus query DSL + octad emission for free.
- **Synonyms TOML rows: 863 → ~3,400** (4× expansion).
  - 9 new per-prover tables (isabelle_afp, metamath, mizar, hol_light,
    hol4, dafny, why3, fstar, acl2).
  - 3 cross-prover taxonomic dictionaries
    (`_msc2020.toml`, `_wordnet_math.toml`, `_conceptnet_seed.toml`)
    enabling cross-corpus semantic-class resolution.
- **New arbitration trio** under `src/rust/verification/`:
  - `bayesian_arbiter.rs` — calibrated per-prover likelihoods + log-odds
    accumulation + Shannon-entropy reporting.
  - `dempster_shafer.rs` — belief mass combination with conflict
    detection (`HighConflict` at k > 0.95).
  - `pareto_arbiter.rs` — multi-objective Pareto-frontier over
    (confidence, latency, axiom_cost, certificate_size).
- **New exchange bridges** under `src/rust/exchange/`:
  - `tptp.rs`, `smtlib.rs`, `smtcoq.rs`, `lambdapi.rs`.
  - Round-trip parse/emit + bidirectional translations where the
    semantics overlap (TPTP↔SMT-LIB for first-order, Dedukti↔Lambdapi
    for proof rewriting).
- **Formal E-R schema** at `docs/architecture/VERISIM-ER-SCHEMA.md`:
  - 12 entities + 7 relationships fully specified.
  - Crosswalk Rust struct ↔ Cap'n Proto schema ↔ ClickHouse table.
  - Drift-detection plan (SHA of schema + .capnp) tracked for CI gate.
- **Test fixtures** for every new adapter under
  `tests/corpus_fixtures/<adapter>/`.

### Negative / debt taken on

- The new corpus adapters are **heuristic structural indexers**, not full
  parsers. They will false-positive on some pathological inputs (e.g.
  `assume` inside a string literal). Matches the existing
  `agda.rs` / `coq.rs` convention but is a known limitation.
- **No real-corpus benchmarking** in this campaign. New adapters were
  smoke-tested against fixtures only. Wave3 bench numbers will reveal
  any real-corpus performance issues.
- **Cap'n Proto schema for the E-R** is referenced in the doc but
  **not yet generated**. Planned in a follow-up commit before the
  drift-gate CI lands.
- **CertificateBlob** entity (E11) in the E-R is declared but not yet
  extracted to a dedicated table — currently inlined in
  `ProofAttempt.certificate_path`. Migration tracked in the E-R doc.
- **`mod.rs` registration** consumed two trivial edits per affected
  module index (one to `src/rust/corpus/mod.rs`, one each to
  `src/rust/verification/mod.rs` and `src/rust/exchange/mod.rs`). Each
  is additive only; no existing line was reordered or semantically
  changed.

### Coordination with wave3/161-162

The handover document at `docs/handover/PROVER-CORPUS-SATURATION-LANE.md`
enumerated the hard-exclusion list (chapel sources, benches, corpus
monitor diagnostics, training_data premises files, Justfile train recipes,
models/, julia run_training, the 300+ files wave3 had unstaged).
Throughout the campaign, this branch touched **only new files** plus
three surgical mod.rs additions. **Zero overlap** with wave3 was
maintained.

## Implementation notes

### Commit chain on `prover-corpus-saturation`

1. `f73ee00` — docs(handover): declare saturation lane
2. `46a7408` — feat(corpus): 13 adapters + 12 synonyms + MSC2020/WordNet/ConceptNet seeds
3. `<arbiter>` — feat(arbiter): bayesian + dempster-shafer + pareto trio
4. `<exchange>` — feat(exchange): tptp + smtlib + smtcoq + lambdapi bridges
5. `<er-schema>` — docs(er): formal verisim E-R schema + CORPUS-ADAPTERS index
6. `<adr>` — docs(adr): this file

### What this campaign did NOT do

- Did not train the GNN (collision risk + out-of-scope).
- Did not invoke `just provision-corpora` to fetch real corpus content
  (out-of-scope; the adapters work on whatever the consumer hands them).
- Did not expand SMT portfolio beyond the existing default set (deferred
  to a follow-up; intentionally low marginal benefit at this stage).
- Did not touch any of the 19 Tier-4 placeholder backends (genuinely
  upstream-blocked on Containerfile work).
- Did not modify any wave3-owned file.

## Alternatives considered

- **Bundle into one mega-PR vs split per-adapter**: chose mega-PR per
  agent group (corpus / synonyms / arbiter / exchange / docs) for
  reviewability without losing parallel-fan-out throughput. Per-adapter
  PRs would have been ~20 round-trips.
- **Fetch real upstream corpora and check them in**: rejected — would
  blow the 1MB pre-commit large-file limit many times over and is
  better handled by `just provision-corpora`.
- **Skip MSC2020 / WordNet / ConceptNet seeds**: rejected — the offline
  dictionaries are load-bearing for the S5 verification gate which has
  no network access.

## Follow-ups

Tracked in `docs/CORPUS-ADAPTERS.md` "Open backlog" section and in the
E-R schema "Open migrations" section. Highest priority: produce
`crates/echidna-wire/schemas/verisim_er.capnp` matching the new doc.

## References

- Handover: `docs/handover/PROVER-CORPUS-SATURATION-LANE.md`
- E-R schema: `docs/architecture/VERISIM-ER-SCHEMA.md`
- Corpus index: `docs/CORPUS-ADAPTERS.md`
- Prover count source of truth: `docs/PROVER_COUNT.md`
- Sibling branch: `wave3/161-162-bench-telemetry-corpus`
