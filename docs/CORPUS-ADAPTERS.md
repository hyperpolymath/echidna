<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
-->

# Corpus Adapters — Index

**Status**: canonical. Updated 2026-06-01 as part of the saturation campaign
(see `docs/decisions/2026-06-01-saturation-campaign.md`).

Each adapter is a `pub fn ingest(root: &Path) -> Result<Corpus>` in
`src/rust/corpus/<name>.rs`, structurally indexing a proof tree into
`Corpus` (`src/rust/corpus/mod.rs:138`). Hazards (axioms, sorry,
believe_me, cheat, …) populate `AxiomUsage` per entry.

## Adapter table

| Adapter | File extensions | Canonical source URL | Hazard flags surfaced | Status |
|---|---|---|---|---|
| **agda** | `*.agda` | <https://github.com/agda/agda> | postulate, believe_me, assert_total, sorry, trustme | shipped pre-2026-04 |
| **coq** | `*.v` | <https://github.com/coq/coq> | Axiom, Parameter, Admitted | shipped pre-2026-04 |
| **lean** | `*.lean` | <https://github.com/leanprover-community/mathlib4> | sorry, axiom, admit | shipped pre-2026-04 |
| **idris2** | `*.idr` / `*.ipkg` | <https://github.com/idris-lang/Idris2> | believe_me, assert_total, postulate | shipped pre-2026-04 |
| **isabelle** | `*.thy` | <https://www.isa-afp.org/> | axiomatization, axiom, sorry, oops, consts, nitpick, quickcheck | **NEW 2026-06-01** |
| **metamath** | `*.mm` | <https://github.com/metamath/set.mm> | `$a` axiom usage, `?` admitted in proof | **NEW 2026-06-01** |
| **mizar** | `*.miz`, `*.abs` | <http://mizar.org/version/8.1.14/mml/> | `@proof` sketch, commented-theorem, consider-without-proof | **NEW 2026-06-01** |
| **hol_light** | `*.ml` (HOL Light filter) | <https://github.com/jrh13/hol-light> | new_axiom, mk_thm, free ASSUME, failwith "not yet" | **NEW 2026-06-01** |
| **hol4** | `*Script.sml` | <https://github.com/HOL-Theorem-Prover/HOL> | new_axiom, mk_thm, cheat, CHEAT_TAC | **NEW 2026-06-01** |
| **dafny** | `*.dfy` | <https://github.com/dafny-lang/dafny> | assume, `:axiom`, extern, expect, `:fuel 0` | **NEW 2026-06-01** |
| **why3** | `*.mlw`, `*.why` | <https://gitlab.inria.fr/why3/why3> | axiom, val function (uninterpreted), val lemma, assume, absurd | **NEW 2026-06-01** |
| **fstar** | `*.fst`, `*.fsti` | <https://github.com/FStarLang/FStar> | assume, admit, magic, Obj.magic, unsafe_coerce, admit_smt_queries | **NEW 2026-06-01** |
| **acl2_books** | `*.lisp`, `*.acl2` | <https://github.com/acl2/acl2> | defaxiom, defstub, skip-proofs (top-level surfaced), ld-skip-proofsp, local-in-theory-nil | **NEW 2026-06-01** |
| **tptp** | `*.p`, `*.tptp` | <https://tptp.org/> | no_conjecture (axiom-only file), TFF/THF dialects not fully supported | **NEW 2026-06-01** |
| **smtlib** | `*.smt2`, `*.smt` | <https://smt-lib.org/benchmarks.shtml> | status_unknown, uninterpreted (declared-not-defined), unnamed_bang_pattern | **NEW 2026-06-01** |
| **proofnet** | `*.jsonl` | <https://github.com/zhangir-azerbayev/ProofNet> | sorry, admit, axiom, no_formal_proof | **NEW 2026-06-01** |
| **minif2f** | `*.lean`, `*.thy`, `*.ml`, `*.mm`, `*.v` (multi) | <https://github.com/openai/miniF2F> | sorry, admit, Admitted, empty_body, todo | **NEW 2026-06-01** |

## Coverage summary

**Pre-2026-04**: 4 adapters (agda, coq, lean, idris2).
**Post-2026-06-01**: 17 adapters — 4.25× expansion.

## Test fixtures

Every adapter has a minimal smoke fixture under
`tests/corpus_fixtures/<adapter>/`. Fixtures cover the
happy-path decl parse plus at least one hazard-detection case.
They are intentionally tiny — the goal is "compile + smoke
correctness", not "extensive coverage". Larger evaluation corpora
live outside the repo (mathlib4 etc. are fetched at training time
via `just provision-corpora`).

## Cross-prover synonyms

Every adapter has a corresponding per-prover synonyms TOML at
`data/synonyms/<adapter>.toml` listing tactic / decl / hazard
vocabulary with canonical-and-aliases form. Plus three cross-prover
taxonomic dictionaries (underscore-prefix; merged into
`SynonymTable` via `merge_external()`):

- `_msc2020.toml` — 87 MSC2020 codes for cross-domain classification
- `_wordnet_math.toml` — ~80 lemmas from WordNet 3.1 math sub-hierarchy
- `_conceptnet_seed.toml` — ~55 pre-fetched ConceptNet 5.7 edges
  for offline-resilient semantic_class resolution

## Wiring into downstream consumers

1. **suggest**: `src/rust/suggest/synonyms.rs::SynonymTable::load_all()`
   reads per-prover TOMLs. The cross-prover dictionaries are loaded
   via `with_msc2020()` / `with_wordnet()` / `with_conceptnet()` (new
   methods landing in the same campaign).

2. **octad emission**: `src/rust/corpus/octad.rs::Corpus::emit_octads()`
   walks any `Corpus` produced by any adapter and emits 8-modality
   octads into VeriSimDB (see `docs/architecture/VERISIM-ER-SCHEMA.md`).

3. **GNN training**: `src/julia/training/train.jl` consumes
   `premises_<adapter>.jsonl` files under `training_data/`. The new
   adapters can produce these files via
   `cargo run --bin corpus-emit -- --adapter <name> --output training_data/premises_<name>.jsonl`
   (TODO — wire CLI).

## When to add a new adapter

- Upstream proof library has > 100 declarations AND
- The library has a stable file format (not a daily-changing CI artifact) AND
- A real prover backend exists in `src/rust/provers/` OR
  it's a recognised ML evaluation set (ProofNet, MiniF2F, NaturalProofs, …).

Drop the new file under `src/rust/corpus/<name>.rs`, add it to
`mod.rs`, write at least 2 unit tests, add a fixture under
`tests/corpus_fixtures/<name>/`, add an entry to this index, and
add the per-prover synonyms TOML at `data/synonyms/<name>.toml`
(omit if it's a format like TPTP/SMT-LIB rather than a prover).

## Open backlog (next saturation wave)

- `src/rust/corpus/naproche.rs` (Naproche-SAD)
- `src/rust/corpus/mathcomp.rs` (Coq MathComp — distinct from generic coq.rs)
- `src/rust/corpus/iris.rs` (Coq Iris separation logic)
- `src/rust/corpus/cubical_agda.rs` (Cubical Agda stdlib)
- `src/rust/corpus/tlaps.rs` (TLA+ Proofs)
- `src/rust/corpus/pvs.rs` (PVS theories)
- `src/rust/corpus/naturalproofs.rs` (Bobrow et al. NL→Coq dataset)
- `src/rust/corpus/alphaproof.rs` (DeepMind 2024 olympiad set)

Drop here as upstream URLs are confirmed and at least one production
consumer needs each.

## Type-discipline detection

See `docs/architecture/TYPE-DISCIPLINE-EMBEDDING.md` for the canonical
specification.

Every adapter calls `detect_disciplines(adapter_name, statement, proof,
registry)` (`src/rust/disciplines/detector.rs`) on every `CorpusEntry`
post-extraction. The detector returns `Vec<TypeDiscipline>` against the
39-discipline taxonomy used by the HP type-checker ecosystem
(`src/rust/provers/hp_ecosystem.rs:63-126`, dispatched via TypedWasm
Sigma parameters), and the result is surfaced as
`CorpusEntry.type_discipline_tags`.

The tags flow through `SemanticPayload`
(`src/rust/verisim_bridge.rs`, new field per `VERISIM-ER-SCHEMA.md`
E2 / Cap'n Proto `@11`) into VeriSimDB and into the Julia GNN
training pipeline as a 39-dim multi-hot feature vector per example.
See sub-table §4 of `TYPE-DISCIPLINE-EMBEDDING.md` for the per-adapter
× per-family expected-hit-frequency matrix.
