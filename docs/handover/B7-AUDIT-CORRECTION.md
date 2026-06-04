<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# B7 audit correction — HP ecosystem backends are NOT corpus-only

**Status**: Correction.
**Origin**: The 2026-06-03 "what stops echidna from running proof work
across the estate" punch list listed **B7** as:

> _HP type-checker ecosystem (13 provers) corpus-only — KatagoriaVerifier,
> Modal/Session/Choreographic/Epistemic/Refinement/Echo/Dependent/QTT/
> Effect-Row/Tropical/TypeLL backends missing. Rust adapters not
> scaffolded in `src/rust/provers/`. Corpus contributes to vocab/training
> only._

That characterisation is incorrect. This memo replaces B7's "scaffold
missing adapters" framing with what is actually missing.

## What is actually in tree (verified 2026-06-03)

### Unified `HPEcosystemBackend`

`src/rust/provers/hp_ecosystem.rs:50-153` defines
`HPEcosystemBackend`, a full `ProverBackend` implementation that:

- Pattern-matches on `ProverKind` to select the upstream CLI
  (`typell`, `katagoria`, `tropical-type-check`) and discipline tag
  (`echo`, `session`, `qtt`, `effect-row`, ...) — see
  `hp_ecosystem.rs::upstream()` lines 63-126.
- Implements `parse_file`, `parse_string`, `apply_tactic`, and
  `verify_proof` against the upstream binary — lines 156-330.
- Injects a `#discipline:` header when the source lacks one (lines
  196-205), so estate consumers don't need to know the wire format.

### Routing in `ProverFactory::create`

`src/rust/provers/mod.rs:1774-1824` routes:

| ProverKind                                            | Backend                                          |
|-------------------------------------------------------|--------------------------------------------------|
| `TypeLL`, `KatagoriaVerifier`                         | `hp_ecosystem::HPEcosystemBackend`               |
| 39 other `*TypeChecker` variants incl. `EchoTypeChecker`, `TropicalTypeChecker` | `typed_wasm::TypedWasmBackend::for_kind` |

Both routes exist on `main`. None of the 41 enum variants falls
through to "unsupported".

### Test infrastructure

`tests/common/mod.rs:114`, `:185`, `:245` already special-case
`k.is_hp_ecosystem()` for executable / args / default-binary resolution
in the prover-smoke harness. `tests/gnn_augment_integration.rs:545`
covers `test_hp_ecosystem_gnn_wires_top_premise`.

## What is genuinely outstanding for these backends

The audit's underlying intuition (estate proof work won't run end-to-end
on these provers) is correct — but the gap is downstream of the
scaffold, not the scaffold itself:

1. **Upstream binaries are not packaged.** `typell`, `katagoria`, and
   `tropical-type-check` are referenced from `hp_ecosystem.rs::upstream()`
   but none of them ship in any of echidna's Containerfiles or the
   Guix manifest. `manifests/live-provers.scm` covers Z3, CVC5, Lean4,
   Coq, Agda, Isabelle, Idris2, F*, Dafny, TLAPS — the HP triad is
   absent. A live CI run can compile and dispatch but the subprocess
   exits with "binary not found".

2. **No smoke fixture for the three named provers.** `tests/chapel_fixtures/`
   has `coq_trivial.v` and `lean_trivial.lean`; there is no equivalent
   `echo_trivial.tll`, `tropical_trivial.tll`, or `katagoria_trivial.k`.
   This PR adds the minimum three.

3. **No discoverability for "how do I add a new HP discipline."**
   Adding a discipline today means editing the 39-arm match in
   `hp_ecosystem.rs::upstream()`, the 41-arm match in
   `ProverFactory::create`, and matching arms in `is_hp_ecosystem()`
   and `default_executable()`. There is no documented onboarding flow.

## What this PR delivers

- This correction memo (`docs/handover/B7-AUDIT-CORRECTION.md`).
- Three smoke fixtures (`tests/fixtures/hp/`):
  - `echo_trivial.tll`         — discipline `echo`, single identity goal.
  - `tropical_trivial.tll`     — discipline `tropical`, resource-aware identity.
  - `katagoria_trivial.k`      — discipline `verify`, single isomorphism.
- A short onboarding doc (`docs/HP-BACKEND-ONBOARDING.md`) listing the
  ~4 files an author must touch to add a new HP discipline, with line
  references.

What it does **not** deliver:

- The upstream `typell` / `katagoria` / `tropical-type-check` binaries
  (those live in `developer-ecosystem/katagoria`,
  `verification-ecosystem/tropical-resource-typing`, and
  `verification-ecosystem/typell` and are owner-managed).
- A live CI run gate (that needs the binaries packaged first; see
  the L3 path checklist in the D18 PR).
- Per-discipline GNN training data extraction (TypeDiscipline Phase-2
  deferred — audit item F26).

## Cross-references

- `docs/handover/TODO.md` P4 — Wave-4 + HP ecosystem expansion (now
  partially superseded for the HP rows).
- `docs/PROVER_COUNT.md` Tier-8 — canonical 41-variant inventory.
- C12 PR (echidnabot manifest) — per-repo opt-in shape that consumers
  using these backends will adopt.
- D18 PR (L3 gate checklist) — packaging the upstream binaries is one
  of the L3 → L1 hand-off criteria.
