<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Canonical Prover Count and Tier Table

**Status**: canonical. Cite this file when documenting backend coverage in any
other doc. Every number below was re-measured against the tree — see
[Verifying locally](#verifying-locally) for the exact commands, which are the
definition of each figure rather than a description of it.

> **Read this first — the counts differ because they count different things.**
> There is no single "number of provers". The two figures most often confused:
> **141** is the number of `ProverKind` *enum variants*; **105** is the number
> of *backend implementation files* in `src/rust/provers/`. Both are correct.
> A surface quoting one of them as "the" count without saying which is drift —
> that is why historical counts (12, 30, 48, 74, 105, 128) are scattered across
> older documents. Prefer citing this file to quoting any number.

## TL;DR

| Question | Answer | Command |
|---|---|---|
| Total `ProverKind` variants in `src/rust/provers/mod.rs` | **141** | `V` below |
| Backend implementation files in `src/rust/provers/` | **105** | `F` below |
| Implementations providing `suggest_tactics` | **102** | `S` below |
| Exposed by default REST API (`Tier 1` / core) | **12** (`GET /api/provers`) | `C` below |
| Variants carrying a type-checker / discipline role | **46** | `D` below |
| Routing tactic suggestions through `gnn_augment_tactics` | **all backends with `suggest_tactics`** — gracefully no-ops when `gnn_api_url` is None or `neural_enabled` is false | — |
| Trust pipeline integrity-hashed | All Tier 1; Tier 2 incrementally | — |

## Tier table

Tiers correspond to CI coverage cadence and default-API visibility.

> **Membership counts in this table are not machine-checked.** Tier 1 mirrors
> `ProverKind::all_core()` and is verified by command `C`. Tier 9 is verified by
> command `D`. The remaining per-tier figures (Tier 4's placeholder count,
> Tier 8's corpus-only count) are hand-maintained and have not been
> re-measured — treat them as indicative. Making tier membership derivable
> from the code (an attribute on each variant) is tracked as documentation
> debt in [`docs/DEBT.md`](DEBT.md).

| Tier | Cadence | Members | Notes |
|---|---|---|---|
| **1 — core** | Every PR | Agda, Coq, Lean 4, Isabelle/HOL, Z3, CVC5, Metamath, HOL Light, Mizar, PVS, ACL2, HOL4 | Returned by `ProverKind::all_core()`; exposed by default at `GET /api/provers`; required to pass for green CI. Install hints in [`SUPPORTED_PROVERS.md`](SUPPORTED_PROVERS.md). |
| **2 — extended** | Every PR (allow-fail) | Idris 2, Lean 3, Vampire, E Prover, SPASS, Alt-Ergo, F*, Dafny, Why3, TLAPS, Twelf, Nuprl, Minlog, Imandra, Princess, IProver, Twee, MetiTarski, CSI, AProVE, Leo-III, Satallax, Lash, AgsyHOL, GLPK, SCIP, MiniZinc, Chuffed, OR-Tools, Dreal, CBMC, KeY, KeYmaera X, EasyCrypt, Abella, Athena, Cameleer | Direct invocation via `ProverKind` (covered by `ProverKind::all()` beyond `all_core()`). CI runs but doesn't block. List is illustrative; the live set is whatever `ProverKind::all()` returns. |
| **3 — niche** | Nightly | Arend, Cedille, Lego, Aprové, Boogie, CVC4, Petri-net checkers, modal-logic provers, real-algebraic provers | Specialised use. |
| **4 — placeholder** | Smoke only | 19 backends present as `ProverKind` variants but with mock-only invocation. | Promote when upstream maintainer ships a Containerfile. See [`handover/TODO.md`](handover/TODO.md) P4. |
| **5 — Wave-3 secured** | Every PR | Tamarin, ProVerif, Metamath (rust-native), Twelf, OR-Tools | All ✅ real, runtime-smoke verified, Containerfile.wave3 |
| **6 — pure-Rust** | Every PR | Metamath (own crate) | No external binary; in-process. |
| **7 — Wave-2 modal/real-algebraic** | Every PR | Modal, real-algebraic provers (Phase 3 implementations) | See [`handover/PHASE-3-PROMPT.md`](handover/PHASE-3-PROMPT.md) |
| **8 — HP type-checker ecosystem** | Nightly | 13 corpus-only provers (Ephapax / Wokelang / AffineScript backends) | Adapters pending; tracked in handover/TODO P4 |
| **9 — TypeChecker disciplines** | Every PR | 46 variants carry a type-checker / discipline role (Hindley-Milner, System F, Rank-N, ATS-style affine, …) — command `D` | Routed via `crates/typed_wasm` Sigma parameters; do not require an external binary. |
| **10 — Coq-Jr ecosystem (playground)** | Sub-project CI | `echidna-playground/` backends | Separate sub-project; tracked there. |

## Why so many counts in the wild?

Two independent causes, and they need different remedies.

**Cause 1 — genuine growth over time.** Each milestone's documents quote the
count current to their authoring date:

| Release | Declared | What changed |
|---|---|---|
| v1.0 (Dec 2025) | 12 | MVP scope: 12 real backends |
| v1.2 (Jan 2026) | 30 | 12 fully tested |
| v1.3 (Feb 2026) | **48** | ~32 with real `suggest_tactics` |
| v2.0 (Apr 2026) | 74 | Wave-1 + Wave-2 absorption |
| v2.1 (May 2026) | **105** | Wave-3 (Tamarin, ProVerif, Twelf, OR-Tools) |
| v2.2 (May 2026) | **128** | TypeChecker disciplines Sigma-routed through TypedWasm |
| current `main` | **141** | measured, this file |

Historical snapshots under `docs/releases/`, `docs/handover/` and
`docs/decisions/` are *deliberately* left at their authoring-time numbers —
they are records, not claims about today.

**Cause 2 — counting different things and calling both "provers".** This is
the harmful one, because both numbers are defensible in isolation. 141 counts
enum variants; 105 counts implementation files; 102 counts implementations
exposing `suggest_tactics`; 12 counts the default-exposed core. A document that
says "N prover backends" without naming the denominator will be read as a claim
about all four.

**Remedy:** cite this file rather than a number. The `R5a` canonical-reference
CI rule (`.github/canonical-references/prover-counts.yml`, enforced by the
`Canonical-reference drift (R5 generic)` step in the shared
`governance-reusable.yml`) fails the build when a bare count appears in a
load-bearing top-level document. Note its scope is the top-level document set
listed in that file — `docs/`, `.machine_readable/` and `crates/*/README.md`
are **not** covered, which is where the surviving drift accumulated.

## Verifying locally

Each command is the definition of its figure. Run from the repository root.

```bash
# V — total ProverKind variants (141)
awk '/pub enum ProverKind/{f=1;next} f&&/^\}/{exit} f' src/rust/provers/mod.rs \
  | grep -cE '^\s*[A-Z][A-Za-z0-9_]*\s*,'

# F — backend implementation files (105)
ls src/rust/provers/*.rs | grep -cv 'mod\.rs$'

# S — implementations providing suggest_tactics (102)
git grep -l 'fn suggest_tactics' -- 'src/rust/provers/*.rs' | wc -l

# C — Tier-1 core, exposed by default at GET /api/provers (12)
awk '/fn all_core/{f=1} f&&/\]/{print;exit} f' src/rust/provers/mod.rs \
  | grep -oE 'ProverKind::[A-Za-z0-9_]+' | wc -l

# D — variants carrying a type-checker / discipline role (46)
awk '/pub enum ProverKind/{f=1;next} f&&/^\}/{exit} f' src/rust/provers/mod.rs \
  | grep -icE 'typecheck|discipline'
```

`ProverKind::all()` in `src/rust/provers/mod.rs` is the machine source of
truth; this document is its human-readable mirror. If a count changes, update
this file **and** `.machine_readable/provers.a2ml` in the same PR.

## When to cite this file

Cite `docs/PROVER_COUNT.md` (not a number) in:
- the `README.md` tagline and the repository description
- `CLAUDE.md` project overview
- any new design doc
- PR descriptions referring to "all backends"
- issue templates

When a number genuinely must appear (a release note, a benchmark table), name
the denominator: "141 `ProverKind` variants", not "141 provers".

If a count changes (new wave absorbed, backend retired), update this file
in the same PR. The single source of truth for the count is `ProverKind::all()`
in `src/rust/provers/mod.rs`; this doc is the human-readable mirror.
