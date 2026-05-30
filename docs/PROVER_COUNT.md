<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Canonical Prover Count and Tier Table

**Status**: canonical. Cite this file when documenting backend coverage in any
other doc. Other surfaces that quoted historical counts (12, 30, 48, 105) are
being updated to point here. Last revised: 2026-05-30.

## TL;DR

| Question | Answer |
|---|---|
| Total `ProverKind` variants in `src/rust/provers/mod.rs` | **128** |
| External prover bindings (separate binary or library) | 89 |
| `TypeChecker` disciplines routed via TypedWasm Sigma | 39 |
| Exposed by default REST API (`Tier 1` / core) | **12** |
| With real `suggest_tactics` (not stub) | **91 of 91** |
| Routing tactic suggestions through `gnn_augment_tactics` | **all backends with `suggest_tactics`** (S5 pilot 5 + Tier-1 extension 5 + Tier-1 finisher 2 + Tier-2 sweep 33 + Tier-3/niche sweep 53 — full coverage as of 2026-05-30; gracefully no-ops when `gnn_api_url` is None or `neural_enabled` is false) |
| With native search command | 16 of 91 (72 return `Ok(vec![])` — cross-prover search via `VeriSimAdvisor` covers them) |
| Trust pipeline integrity-hashed | All Tier 1; Tier 2 incrementally |

## Tier table

Tiers correspond to CI coverage cadence and default-API visibility.

| Tier | Cadence | Members | Notes |
|---|---|---|---|
| **1 — core** | Every PR | Coq/Rocq, Lean 4, Agda, Isabelle/HOL, Idris 2, F*, Z3, CVC5, Alt-Ergo, Dafny, Vampire, E Prover | Exposed by default REST `/api/verify`. Required to pass for green CI. |
| **2 — extended** | Every PR (allow-fail) | HOL Light, Metamath, Mizar, HOL4, PVS, ACL2, TLAPS, Twelf, Nuprl, Minlog, Imandra, SPASS, Princess, IProver, Twee, MetiTarski, CSI, AProVE, Leo3, Satallax, Lash, AgsyHOL, GLPK, SCIP, MiniZinc, Chuffed, OR-Tools, Dreal, CBMC, KeY, KeYmaera X, EasyCrypt, Abella, Athena, Cameleer, Why3 | Direct invocation via `ProverKind`. CI runs but doesn't block. |
| **3 — niche** | Nightly | Arend, Cedille, Lego, Aprové, Boogie, CVC4, Petri-net checkers, modal-logic provers, real-algebraic provers | Specialised use. |
| **4 — placeholder** | Smoke only | 19 backends present as `ProverKind` variants but with mock-only invocation. | Promote when upstream maintainer ships a Containerfile. See [`handover/TODO.md`](handover/TODO.md) P4. |
| **5 — Wave-3 secured** | Every PR | Tamarin, ProVerif, Metamath (rust-native), Twelf, OR-Tools | All ✅ real, runtime-smoke verified, Containerfile.wave3 |
| **6 — pure-Rust** | Every PR | Metamath (own crate) | No external binary; in-process. |
| **7 — Wave-2 modal/real-algebraic** | Every PR | Modal, real-algebraic provers (Phase 3 implementations) | See [`handover/PHASE-3-PROMPT.md`](handover/PHASE-3-PROMPT.md) |
| **8 — HP type-checker ecosystem** | Nightly | 13 corpus-only provers (Ephapax / Wokelang / AffineScript backends) | Adapters pending; tracked in handover/TODO P4 |
| **9 — TypeChecker disciplines** | Every PR | 39 disciplines (Hindley-Milner, System F, Rank-N, ATS-style affine, …) | Routed via `crates/typed_wasm` Sigma parameters; do not require external binary. |
| **10 — Coq-Jr ecosystem (playground)** | Sub-project CI | `echidna-playground/` backends | Separate sub-project; tracked there. |

## Why so many counts in the wild?

History of the count drift:

- v1.0 (Dec 2025): **12** real backends. Released as the MVP scope.
- v1.2 (Jan 2026): **30** declared, 12 fully tested.
- v1.3 (Feb 2026): **48** declared, ~32 with real `suggest_tactics`.
- v2.0 (Apr 2026): **74** after Wave-1 + Wave-2 absorption.
- v2.1 (May 2026): **105** after Wave-3 (Tamarin, ProVerif, Twelf, OR-Tools).
- v2.2 (May 2026): **128** after 39 TypeChecker disciplines were Sigma-routed
  through TypedWasm (commit `c4bc272` and follow-on).
- v2.3 (May 2026): same **128** declared, but `gnn_augment_tactics` now wraps
  every backend with `suggest_tactics` (S5 pilot c8a4f25 + #135 Tier-1 extension
  + #136 Tier-1 finisher + Tier-2 sweep + Tier-3/niche sweep). Wiring is a
  no-op when the Julia `/gnn/rank` service is unreachable; once trained
  weights land (`models/neural/`), every backend automatically returns
  model-derived premise-apply tactics at the top of its `suggest_tactics`
  list.

Documents in this repo predating each milestone often quote the count current
to their authoring date. When in doubt, **trust this file** and
`.machine_readable/6a2/STATE.a2ml`.

## Verifying locally

```bash
# Total variant count
rg -c "^\s*[A-Z][a-zA-Z0-9_]+," src/rust/provers/mod.rs | head -1

# Tier 1 core list
rg "fn all_core" -A 30 src/rust/provers/mod.rs

# Per-tier breakdown
just provers              # if implemented
echo "or read"
cat .machine_readable/provers.a2ml
```

## When to cite this file

Cite `docs/PROVER_COUNT.md` (not a number) in:
- README.adoc tagline
- CLAUDE.md project overview
- Any new design doc
- PR descriptions referring to "all backends"
- Issue templates

If a count changes (new wave absorbed, backend retired), update this file
in the same PR. The single source of truth for the count is `ProverKind::all()`
in `src/rust/provers/mod.rs`; this doc is the human-readable mirror.
