<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: MPL-2.0 -->
# FAQ

## How many provers are supported?

**128 total** ProverKind variants: 89 external prover bindings plus 39 TypeChecker disciplines routed via TypedWasm Sigma.

Of these, **12 core** are exposed by the default REST API: Coq/Rocq, Lean 4, Agda, Isabelle/HOL, Idris 2, F\*, Z3, CVC5, Alt-Ergo, Dafny, Vampire, E Prover. The remaining 116 are reachable via explicit `ProverKind` selection in CLI / REPL / GraphQL.

The full tier table lives in [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md).

## Are proofs sandboxed?

Yes. Each prover runs in Podman or bubblewrap with no host filesystem or network access. Resource limits (CPU, memory, wall time) are enforced per `DispatchConfig`. See [`src/rust/executor/`](https://github.com/hyperpolymath/echidna/tree/main/src/rust/executor).

## How is trust scored?

Five-tier Bayesian confidence model (`src/rust/verification/confidence.rs`). Proofs verified by multiple independent provers receive higher trust. Cross-prover certificate verification (Alethe / DRAT-LRAT / TSTP, replayed independently) elevates trust further. Solver binaries are SHAKE3-512 + BLAKE3 integrity-checked against `config/solver-manifest.toml` before invocation.

## Can I add my own prover?

Yes. Implement the `ProverBackend` trait in `src/rust/provers/your_prover.rs`, add a variant to `ProverKind`, register in `ProverFactory`, and add fixtures under `tests/`. See [Guides](Guides) for the step-by-step.

## What's the ML layer?

Julia sidecar (port 8090). A GNN ranks premises; a logistic regression head suggests tactics. Both can be retrained from accumulated proof outcomes stored in VeriSimDB. The architecture is "ML suggests; provers verify" — a wrong suggestion costs a CPU cycle, not soundness.

See [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md) for the data flow.

## Is the wiki authoritative?

No. **The repo wins** when the wiki and the in-repo docs disagree. The wiki is a navigation aid pointing at the canonical sources. Pages here are refreshed periodically but lag the repo.

Canonical sources of truth:
- [`CLAUDE.md`](https://github.com/hyperpolymath/echidna/blob/main/CLAUDE.md) for codebase orientation
- [`.machine_readable/6a2/STATE.a2ml`](https://github.com/hyperpolymath/echidna/blob/main/.machine_readable/6a2/STATE.a2ml) for current state
- [`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) for direction

## Why MPL-2.0 and not MIT or AGPL?

Practical balance: weak copyleft at the file level (modifications to MPL'd files must be open) without copyleft-by-linking (so downstream commercial use is straightforward). The project migrated from a dual MIT/Palimpsest-0.6 licence in 2026; `NOTICE` and `LICENSE` reflect the current state.

## How do I report a security issue?

See [`SECURITY.md`](https://github.com/hyperpolymath/echidna/blob/main/SECURITY.md) and [`.well-known/security.txt`](https://github.com/hyperpolymath/echidna/blob/main/.well-known/security.txt). Do not disclose publicly until addressed.

## Which corpus formats does echidna ingest?

**17 adapters as of the 2026-06-01 saturation campaign** (`src/rust/corpus/<name>.rs`):

agda, coq, lean, idris2, isabelle, metamath, mizar, hol_light, hol4, dafny, why3, fstar, acl2_books, tptp, smtlib, proofnet, minif2f.

The first four shipped pre-2026-04; the other 13 landed in the saturation campaign. Each adapter is `pub fn ingest(root: &Path) -> Result<Corpus>` and surfaces hazard flags (`postulate`, `believe_me`, `sorry`, `cheat`, `Admitted`, …) via `AxiomUsage`.

Full table with file extensions, upstream source URLs, and hazard flags: [`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md).

## What's the difference between the four arbitration mechanisms?

| Arbiter | Module | Output | Strength |
|---|---|---|---|
| **Portfolio** | `src/rust/verification/portfolio.rs` | Categorical agreement summary | Simple majority across N solvers; no calibration needed. |
| **Bayesian** | `src/rust/verification/bayesian_arbiter.rs` | `PosteriorVerdict` (probabilities + Shannon entropy) | Calibrated per-prover precision/FPR; uses log-odds accumulation. |
| **Dempster-Shafer** | `src/rust/verification/dempster_shafer.rs` | `BeliefPlausibility` over `VerdictSet`, or `ArbiterError::HighConflict(k)` | Models ignorance explicitly; refuses to commit when conflict is too high. |
| **Pareto** | `src/rust/verification/pareto_arbiter.rs` | `ParetoDecision` over multi-axis outcomes | Multi-objective (time, memory, certificate-size, trust-tier) — returns non-dominated set, not a single verdict. |

[Guides](Guides) has a "Picking an arbitration mechanism" walkthrough with motivating examples.

## Are MSC2020 / WordNet / ConceptNet required to run echidna?

**No.** They are offline-resilient enhancements to the synonym layer. `load_cross_prover_dicts` (`src/rust/suggest/synonyms.rs`) silently returns empty `SynonymTable`s if the underscore-prefix TOMLs (`_msc2020.toml`, `_wordnet_math.toml`, `_conceptnet_seed.toml`) are missing from `data/synonyms/`. Per-prover synonym lookup still works; cross-prover `by_semantic_class` queries just return fewer hits.

## Can I use TPTP problems with echidna?

**Yes.** TPTP is supported on two surfaces:

- **Corpus ingest** — [`src/rust/corpus/tptp.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/tptp.rs) walks a directory of `*.p` / `*.tptp` files and indexes annotated formulas (`fof`, `cnf` fully supported; `tff` / `thf` recognised but not translated).
- **Exchange** — [`src/rust/exchange/tptp.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/tptp.rs) parses, emits, and best-effort-translates between TPTP and SMT-LIB v2 for cross-prover interop. Vampire, E, SPASS, Princess, iProver, Twee all consume TPTP natively.

## What's the difference between SMTCoq bridge being a stub and a full bridge?

The [`src/rust/exchange/smtcoq.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/smtcoq.rs) module is a **stub bridge** — its module docs say so explicitly. It supplies enough Alethe / LFSC / DRAT parser surface to drive downstream consumers and emits an *honest skeleton* with `(* TODO: SMTCoq integration not yet wired *)` markers, but does **not** invoke the actual SMTCoq Coq plugin to replay the proof in the Coq kernel.

A full bridge would require the upstream SMTCoq binary on `PATH` and would replay Z3 / veriT / CVC4 unsat proofs against Coq for kernel-level re-checking. That's gated on the upstream SMTCoq plugin and is out of scope for the current module. Downstream callers can detect the stub status by grepping the emitted skeleton for the TODO markers before trusting the output.

## Where's the formal data model / schema?

Two complementary surfaces:

- [`docs/architecture/VERISIM-ER-SCHEMA.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/architecture/VERISIM-ER-SCHEMA.md) — the formal entity-relationship schema for the VeriSim shared-state model (entities, relations, cardinalities, invariants).
- [`crates/echidna-wire/schemas/verisim_er.capnp`](https://github.com/hyperpolymath/echidna/blob/main/crates/echidna-wire/schemas/verisim_er.capnp) — the Cap'n Proto wire schema that implements it.

The 8-modality octad emission layer (`src/rust/corpus/octad.rs`) is the load-bearing producer; any corpus from any adapter can emit octads conforming to this schema.
