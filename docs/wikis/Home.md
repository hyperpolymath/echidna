<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# ECHIDNA Wiki

**ECHIDNA** — Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance — is a trust-hardened neurosymbolic theorem-proving platform with a large multi-backend prover surface, of which **12 core backends** are exposed by the default API. Counts differ depending on what is being counted; [`docs/PROVER_COUNT.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.adoc) is canonical and carries the commands that reproduce each figure.

**License**: MPL-2.0 for the code, the **machine-readable specification surface** (`.machine_readable/`, manifests, OCI image labels) and **`echidna-playground/`**; **documentation** under CC-BY-SA-4.0. MPL-2.0 is file-level copyleft: changes to ECHIDNA's own files stay open, while combining them with other code carries no obligation on the rest of that work. Re-ruled 2026-10-01 from the 2026-08 AGPL split. Full statement: [`NOTICE`](https://github.com/hyperpolymath/echidna/blob/main/NOTICE).

**Release history**: [`CHANGELOG.adoc`](https://github.com/hyperpolymath/echidna/blob/main/CHANGELOG.adoc); semver pin in [`Cargo.toml`](https://github.com/hyperpolymath/echidna/blob/main/Cargo.toml).

## Quick navigation

- [Getting Started](Getting-Started) — install, build, first proof
- [Architecture](Architecture) — components, trust pipeline, polyglot layout
- [Guides](Guides) — adding provers, API usage, ML training
- [FAQ](FAQ) — common questions
- [Troubleshooting](Troubleshooting) — build issues, prover failures

## Canonical in-repo documents

When the wiki and the repo disagree, **the repo wins**:

- [`README.adoc`](https://github.com/hyperpolymath/echidna/blob/main/README.adoc) — primary project README
- [`CLAUDE.md`](https://github.com/hyperpolymath/echidna/blob/main/CLAUDE.md) — codebase orientation
- [`docs/ARCHITECTURE.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.adoc) — current architecture
- [`docs/PROVER_COUNT.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.adoc) — tier table
- [`docs/ENV-VARS.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/ENV-VARS.adoc) — environment variables
- [`docs/ROADMAP.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.adoc) — stage map and sprint targets
- [`docs/handover/HANDOVER-INDEX.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/HANDOVER-INDEX.adoc) — handover/ navigation
- [`RSR_COMPLIANCE.adoc`](https://github.com/hyperpolymath/echidna/blob/main/RSR_COMPLIANCE.adoc) — RSR / CCCP compliance statement
- [`.machine_readable/descriptiles/STATE.a2ml`](https://github.com/hyperpolymath/echidna/blob/main/.machine_readable/descriptiles/STATE.a2ml) — machine-readable state

## Capability status (honest, 2026-10-05)

Each row says how far the capability actually goes. The words are used
strictly and none implies the next: **implemented** (code exists),
**wired** (reachable from the CLI/API), **tested** (exercised by an automated
test), **CI-gated** (a workflow runs it on every PR), **proved** (machine-checked
proof), **deployed** (running somewhere for users). Evidence: workflow runs on
`main` at `b761b3a` (paginated check-runs) plus the repository at the same
commit.

| Capability | Status | Not yet |
|---|---|---|
| Rust core, CLI, REPL (`echidna prove/verify/search/…`) | implemented, wired, tested (`cargo test`) | Rust CI was in `startup_failure` on `main` from 2026-07 to 2026-10; restored by the 2026-10-05 start-point PR |
| 12 core backends (`GET /api/provers`) | implemented, wired, live-tested (T1/T2 live-prover matrices green) | — |
| Wider backend surface (see [`docs/PROVER_COUNT.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.adoc)) | implemented | Tier-4 backends are mock-only; the HP-ecosystem type-checker backends call `typell --discipline` / `tropical-type-check`, which upstream does not provide, so they are **not wired** |
| Trust pipeline (integrity, certificates, axioms, confidence, mutation, Pareto, statistics) | implemented, wired into `dispatch.rs`, unit-tested | not proved |
| Idris2 ABI (`src/abi/`) | type-checked, CI-gated (`idris2-abi-ci.yml`) | — |
| Dogfood proof corpus (`proofs/{coq,lean,agda}`) | CI-gated (`dogfood-proofs-ci.yml`) | — |
| Agda meta-checker | implemented | its workflow was in `startup_failure` on `main` |
| Creusot trust kernel (`crates/echidna-core-creusot`) | annotations **stated**; stable-Rust test mirror runs in CI | **not proved**: no obligation has been discharged; the Creusot job is manual-only |
| Ada/SPARK kernel (`spark/`) | implemented; `spark-theatre-gate` green | proof status not re-verified in this pass |
| Chapel parallel search (`--features chapel`) | implemented, builds in CI | the "real Chapel library" job is allow-fail and red |
| Julia ML (tactic prediction, GNN) | logistic-regression predictor implemented | GNN training runs offline; not CI-tested |
| REST / gRPC / GraphQL servers | implemented; server boot gate green | — |
| UI | static shell (`just serve-ui`, Bun) | AffineScript-TEA compile pipeline not wired (`just build-ui` fails on purpose) |
| ID minting (`echidna::ids`) | UUIDv7 record ids: implemented, wired, tested. UUIDv8 content ids (SHA-256 over JCS): implemented, tested | content ids not yet used for goals/corpus/octads |
| `echidna prove --output json` (`echidna.prove.result/1`) | — | not implemented yet |
| Containers | built in CI | publication not verified |
| Forge mirrors | GitLab, Codeberg, SourceHut, Radicle succeed | Bitbucket, Disroot, Gitea mirror jobs fail |

## Core invariants

1. **ML suggests; provers verify.** Neural components rank, route, propose. Formal provers carry the trust.
2. **Trust is checked, not asserted.** Solver binaries are SHAKE3-512 / BLAKE3 integrity-checked; certificates (Alethe, DRAT/LRAT, TSTP) are independently reproduced where formats allow.

## Key concepts

- **12 core backends** exposed by default; the wider surface (external prover bindings plus TypeChecker disciplines routed via TypedWasm Sigma) is reachable through explicit `ProverKind` selection. Figures and their denominators: [`docs/PROVER_COUNT.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.adoc).
- **17 corpus adapters** — every major public proof corpus has a structural ingest path (see [`docs/CORPUS-ADAPTERS.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.adoc)).
- **4 arbitration mechanisms** — portfolio majority-vote, Bayesian posterior, Dempster-Shafer belief combination, Pareto multi-objective frontier.
- **6 cross-prover exchange formats** — OpenTheory, Dedukti, TPTP, SMT-LIB, SMTCoq, Lambdapi.
- **11-step trust pipeline** — integrity → portfolio → certificates → axioms → confidence → mutation → pareto → statistics → emission (see Architecture page).
- **Polyglot stack** — Rust core, Julia ML sidecar, Idris2/Agda formal proofs, Zig FFI, Chapel parallel, AffineScript UI with a static shell served by Bun (ReScript removed 2026-08; Deno retired 2026-09; the AffineScript-TEA compile pipeline is not wired yet — issues #117/#266).
- **Guix-only package management** — sealed-container escape hatch for the non-free tail. (The Nix fallback was deprecated in the 2026-05-18 estate ruling and fully removed estate-wide on 2026-06-01.)
- **Justfile, not Make. Podman, not Docker.**

## Recent major work

The 2026-06-01 **prover/corpus/vocab/synonyms/arbitration saturation campaign** added 13 corpus adapters, 3 new arbiters, 4 new exchange bridges, and a formal data-model spec. Entry points:

- [`docs/CORPUS-ADAPTERS.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.adoc) — 17-adapter index with per-adapter source URLs, hazard flags, and downstream wiring (`suggest` / `octad-emit` / GNN training).
- [`docs/architecture/VERISIM-ER-SCHEMA.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/architecture/VERISIM-ER-SCHEMA.adoc) — VeriSim ↔ ECHIDNA E-R schema (12 entities + 7 relationships, each with Rust struct + VeriSimDB table + Cap'n Proto schema + PK/FK).
- [`docs/decisions/2026-06-01-saturation-campaign.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/decisions/2026-06-01-saturation-campaign.adoc) — ADR documenting the ordered marginal-benefit hierarchy and the decision to execute levers (1)–(6) and defer (7) GNN-training.
- [`docs/handover/PROVER-CORPUS-SATURATION-LANE.adoc`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/PROVER-CORPUS-SATURATION-LANE.adoc) — saturation lane handover with sibling-branch collision avoidance.

The **dogfood proof corpus is now CI-gated**: every theorem under `proofs/{coq,lean,agda}` and the `src/idris` validator type-checks on each PR (`dogfood-proofs-ci.yml` + `idris2-abi-ci.yml`), each driven by a `just proofs-*` recipe — closing a gap where the corpus had no CI. Run it locally via `just proofs`; see [Getting Started](Getting-Started).
