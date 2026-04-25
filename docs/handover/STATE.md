# Echidna Production-Wiring — State of Things

**Where we are now, in relation to the forward vision.** Complements
`ECHIDNA-TODO.md` (actionable backlog) and the full continuation
prompts at `verification-ecosystem/echidna/docs/handover/`.

Last updated: 2026-04-26.

---

## Vision (one paragraph)

Take Echidna from "48 / 105 backends trait-wired with mock-only CI" to
"production-level live subprocess CI across ~38 backends, Cap'n Proto
IPC end-to-end, Chapel as first-class parallel execution layer." Three
phases, deliberately sequenced **L3 → L1 → L2**: live-prover CI first
because it surfaces real bugs mocks hide, Cap'n Proto next so Chapel
can consume its schemas, Chapel last because its sub-waves are the
largest piece. Guix is the authoritative package manager throughout
with Nix as fallback. GitHub is the single source of truth; no other
forges pushed directly.

## Decisions locked

| # | Decision | Rationale |
|---|----------|-----------|
| D1 | **Serialization = Cap'n Proto** | Chosen over Bebop3 for dependability + maturity (Cloudflare Workers use at scale), zero-copy reads, strong schema-evolution. Tradeoff: heavier codegen; shim Julia/Chapel via C-ABI (fits existing Idris2-ABI + Zig-FFI). |
| D2 | **Chapel = first-class, maximal** | 420-LoC POC promoted to `src/chapel/` across 7 sub-waves — portfolio dispatch, speculative tactic search, corpus-parallel ops, mutation-testing parallelism, multi-locale distributed, numeric hot paths. |
| D3 | **Guix primary, Nix fallback** | Per project CLAUDE.md. `guix.scm` / `manifests/live-provers.scm` authoritative; `flake.nix` mirrors. |
| D4 | **Execution order = L3 → L1 → L2** | Live-prover CI first: highest-leverage gap, surfaces real bugs mocks hide. Cap'n Proto next, since Chapel consumes those schemas. |
| D5 | **Live-prover CI cadence tiered** | T1 every PR, T2 nightly, T3 weekly, T4 quarterly allow-fail. |
| D6 | **No JSON emit on hot path** | Per `feedback_no_json_emit_a2ml`. Cap'n Proto replaces HTTP-JSON Rust↔Julia. Tool config stays Nickel/A2ML. |

## Current state per phase

### L3 — Live-Prover CI — PARTIALLY SHIPPED

Four waves. First two done, third and fourth scaffolded only.

| Wave | Scope | Status | Commits |
|------|-------|--------|---------|
| Wave-1 | Tier-1 apt-installable (9 backends) every PR: Z3, CVC5, Vampire, EProver, SPASS, Alt-Ergo, GLPK, MiniZinc, Chuffed | **DONE** 2026-04-19 | `b022bf4` |
| Wave-2 | Tier-2 build-from-source (10 backends) nightly: coq/agda/why3 (apt), idris2 (source bootstrap), lean4 (elan), isabelle (Isabelle2024 tarball), dafny (dotnet tool), fstar (release tarball), tlaps (installer). hol-light deferred to Wave-3. | **DONE 2026-04-19** locally; CI-unverified | `9a4aeeb`, `6717b12` |
| Wave-3 | Tier-3 weekly, 9 backends (Tamarin, ProVerif, Imandra, SCIP, OR-Tools, HOL4, ACL2, Twelf, Metamath). Needs per-backend Containerfiles (Podman). | **SCAFFOLD ONLY** — handover hints in STATE.a2ml | — |
| Wave-4 | Tier-4 quarterly, 19 backends. Retained as mock-only unless a maintainer volunteers. | **SCAFFOLD ONLY** | — |

Local verification of Wave-1 + Wave-2: **18/18 live tests pass** (13 real versions returned, 5 auto-skipped for missing binaries: GLPK/SPASS/MiniZinc/TLAPS/Chuffed).

**Dafny flagged as shallow** (165 LoC subprocess wrapper). Live version-check passes but the wiring is stub-ish — needs L3-phase deepening before mocks retire.

### L1 — Cap'n Proto Protocol Swap — NOT STARTED

Blockers: L3 Tier-1 green on main for ≥ 7 days. Current IPC:
- **Rust ↔ Julia**: HTTP + JSON (`src/rust/gnn/client.rs:1-195` → `src/julia/api_server.jl:8090`) — violates `no_json_emit`.
- **Rust ↔ Chapel**: Stub (Zig bridge self-links but not in dispatch path).
- **Rust ↔ gRPC**: schema-only; `dispatch.rs` uses in-process traits.

### L2 — Chapel Maximum Integration — PARTIALLY PREPARED

- 420-LoC POC at `chapel_poc/parallel_proof_search.chpl` + Chapel `export` functions at `chapel_poc/chapel_ffi_exports.chpl`.
- Zig FFI bridge at `src/zig_ffi/chapel_bridge.zig` — **now self-links** against bundled stubs (commit `53ab9b8`, 2026-04-19). `cargo build --features chapel` works standalone; 6/6 `proof_search` tests pass.
- Nothing in dispatch path yet. No `src/chapel/` directory. All 7 sub-waves pending.

## Wiring depth snapshot (from 2026-04-19 audit)

- **Deep** (persistent process + structured protocol parsing): Z3, CVC5, Coq (SerAPI), Lean 4, Idris2.
- **Medium** (subprocess + output parse, no streaming): Agda, Vampire.
- **Stub-ish / thin**: Dafny (165 LoC) — flagged for hardening during L3.

Also corrected 2026-04-19 (were mis-listed as "planned"):
- **Tamarin** — fully wired (`provers/tamarin.rs`, 592 LoC, registered in `ProverFactory`, 4 unit tests).
- **ProVerif** — fully wired (`provers/proverif.rs`, 799 LoC, registered).
- **No TODO/FIXME in `src/rust/`** — 0 matches; standing property.

## Corpus

66,674 proofs across 16 prover systems (`COMPLETE_CORPUS_SUMMARY.md`). 179,933 tactics, 10,599 unique tactic signatures, 300 indexed premises. Untouched this session.

## CI today

- `.github/workflows/rust-ci.yml` — mock-only tests on every PR. Baseline smoke.
- `.github/workflows/chapel-ci.yml` — compiles Chapel POC and the Zig FFI bridge. **Does not feed into dispatch** and **does not link real Chapel**; tests run against bundled stubs only.
- `.github/workflows/live-provers.yml` — tiered workflow (T1 PR, T2 nightly, T3 weekly, T4 quarterly). T1 + T2 matrices filled with real provisioning; T3 + T4 placeholder jobs.
- `.github/workflows/agda-meta-checker.yml` — formally-verified trust-pipeline properties.

## Architectural invariants (from 0-AI-MANIFEST.a2ml + CLAUDE.md)

- **Idris2 ABI** for formal proofs; zero `believe_me`.
- **Zig FFI** for C-ABI bridges to polyglot consumers.
- **Justfile** primary build system; not Make.
- **Containerfile** + Podman; not Dockerfile / Docker.
- **State files in `.machine_readable/6a2/` only**; never root.
- **All interfaces under `src/interfaces/`**; never extract to separate repos.
- **When adding provers: update all 3 layers** (Rust backend, Julia ML, Chapel).
- **Original name: "Cognitive Hybrid"** not "Computational Heuristic".
- **PMPL-1.0-or-later** throughout.
- **No Python** — Julia for ML, Rust for systems, ReScript for apps.

## Tech stack

- **Primary**: Rust (48 / 105 prover backends, trust pipeline, CLI, REPL, API servers).
- **Secondary**: Julia (ML inference, port 8090), ReScript + Deno (UI, 33 files, zero TypeScript).
- **Optional**: Chapel (parallel proof dispatch).
- **ABI**: Idris2 (7+ modules, zero `believe_me`).
- **FFI**: Zig (4 shared libraries).
- **Interfaces**: GraphQL (8081), gRPC (50051), REST (8000). All three interface crates build clean as of 2026-04-26.
- **Build**: Justfile primary, Cargo workspace.
- **Container**: Podman + Containerfile.

## 11-step trust pipeline (v1.5+)

1. Solver binary integrity (SHAKE3-512 + BLAKE3).
2. SMT portfolio solving / cross-checking.
3. Proof certificate checking (Alethe, DRAT/LRAT, TSTP).
4. Axiom usage tracking (4 danger levels).
5. Solver sandboxing (Podman, bubblewrap).
6. 5-level trust hierarchy for confidence scoring.
7. Mutation testing for specifications.
8. Prover dispatch pipeline.
9. Cross-prover proof exchange (OpenTheory, Dedukti).
10. Pareto frontier (multi-objective proof search).
11. Bayesian timeout estimation.

## v2.x roadmap (from CLAUDE.md)

- **v2.1 (landed)**: GNN proof graph construction (7 node kinds, 8 edge kinds); 32-dim local term embeddings + GNN inference client; GNN-guided proof search (hybrid GNN + symbolic scoring); Julia `/gnn/rank` endpoint with cosine fallback; Idris2 formal proofs (7 GNN properties, 0 `believe_me`); 28 new tests.
- **v2.2**: Train GNN/Transformer on larger corpus (Flux.jl); Chapel → Rust C FFI bridge **(the Zig layer is done; dispatch-path integration is the L2 work above)**; Tamarin/ProVerif bridge **(already landed — stale in the roadmap)**.

## Handover artefacts (in-repo, canonical)

| File | Role |
|------|------|
| `verification-ecosystem/echidna/docs/handover/PRODUCTION-WIRING-PLAN.md` | Master plan |
| `verification-ecosystem/echidna/docs/handover/L1-CAPNPROTO-PROMPT.md` | L1 Cap'n Proto continuation prompt |
| `verification-ecosystem/echidna/docs/handover/L2-CHAPEL-PROMPT.md` | L2 Chapel continuation prompt |
| `verification-ecosystem/echidna/docs/handover/L3-LIVE-PROVER-CI-PROMPT.md` | L3 live-prover continuation prompt (marked Wave-2 DONE, pointing to Wave-3) |
| `verification-ecosystem/echidna/.machine_readable/6a2/STATE.a2ml` | Session ledger incl. `[l3-status-after-wave-2]` + `[wave-3-handover-hints]` |
| `verification-ecosystem/echidna/docs/handover/README.md` | Index + drift-handling policy |

## Session log highlights (2026-04-26)

- **echidna-graphql build fixed** (`5aec9d5`) — ProverKind enum expanded from 30 → 113 variants (exhaustive, no catch-all) across schema.rs + resolvers.rs + ffi_wrapper.rs; FfiProverBackend trait wired (config/set_config/search_theorems); FFI pointer casts corrected. `cargo build -p echidna-graphql` now clean.
- **FFI boundary audit** (`b4d682b`) — `audits/audit-ffi-boundary.md` (4-section per-module safety review) + `audits/assail-classifications.a2ml` (7 classifications suppressing legitimate UnsafeCode at all three interface ffi_wrapper.rs files + core ffi/ + proof_search.rs). panic-attack findings drop from active to classified.
- **bounded_read_config helper** — `src/rust/integrity/io.rs` ships sync 1 MiB-capped read helper; `solver_integrity.rs` migrated. Remaining UnboundedAllocation finding resolved.
- **F5 deferred** — `boj-server` `echidna-llm-mcp` cartridge real invocation is the one remaining open item. BoJ currently operates in skeleton mode for this cartridge; echidna REST layer is fully wired to its boundary.

## Session log highlights (2026-04-19)

- **Chapel FFI self-link fix** (`53ab9b8`) — `-Dstubs=true` default in `src/zig_ffi/build.zig`; `-fno-sanitize=undefined` flag; `use anyhow::Context;` in `proof_search.rs`. `cargo build --features chapel` now links standalone.
- **Stale-gap corrections** — Tamarin + ProVerif marked fully wired; zero TODO/FIXME standing property; Chapel FFI "not yet wired" was actually a link-time gap, fixed.
- **L3 Wave-2 installers** — idris2 source bootstrap against Chez Scheme; isabelle Isabelle2024 tarball; dafny `dotnet tool install`; fstar release tarball (binary `fstar.exe` even on Linux); tlaps self-extracting installer (`tlapm`). hol-light deferred to Wave-3.
- **Tests extended** — `live_fstar_version` + `live_tlaps_version` added; `kind_label` gained FStar / TLAPS; `ProverConfig` literal gained missing `library_paths` field (pre-existing compile error fixed).
- **Docs + `.gitignore`** — `QUICKSTART-DEV.adoc` chapel-feature build instructions; `chapel_poc/README.md` "Add FFI bindings to call from Rust" marked DONE; `.gitignore` adds `models/e*/`, `/models_e*/`, `src/zig_ffi/zig-out/`, `.zig-cache/`.
- **Mirrored** — all 4 Desktop handover docs now in-repo at `docs/handover/` (commit `b6d437c`).
