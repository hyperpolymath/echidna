# ECHIDNA — Production Wiring Master Plan

**Status**: Active — kickoff session 2026-04-19
**Scope**: Take Echidna from "48 backends trait-wired with mock-only CI" to "production-level live
subprocess CI across ~38/48 backends, Cap'n Proto IPC, Chapel as first-class execution layer"
**Repo**: `/var/mnt/eclipse/repos/verification-ecosystem/echidna/`
**Owner**: Jonathan D.A. Jewell
**Coordinator**: Claude (Opus 4.7, 1M ctx)

---

## Decisions Locked

| # | Decision | Rationale |
|---|---|---|
| D1 | **Serialization = Cap'n Proto** | Chosen over Bebop3 for dependability+maturity (Cloudflare Workers use at scale), zero-copy reads, strongest schema-evolution story. Tradeoff: heavier codegen. Shim Julia/Chapel via C-ABI (fits existing Idris2-ABI + Zig-FFI policy). |
| D2 | **Chapel = first-class, maximal** | Existing POC (`chapel_poc/parallel_proof_search.chpl`, 420 LoC) promoted to `src/chapel/`. Expand into portfolio dispatch, speculative tactic search, corpus-parallel ops, mutation-testing parallelism, multi-locale distributed, numeric hot paths. |
| D3 | **Guix primary, Nix fallback** | Per project `CLAUDE.md` package-management policy. `guix.scm` / `manifests/live-provers.scm` authoritative; `flake.nix` mirrors. |
| D4 | **Execution order = L3 → L1 → L2** | Live-prover CI first: highest-leverage gap, surfaces real bugs mocks hide, no protocol break. Cap'n Proto next, since Chapel wiring (L2) will consume those schemas. |
| D5 | **Live-prover CI cadence = tiered** | Tier-1 every PR, Tier-2 nightly, Tier-3 weekly, Tier-4 "best-effort / allow-fail" quarterly. |
| D6 | **No JSON emit** | Per memory rule `feedback_no_json_emit_a2ml`. Cap'n Proto replaces the current HTTP-JSON Rust↔Julia channel. Tool config stays Nickel/A2ML. |

---

## The Three Phases

### L3 — Live-Prover CI (Guix-first) — **~3 weeks**

**Goal**: every provisionable backend exercised against a canonical micro-goal on a predictable cadence.

**Artefacts**:
- `manifests/live-provers.scm` — Guix manifest listing all provisionable prover binaries
- `flake.nix` — Nix fallback, mirror of Guix set
- `.github/workflows/live-provers.yml` — tiered CI workflow (PR/nightly/weekly/quarterly)
- `tests/live_prover_suite.rs` — Rust test harness with canonical goals per backend
- `tests/live_goals/` — micro-goal fixtures (one per backend, per category)

**Tier assignment** (per `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/rust/provers/` audit):

| Tier | Cadence | Backends |
|---|---|---|
| **T1 — apt/trivial** | Every PR | Z3, CVC5, Alt-Ergo, Vampire, E Prover, SPASS, GLPK, MiniZinc, Chuffed |
| **T2 — build-from-source** | Nightly | Coq/Rocq, Lean 4, Agda, Idris2, F*, Isabelle/HOL, Why3, Dafny, HOL Light, TLAPS |
| **T3 — container / special** | Weekly | Tamarin, ProVerif, Imandra, SCIP, OR-Tools, HOL4, ACL2, Twelf, Metamath |
| **T4 — niche / best-effort** | Quarterly, allow-fail | Mizar, Nuprl, PVS, Minlog, Dedukti, Arend, KeY, Prism, UPPAAL, ViPER, NuSMV, Spin, TLC, CBMC, Seahorn, dReal, Boogie, Kissat, Alloy |

**Acceptance criteria**:
- Tier-1 matrix runs green on every PR
- Each backend has ≥1 canonical goal fixture that the live binary accepts/rejects correctly
- Mock tests retained as fast pre-CI smoke (keep `sanity_suite.rs`)
- `guix shell -m manifests/live-provers.scm -- cargo test --test live_prover_suite --features live-provers` works locally

**Out of scope for L3**: Cap'n Proto schemas (L1), Chapel integration (L2).

---

### L1 — Cap'n Proto Protocol Swap — **~2 weeks**

**Goal**: replace HTTP+JSON Rust↔Julia channel and define canonical wire format for future Chapel + ReScript layers.

**Artefacts**:
- `schemas/echidna.capnp` — canonical schemas: `ProofGoal`, `ProofResult`, `TacticSuggestion`, `GnnRankRequest`, `GnnRankResponse`, `ProverInvocation`, `TrustedOutcome`
- `src/rust/ipc/` — Cap'n Proto Rust bindings, transport (Unix-domain socket first, TCP fallback)
- `src/julia/ipc.jl` — Julia Cap'n Proto reader/writer (use `CapnProto.jl` or shim via C)
- `src/abi/CapnSchemas.idr` — Idris2 ABI mirror proving schema compatibility
- `ffi/zig/capnp_bridge.zig` — C-ABI bridge for polyglot consumers
- `bindings/rescript/echidna_capnp.res` — ReScript client bindings (for UI layer)

**Acceptance criteria**:
- Existing HTTP-JSON GNN client fully replaced; zero `serde_json` calls on Rust↔Julia hot path
- All schemas have Idris2 ABI proofs (zero `believe_me`)
- Benchmarks: Cap'n Proto round-trip ≤ 50% of JSON latency for GNN rank request
- Schema versioning doc (`schemas/VERSIONING.md`) explains forward/backward compat rules

**Out of scope for L1**: Chapel (L2), gRPC replacement (keep as declared schema; Cap'n Proto over UDS is the live path).

---

### L2 — Chapel Maximum Integration — **~5–6 weeks**

**Goal**: Chapel is a first-class execution layer handling parallelism Rust-with-Rayon can't match.

**Layered sub-phases**:

1. **L2.1 — Portfolio dispatch (promote POC)** ~1 week
   - `src/chapel/portfolio.chpl` — migrate from `chapel_poc/`
   - Consume `ProverInvocation` from Cap'n Proto
   - 48-prover parallel race via `coforall`, atomic first-wins, SIGKILL losers
   - Wired into `src/rust/dispatch.rs` behind `--chapel` feature flag via Zig FFI
2. **L2.2 — Speculative tactic search** ~1 week
   - `src/chapel/tactic_search.chpl`
   - Parallel beam search, parallel MCTS over tactic trees
   - Speculative branch execution with cancellation
3. **L2.3 — Corpus-parallel ops** ~1 week
   - `src/chapel/corpus.chpl`
   - Parallel replay of 66k proofs (`forall` over corpus)
   - Parallel premise scoring, tactic mining, indexing
4. **L2.4 — Mutation testing parallelism** ~3 days
   - `src/chapel/mutation.chpl`
   - Fan out 1000s of mutants across all cores/locales
5. **L2.5 — Multi-locale distributed** ~1.5 weeks
   - PGAS-sharded corpus across locales
   - Locale-aware prover dispatch (NUMA / multi-node)
   - GPU-locale offload for GNN embeddings (Chapel GPU support)
6. **L2.6 — Numeric hot paths** ~4 days
   - `src/chapel/numeric.chpl`
   - Parallel GNN embedding pre-processing
   - Parallel Pareto frontier, parallel confidence statistics
7. **L2.7 — CI + bench** ~3 days
   - `.github/workflows/chapel-live.yml`
   - Chapel-in-dispatch benchmarks vs Rust-only baseline
   - Reproducibility harness

**Acceptance criteria**:
- Chapel invoked on the hot path by default (feature-flagged off → opt-in → default-on progression across milestones)
- Benchmarks show measurable speedup for portfolio solving on 8+ core machines
- Multi-locale path proven on dev hardware (single-locale covers 80% of value)

---

## Current State Snapshot (audit 2026-04-19)

**Wiring depth** (sampled 8 backends):
- **Deep** (persistent process + structured protocol parsing): Z3, CVC5, Coq (SerAPI), Lean 4, Idris2
- **Medium** (subprocess + output parse, no streaming): Agda, Vampire
- **Stub-ish / thin**: Dafny (165 LoC — flag for hardening during L3)

**IPC today**:
- Rust ↔ Julia: **HTTP + JSON** (`src/rust/gnn/client.rs:1-195` → `src/julia/api_server.jl`, port 8090) — violates `no_json_emit` rule
- Rust ↔ Chapel: **Stub** (`src/zig_ffi/chapel_bridge.zig`) — not in dispatch path
- Rust ↔ gRPC: schema-only; `dispatch.rs` uses in-process traits

**CI today**:
- `.github/workflows/rust-ci.yml` runs mock-only tests on every PR
- `.github/workflows/chapel-ci.yml` compiles Chapel but doesn't feed into dispatch
- **Zero live-prover invocations in CI**

**Corpus**:
- 66,674 proofs across 16 prover systems (from `COMPLETE_CORPUS_SUMMARY.md`)
- 179,933 tactics, 10,599 unique tactic signatures, 300 indexed premises

---

## Memory-Rule Cross-Checks

Applies to this plan:
- `feedback_wire_everything` — no stubs; L2 promotes the POC rather than leaves it
- `feedback_no_json_emit_a2ml` — L1 kills JSON on hot path
- `feedback_verisimdb_policy` — L3 test harness should emit VeriSimDB records per live run
- `feedback_full_battery_before_claims` — "production" claim means tests + benches + panic-attack + proofs + axioms + causality + verifiable I/O
- `feedback_commit_asap` — one unit = one commit
- `feedback_meander_resource_costs` — Chapel builds slow; cache aggressively in CI
- `feedback_push_merge_default` — GitHub-only mirror
- `feedback_resource_awareness` — max 3 parallel subagents, 2 parallel Bash
- `feedback_opus_supervise_haiku_first` — Opus orchestrates, delegate mechanical subtasks to Haiku
- `user_priority_order` — dependability > security > interop > usability > performance (Cap'n Proto choice respects this)

---

## Handover Artefacts

- `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md` ← this file (master)
- `~/Desktop/ECHIDNA-L3-LIVE-PROVER-CI-PROMPT.md` — continuation prompt for L3
- `~/Desktop/ECHIDNA-L1-CAPNPROTO-PROMPT.md` — continuation prompt for L1
- `~/Desktop/ECHIDNA-L2-CHAPEL-PROMPT.md` — continuation prompt for L2
- `.machine_readable/6a2/STATE.a2ml` — mirrored wave entry in-repo

## Session Log

- **2026-04-19** — Kickoff. Audited wiring depth (Opus + Explore agent). User confirmed decisions D1–D5. Created Desktop handover docs + L3 Wave-1 artefacts (Guix manifest, Nix fallback, `live-provers.yml`, `tests/live_prover_suite.rs` skeleton with Tier-1 backends). Committed as one unit.
