<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# ECHIDNA Roadmap

**Status**: canonical • supersedes the aspirational parts of
[`FUTURE_DEVELOPMENT_ROADMAP.md`](./FUTURE_DEVELOPMENT_ROADMAP.md).
**Last revised**: 2026‑04‑20
**Scope**: the shortest honest path from today's repo to the endpoint vision.

This document is the single source of truth for where ECHIDNA is going.
The domain‑specific plans under [`handover/`](./handover/) and
[`design/SPARK_ADOPTION_PLAN.md`](./design/SPARK_ADOPTION_PLAN.md) are
still authoritative for their sub‑areas; they fit *inside* this
roadmap as implementations of individual stages.

## 1. Endpoint

ECHIDNA, when complete, is the **reasoning substrate of the
hyperpolymath ecosystem** — not just a proof tool.  It is:

* a unified interface to every mature theorem prover, SMT solver,
  model checker, and type checker in public use;
* an ML layer (GNN + Transformer over Flux.jl) that actually learns
  premise selection, tactic synthesis, and strategy routing well
  enough to beat hand‑curated choices on held‑out theorems;
* a persistent E‑R layer (Verisim) that stores every proof, tactic
  application, and version as a content‑addressed row and closes a
  real learning loop over historical outcomes;
* a parallel dispatch layer (Chapel) that runs portfolio solves
  across CPU cores and dispatches specialised work to coprocessors
  (GPU / tensor / vector / FPGA / QPU);
* a high‑speed IPC fabric (Cap'n Proto) between the Rust core and
  the Julia ML sidecar and between the backend and the frontend;
* a frontend in AffineScript + Deno (TEA architecture) with i18n via
  the LOL locale repo;
* a 16‑endpoint Zig ABI that external consumers (Coursera labs,
  other projects) link against, with an SPDX‑pinned, Guix‑built,
  Chainguard‑based container managed by Stapeln and hardened by the
  Vordr / Selur / Svalinn / Cerro‑Torre surround;
* itself formally verified — the trust kernel's critical invariants
  are proved in SPARK and in Idris2 / Agda.

From a user's seat: **indistinguishable from magic for easy
obligations, honest about ambiguity for hard ones, never silently
wrong.**

## 2. Stage map

```
Stage 1  Train the model at all             ML layer can receive signal
    1a  extractors emit premises            [done 2026‑04‑20, 22 of 50 ✓]
    1b  align_premises joins correctly      [done 2026‑04‑19 ✓]
    1c  residual extractor gaps fixed       [in progress, 28 to go]
    1d  vocab covers the surface            [255 K; target ~1 M]

Stage 2  Signal becomes useful              MRR moves off 0.66 baseline
    2a  run training at scale               hardware task
    2b  online vocab growth                 new feature
    2c  re‑baseline and publish metrics     run gate

Stage 3  Learning loop closes               model improves from outcomes
    3a  Verisim read paths                  cross‑prover queries by goal_hash
    3b  hypatia strategy loop wired         `mv_prover_success_by_class` reads
    3c  Proof / TacticApplication / ProofVersion emission wired
                                            [defined 2026‑04‑19 ✓, emission pending]

Stage 4  Interaction layer honest           every declared ProverKind works
    4a  typed_wasm → crates/typed_wasm      [done 2026‑04‑22 ✓]
    4b  39 TypeChecker variant dispatch     [done 2026‑04‑22 ✓, all Sigma‑routed]
    4c  tactic synthesis template           [86/91 done; 5 suggest_tactics stubs remain]
    4d  search_theorems template            [done 2026‑04‑27 ✓ — cross-prover layer
                                             added at dispatcher (CLI/REST/REPL all
                                             call `vcl_ut::cross_prover_search_names`).
                                             The 72 backend `Ok(vec![])` returns are
                                             correct: they report "no native search
                                             command" — cross-prover semantics live
                                             one layer up where Verisim covers all
                                             provers in one query.]

Stage 5  Distributed & fast                 scale + specialised hardware
    5a  Cap'n Proto IPC                     Rust ↔ Julia, :8090
    5b  Chapel full integration             dispatch.rs picks by config
    5c  coprocessor abstraction             trait + tensor/vector/QPU/FPGA
    5d  Tier‑4 live‑CI provisioning         19 backends, Containerfile path

Stage 6  Cross‑prover semantics             translation actually works
    6a  OpenTheory bridge real              bidirectional term translation
    6b  Dedukti bridge real                 λΠ modulo as lingua franca
    6c  mathematical identity arbitration   canonicalise across representations
    6d  Coursera delivery                   Zig ABI exposes capability

Stage 7  Sovereign tooling surround         the rest of the ecosystem
    7a  Stapeln container lifecycle
    7b  Vordr entry gate
    7c  Selur scheduler
    7d  Svalinn trust boundary
    7e  Cerro‑Torre observability
    7f  AffineScript‑TEA frontend           src/rescript/, ≥33 modules
    7g  LOL i18n                            locale/ + t!() macro
    7h  Zig ABI 16‑endpoint surface         src/zig/echidna_abi.zig

Stage 8  Self‑verified                      ECHIDNA proves ECHIDNA
    8a  Idris2 meta‑proofs extend           from 32 modules to full kernel
    8b  Agda meta‑proofs extend             from 12 modules
    8c  SPARK‑verified trust kernel         crates/echidna-core-spark/
    8d  panic‑attack hardened               proptest + AFL++ nightly
```

## 3. Endpoint target — row by row

| Claim | Today | End‑state target |
|---|---|---|
| "Every important solver" | **128 ProverKind variants** (89 external prover bindings + 39 TypeChecker disciplines routed through TypedWasm); **5 `suggest_tactics` stubs**; **72 backends with empty native search but a cross-prover Verisim fallback at the dispatcher layer (CLI/REST/REPL)** | **All variants with real `suggest_tactics` (GNN‑ranked top‑k); per-backend search reflects each prover's native capability while cross-prover queries are served from Verisim by `goal_hash`** |
| "Vocab at 2.5 M" | 255 K | **~1 M canonical tokens** after Mathport + Iris + VST + Flyspeck + HoTT absorption, with **online growth** adding tokens during training |
| "Chapel fully supported" | 2 files, POC only | **`dispatch.rs` picks Chapel‑parallel dispatch by config**; runtime init + cancellation + error propagation wired; ≥1 OoM speedup on portfolio solves |
| "Cap'n Proto serialisation" | 0 `.capnp` files | **`crates/echidna-wire/`** contains schemas for ProofState / Goal / Tactic / EmbeddingRequest / RankingResponse; IPC on :8090 is Cap'n Proto; JSON retained only as debug fallback |
| "Vordr / Selur / Svalinn / Cerro‑Torre / Stapeln" | Not present | Each named as a versioned dependency in Cargo.toml or the container definition, wired into its role |
| "AffineScript‑TEA frontend" | Not present (10 `.res` files stub) | **`src/rescript/`** holds ≥33 AffineScript‑TEA modules, persistent Model → Msg → Update loop, talks to core over Cap'n Proto WebSocket |
| "LOL i18n" | Not present | **`locale/`** with LOL‑sourced translations; `t!()` macro for every user‑facing string |
| "Rust/SPARK base stable" | Rust only | **`crates/echidna-core-spark/`** holds the Ada/SPARK‑verified kernel (axiom scanning, trust‑level computation); proved free of runtime errors; called from Rust via C ABI |
| "16‑endpoint Zig ABI" | 4 shared libs, endpoint count unverified | **`src/zig/echidna_abi.zig`** exports exactly 16 functions (`echidna_prove`, `echidna_apply_tactic`, `echidna_rank_premises`, `echidna_verify_certificate`, `echidna_post_octad`, `echidna_query_identity`, …) with a versioned header |
| "100 K+ per prover" | Uneven; long tail <20 K | **Top 15 provers ≥ 100 K records each**; next 20 ≥ 25 K each; bottom 10 synthetically augmented to ≥ 10 K; `stats_UNIFIED.json` reports the distribution publicly |
| "Panic‑attacked" | No fuzz infra | **`benches/panic_attack/`** with proptest + AFL++ harnesses covering every parser, FFI boundary, IPC schema; nightly CI ≥ 1 h; zero known panic paths |
| "Prover count" | **128 declared, all 128 factory‑dispatched** (no orphans, verified 2026‑04‑27) | **`ProverKind` ≥ 65 variants, every one factory‑dispatched**; CLAUDE.md states the canonical count; no orphans — **target met and exceeded** |

## 4. Current sprint — "the smallest set that flips half the table"

Five concrete commitments.  Landed together inside ~6 weeks they move
"Every important solver", "Vocab", "Prover count", half of "100 K+",
and start the self‑learning loop closure.

| # | Stage | Commitment | Agent tier | Status |
|---|---|---|---|---|
| S1 | 1c | Finish the extractor premise‑emission wave (22 done; 28 remaining) | **Sonnet** | in flight |
| S2 | 2a / 2c | Run training on the fixed corpus; record new MRR; commit `metrics_baseline.jsonl` | **Hardware / you** | gated by S1 |
| S3 | 4a / 4b | Extract `typed_wasm` to `crates/typed_wasm/`; route 39 TypeChecker variants through Sigma parameters | **Opus‑design + Sonnet‑impl** | **done 2026‑04‑22 ✓** |
| S4 | 3a / 3b | Wire Verisim cross‑prover read paths (`goal_hash` queries + `mv_prover_success_by_class` + hypatia loop) | **Opus‑design + Sonnet‑impl** | design pending — needs Verisim schema |
| S5 | 4c / 4d (pilot) | Tactic synthesis template for 5 high‑value provers (coq, lean, agda, isabelle, z3) using the GNN | **Opus‑design + Sonnet‑impl** | partly done — `suggest_tactics` is 86/91 already real; remaining work is GNN‑ranking integration |

After S1–S5 land, the roadmap's next sprint takes up Stage 5 (IPC +
Chapel + Tier‑4 CI) and Stage 8 begins in parallel.

### Sprint critical path (as of 2026‑04‑27)

```
S1 (extractors, Sonnet)  ──┬──►  S2 (training, hardware)   ──┐
                           │                                  │
                           └──►  S4 impl (needs S1 data) ────┴──►  S5 GNN ranking
                                  ▲
                                  │ blocked
                  Verisim schema design  ◄── NEEDED FROM OPUS,
                  (cross‑repo, not in     CROSS‑REPO INPUT.
                   echidna tree)
```

What is **not** blocking and can move now:

- **Phase 1a** (Leo3, Satallax, Lash, AgsyHOL) — done 2026‑04‑26 ✓
- **Phase 1b** (IProver, Princess, Twee, MetiTarski, CSI, AProVE) — done ✓
- **S3** (typed_wasm + 39 TypeChecker Sigma routing) — done ✓
- **`suggest_tactics`** — 86/91 real implementations; only 5 stubs left

What **is** blocking and needs Opus + cross‑repo input:

- **Verisim schema contract** (S4 design): the trait surface from echidna's
  side is straightforward (`async fn search_by_goal_hash(hash) ->
  Vec<ProofRecord>` and `async fn prover_success_by_class(class) ->
  Vec<(ProverKind, f32)>`) but the schema for `ProofRecord` and `class`
  lives in the Verisim repo and must be agreed there before echidna
  can wire reads. **Status as of 2026-04-27**: the Verisim schema is in
  fact fixed (`ProofAttempt` row → ClickHouse `proof_attempts` →
  `mv_prover_success_by_class` MV) and both echidna read paths
  (`query_prover_success_by_class` via `VeriSimAdvisor`,
  `cross_prover_search_names` via `vcl_ut`) and the write path
  (`spawn_record_attempt` from dispatch exits) are now wired.
  - End-to-end loop test: `tests/s4_loop_closure.rs`, runnable via
    `just test-s4-loop`. Skips cleanly when verisim-api is unreachable.
  - Operations runbook: [`docs/handover/S4-LOOP-CLOSURE-RUNBOOK.md`](handover/S4-LOOP-CLOSURE-RUNBOOK.md).
  - CI workflow filing is blocked on a published verisim-api image
    (no `ghcr-publish.yml` in `verification-ecosystem/verisimdb` yet).
    The runbook holds the workflow YAML ready to commit on that day.

## 5. Agent‑tier guidance

**Opus** (supervisor): architecture, schema design, cross‑module
contracts, merge review.  Touches: IPC protocol design, Verisim
schema additions, Chapel FFI shape, coprocessor trait, SPARK kernel
surface.

**Sonnet** (executor): focused implementation against a clear spec,
3–20 files, moderate complexity.  Touches: per‑prover tactic
synthesis, Verisim read client, typed_wasm crate extraction,
adapter code, worker logic.

**Haiku** (bulk): template‑driven mechanical edits, CI YAML,
deletes, repetitive stubs.  Touches: Tier‑4 provisioning shell
commands, extractor boilerplate, per‑prover factory branches that
follow a mould, localisation key additions.

## 6. Inheritance from existing planning docs

* **[`docs/FUTURE_DEVELOPMENT_ROADMAP.md`](FUTURE_DEVELOPMENT_ROADMAP.md)**
  — 2026‑01‑29 vision document.  Its chapters on RL for tactic
  search (§1.1), active learning (§1.2), and distributed dispatch
  map onto Stages 3c / 4c and 5b/5c of this roadmap.  Retain as
  background reading; this document is the source of truth for
  sequencing.
* **[`docs/handover/PRODUCTION-WIRING-PLAN.md`](handover/PRODUCTION-WIRING-PLAN.md)**
  — L1/L2/L3 sprint doc.  L1 = Stage 5a.  L2 = Stage 5b.  L3 Wave‑1/2
  are complete (in Stage 4 surface); Wave‑3 is partially complete in
  this branch (tamarin/proverif/metamath/twelf/ortools); Wave‑4 is
  Stage 5d.
* **[`docs/design/SPARK_ADOPTION_PLAN.md`](design/SPARK_ADOPTION_PLAN.md)**
  — design for the SPARK‑verified kernel.  Executes Stage 8c.
* **[`docs/handover/L1-CAPNPROTO-PROMPT.md`](handover/L1-CAPNPROTO-PROMPT.md)**
  — implementation brief for Stage 5a.  Use as the Sonnet prompt
  when S6 begins.
* **[`docs/handover/L2-CHAPEL-PROMPT.md`](handover/L2-CHAPEL-PROMPT.md)**
  — implementation brief for Stage 5b.
* **[`docs/handover/L3-LIVE-PROVER-CI-PROMPT.md`](handover/L3-LIVE-PROVER-CI-PROMPT.md)**
  — implementation brief for Stage 5d.
* **[`docs/handover/STATE.md`](handover/STATE.md)** and
  **[`.machine_readable/6a2/STATE.a2ml`](../.machine_readable/6a2/STATE.a2ml)**
  — running log of session‑by‑session progress.  Continue to use as
  running state; sync highlights to §2 of this document at each
  sprint boundary.

## 7. How to update this roadmap

* When a stage sub‑item lands, mark its line `[done YYYY‑MM‑DD ✓]`
  in §2 and update the corresponding row of §3.
* When a new endpoint target emerges, add a row to §3, extend §2's
  stage map if it doesn't already fit, and add it to the sprint
  plan in §4 only once it's next‑up.
* Don't remove rows from §3 when they land — keep the history
  visible, the "Today" column becomes "Done" and the "End‑state"
  column stays as the invariant.
* Record non‑trivial decisions in this doc, not in chat.
