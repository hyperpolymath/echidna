# Echidna Production-Wiring — TODO

**Source of truth for pending work.** Complements `ECHIDNA-STATE.md` (where
we are) and the full continuation prompts at
`verification-ecosystem/echidna/docs/handover/{L1,L2,L3,PRODUCTION-WIRING-PLAN}.md`.

Last updated: 2026-04-26 (session 2).

Execution order from the master plan: **L3 → L1 → L2.** L3 blocks L1;
L1 blocks L2 (because Chapel consumes Cap'n Proto schemas).

---

## Completed items (2026-04-26)

- ✅ **`echidna-graphql` build** — ProverKind 30→113 variants, trait stubs, FFI casts fixed (`5aec9d5`). All three interface crates now build clean.
- ✅ **FFI boundary audit** — `audits/audit-ffi-boundary.md` + `audits/assail-classifications.a2ml` classifying all legitimate UnsafeCode at FFI boundaries (`b4d682b`).
- ✅ **`bounded_read_config`** — sync 1 MiB-capped read helper in `src/rust/integrity/io.rs`; `solver_integrity.rs` migrated.
- ✅ **F5 (boj-server `echidna-llm-mcp`)** — `consult` + `suggest_tactics` operations implemented; Elixir router patched for `{operation, params}` alias; 176 boj-server tests pass (`a6c8456`).
- ✅ **Real-Chapel CI job** — `chapel-ci.yml` Job 4 `rust-chapel-real` added (`continue-on-error: true`), downloads real Chapel lib and builds Rust without Zig stubs (`3fb6c6b`).
- ✅ **Stage 8b — Agda meta-proofs 6→12 modules** — TrustLattice, AxiomMonotonicity, DispatchOrdering, SoundnessPreservation, PortfolioConsistency, CertificateChain (`6caff97`).
- ✅ **Stage 8d — panic-attack proptest harnesses** — 13 property tests across term/trust/danger/pareto modules (`99198b0`).
- ✅ **Stage 8d — AFL++ fuzz targets** — 3 real libfuzzer targets (proof_state JSON deserialization, trust pipeline, axiom tracker) replacing stub (`46453c4`).
- ✅ **Stage 8a — Idris2 trust-kernel proofs** — TrustKernelMonotonicity, AxiomPolicyOrdering, ClampTrustBounds; zero believe_me; PROOF-NEEDS.md updated (`1444a30`).
- ✅ **Stage 3a/3b — VeriSimDB read paths + dispatch advisor** — `query_by_goal_hash`, `query_prover_success_by_class`, `VeriSimAdvisor`, `verify_proof_verisim_guided` (`804ead6`).
- ✅ **S5 — GNN-augmented suggest_tactics** — `gnn_augment_tactics` helper; rocq/lean/agda/isabelle/z3 backends prepend GNN-ranked apply tactics (`c4bc272`).
- ✅ **S1 batch — 12 Julia premise extractors** — SMT-LIB, TPTP, Dafny, Lean3, HOL Light, Metamath, Tamarin, ProVerif, Boogie, Viper, MiniZinc, Twelf; named extractors 12→24 (`d7a2493`).
- ✅ **S1 batch — 20 more extractors** (24→44): Isabelle, Coq/Rocq, Why3, TLAPS, Idris2, Vampire, EProver, SPASS, AltErgo, FStar, Mizar, CVC5, HOL4, ACL2, Minlog, PVS, Nuprl, Twelf2, Z3-DTsolver, Agda-core (`53ee39a`).
- ✅ **S1 final 6 extractors** (44→50): SPIN/Promela, CBMC-C, SCIP-opt, KeY-Java, Alloy-Relational, NuSMV-temporal (`4ead82a`).
- ✅ **GPUVerify + Faial backends** — GPU CUDA/OpenCL verification; `src/rust/provers/gpuverify.rs` + `faial.rs`; ProverKind variants 113/114; ProverKindInjectivity updated; Julia GPU extractors (`a1b0e82`, `89b76be`).
- ✅ **live-provers.yml `--features live-provers` compile fix** — `gnn_api_url: None` added to `live_prover_suite.rs` and `live_prover_verify.rs` live_config(); GPU backends added to T4-GPU matrix job (`dc02547`).
- ✅ **Wave-4 per-backend rationale** — all 19 backends documented with mock-only justification in `STATE.a2ml [wave-4-rationale]` (`1ca9862`).
- ✅ **chapel-ci.yml checkout v4→v6** — 3 stale v4 SHA pins upgraded to canonical v6.0.2 (`1ca9862`).

## P0 — Immediate pickup

| Task | Lane | Est | Blocks |
|------|------|-----|--------|
| **Watch next `0 3 * * *` UTC nightly of `live-provers.yml`** — Wave-2 installers (idris2 / isabelle / dafny / fstar / tlaps) are local-pass but CI-unverified. Fix red matrix cells in-place. Likely failure modes: Isabelle2024 500 MB download timeout, tlapm release URL drift, `fstar.exe` symlink resolution, apt mirror changes. | L3 | 1 session | L3 Wave-3 gate |
| ~~**Real-Chapel CI job**~~ | ✅ Done (`3fb6c6b`) | — | — |

## P1 — L3 completion (~2 weeks)

### Wave-3 (Tier-3 weekly, 9 backends) — per-backend Containerfiles (Podman)

Handover hints live in `.machine_readable/6a2/STATE.a2ml [wave-3-handover-hints]`.

| Backend | Install strategy |
|---------|------------------|
| Tamarin | Haskell Stack build; try prebuilt binaries from `tamarin-prover/tamarin-prover/releases` first |
| ProVerif | OCaml via opam; consider INRIA Docker image |
| Imandra | Proprietary — needs signed registration. Gate on Imandra licence decision (see open questions). |
| SCIP | Academic licence lifted; prebuilt `.deb` from scipopt.org |
| OR-Tools | Large C++ build; use official ortools Python wheel's bundled binaries |
| HOL4 | Poly/ML + Moscow ML build; tractable but slow |
| ACL2 | Common Lisp (SBCL/CCL); prebuilt SBCL image + `make` |
| Twelf | SML/NJ build |
| Metamath | In-process pure-Rust verifier per `stub-audit-result`; external binary optional |

### Wave-4 (Tier-4 quarterly, 19 backends, allow-fail placeholder)

Mizar, Nuprl, PVS, Minlog, Dedukti, Arend, KeY, Prism, UPPAAL, ViPER, NuSMV, Spin, TLC, CBMC, Seahorn, dReal, Boogie, Kissat, Alloy. Retain as mock-only unless a maintainer volunteers a Containerfile. Document why each stays mock in a per-backend one-liner.

### Wave-5 (new backend targets, no adapter yet)

Backends not yet scaffolded in `src/rust/provers/`; ProverKind enum, factory dispatch, `kind_to_u8` discriminant, Idris2 injectivity proof, FFI table all need entries before any CI work. Tracked here so they are not forgotten:

| Backend | Scaffold plan | Accessibility |
|---------|---------------|---------------|
| Andromeda | New `provers/andromeda.rs` adapter shelling out to `andromeda` CLI; OCaml source build required | Open-source (MIT), build from source |
| Theorema | Deferred — requires Mathematica licence (commercial) | Access-blocked in OSS CI; revisit if a maintainer has a licence |
| Globular | Not a CLI prover (web UI for higher category theory) — skipped unless scoped to graphical proof capture | N/A |

### L3 hygiene

- ~~**Dafny deep-wiring upgrade**~~ — ✅ Done (`e54275d`): temp-file subprocess, term_to_dafny_expr, real suggest_tactics.
- ~~**VeriSimDB record emission**~~ — ✅ Done (`13cf817`): `emit_live_result()` wired in `assert_version_reachable`.
- **`guix shell -m manifests/live-provers.scm -- just test-live`** — local-reproducibility acceptance criterion; confirm works end-to-end.
- **L3 hand-to-L1 gate**: Tier-1 green on main for ≥ 7 days + all four waves landed or explicitly deferred with rationale in STATE.a2ml.

## P2 — L1: Cap'n Proto protocol swap (~2 weeks, gated on L3 hand-off)

Rationale: HTTP+JSON on Rust↔Julia hot path (`src/rust/gnn/client.rs:1-195` → `src/julia/api_server.jl:8090`) violates `feedback_no_json_emit_a2ml`.

### Deliverables

- `schemas/echidna.capnp` — canonical wire schemas: `ProofGoal`, `ProofResult`, `TacticSuggestion`, `GnnRankRequest`, `GnnRankResponse`, `ProverInvocation`, `TrustedOutcome`.
- `schemas/VERSIONING.md` — forward/backward compat rules.
- `src/rust/ipc/` — Cap'n Proto transport module; UDS primary, TCP fallback.
- Replace HTTP calls in `src/rust/gnn/client.rs` with UDS + Cap'n Proto.
- `src/julia/ipc.jl` — use `CapnProto.jl` if mature; otherwise shim via C-ABI through Zig.
- `src/abi/CapnSchemas.idr` — Idris2 ABI mirror proving schema compatibility, zero `believe_me`.
- `ffi/zig/capnp_bridge.zig` — C-ABI bridge for polyglot consumers.
- `bindings/rescript/echidna_capnp.res` — ReScript UI bindings.
- `just capnp-gen` recipe regenerating all bindings; CI check that generated code is committed.

### Acceptance

- Zero `serde_json::to_*`/`from_*` on Rust↔Julia hot path (verify with code-only grep per `feedback_code_only_grep_for_banned_patterns`).
- Idris2 ABI compiles zero `believe_me`.
- Cap'n Proto round-trip ≤ 50% of JSON latency for GNN rank request.
- Round-trip property tests on all six schemas (Rust, Julia, Idris2).
- Existing GraphQL/gRPC/REST interfaces unchanged — Cap'n Proto is the **internal** wire format.

### Design questions to settle early

1. UDS path convention: `/run/echidna/ipc.sock` vs `$XDG_RUNTIME_DIR/echidna/ipc.sock`.
2. Initial handshake signed with existing BLAKE3/SHAKE3-512 integrity keys?
3. Streaming vs request-response: Cap'n Proto RPC streams for GNN batch inference?
4. Multi-locale Chapel: schemas need to survive locale-to-locale transit; design now so L2 doesn't re-spec.

## P3 — L2: Chapel maximum integration (~5–6 weeks, gated on L1)

Existing POC: `chapel_poc/parallel_proof_search.chpl` (420 LoC) + the self-linking FFI bridge (`53ab9b8`). **Not yet in dispatch path.** Sub-waves:

| Sub-wave | Scope | Est |
|----------|-------|-----|
| L2.1 | Portfolio dispatch (promote POC) → `src/chapel/portfolio.chpl`; atomic first-wins; wire into `src/rust/dispatch.rs` behind `--chapel` feature flag | 1 week |
| L2.2 | Speculative tactic search — parallel beam + MCTS; consumes `TacticSuggestion` stream from GNN | 1 week |
| L2.3 | Corpus-parallel ops — `forall` over 66,674-proof corpus; replay, premise scoring, tactic mining, inverted index | 1 week |
| L2.4 | Mutation-testing parallelism — fan out 1000s of mutants; integrate with `verification/mutation.rs` | 3 days |
| L2.5 | Multi-locale distributed — PGAS-sharded corpus; locale-aware dispatch; GPU-locale offload for GNN embeddings | 1.5 weeks |
| L2.6 | Numeric hot paths — parallel embedding pre-proc, Pareto frontier, confidence statistics | 4 days |
| L2.7 | CI + bench — `chapel-live.yml`; Chapel portfolio vs Rust+Rayon; reproducibility harness | 3 days |

### L2 acceptance

- Chapel invoked on the hot path by **default** after L2.7 benchmarks prove ≥ 1.5× speedup on 8+ core machines (until then: feature-flagged, opt-in).
- `src/chapel/` has 6+ modules wired via Zig FFI + Cap'n Proto.
- `chapel_poc/` archived with redirect note in its README.
- Multi-locale path proven on at least one dev-hardware config.
- No Rust code duplicates what Chapel does best (avoid double-paths).

## P4 — Adjacent / deferred

- **Tamarin + ProVerif backend stale-listing** — corrected 2026-04-19 in STATE.a2ml. They are fully wired (592 / 799 LoC Rust) and registered in `ProverFactory`. Handover docs + AI-WORK-todo already updated.
- **No TODO/FIXME in src/rust/ Rust core** — corrected 2026-04-19; standing property.
- **VeriSim RDF cross-prover alignment** — blocked on `verisimdb#3`; not `echidna#3`.
- **TypeDiscipline deep native wiring** (phase-2 deferred) — per-discipline proof encoding, Idris2 validator tagging, family-aware GNN features, per-discipline integration tests under `tests/disciplines/`, Katagoria fixture round-trip, per-discipline dispatch scoring.
- **HP type-checker ecosystem backends** — 13 corpus-only provers (KatagoriaVerifier, Modal/Session/Choreographic/Epistemic/Refinement/Echo/Dependent/QTT/Effect-Row/Tropical/TypeLL etc.) need Rust backends shelling out to the HP stack (Ephapax, Wokelang, AffineScript) — corpus contributes to vocab/training only until backends wire up dispatch.
- **CR-1..CR-10 cross-repo tests** from standards `TESTING-TAXONOMY.adoc` — notably CR-2 foreign-enum exhaustive-match lint, CR-3 FFI roundtrip over all variants, CR-6 upstream-HEAD sentinel.
- **`verisim` feature compile errors** — `cargo check --lib --features verisim` fails with 22 errors (missing `warn` import, unresolved `Goal`/`theorem`, private-field access in `VeriSimDBClient`). Unrelated to main build; gate off by default.
- **Remaining CI infra failures** — Mirror to Git Forges Radicle SSH key unset; Instant Sync `.git-private-farm` bad credentials. Tokens human-owned — see `YOUR-ACTIONS-todo.md §0c`.

## Non-goals (explicit)

- HTTP capability gateway + SDP for local (non-goal — v2 federation only).
- L1 replacing the declared GraphQL/gRPC/REST external surfaces — Cap'n Proto is **internal** wire format only.
- `boj_cartridge_invoke` wiring ahead of primary HTTP path — not blocking.

## Open questions

1. **Imandra licence** — signed registration needed before Wave-3 Containerfile can download. Do you already hold a licence, or defer Imandra to Wave-4? (Current default: Wave-3 scaffold mentions it but install is gated on this decision.)
2. **Cap'n Proto Julia library** — commit to `CapnProto.jl` and accept its maturity constraints, or shim through C-ABI via the existing Zig FFI layer? Shim is more work up front but removes a dependency risk.
3. **Chapel default-on threshold** — the plan says ≥ 1.5× speedup to flip default-on. Is that the right threshold, or do we want absolute wall-clock improvement too (e.g. ≥ 5 s saved on portfolio dispatch of the full 48-backend set)?

## Rules active (applies to all phases)

- `feedback_wire_everything` — no stubs; promote not re-implement.
- `feedback_no_json_emit_a2ml` — L1's raison d'être.
- `feedback_verisimdb_policy` — L3 harness + all IPC traffic emit VeriSimDB records.
- `feedback_full_battery_before_claims` — "production" = tests + benches + panic-attack + proofs + axioms + causality + verifiable I/O.
- `feedback_commit_asap` — one unit = one commit.
- `feedback_push_merge_default` — push `origin` only (GitHub); no other forges directly.
- `feedback_meander_resource_costs` — Chapel builds slow; cache aggressively.
- `feedback_resource_awareness` — max 3 parallel subagents, 2 parallel Bash.
- `feedback_opus_supervise_haiku_first` — Opus orchestrates, Haiku for mechanical subtasks.

## Task status snapshot

**Complete (L3 Wave-1 + Wave-2 + Chapel self-link):** 19 Tier-1/2 backends CI-installable; 18/18 live tests pass locally; `cargo build --features chapel` links standalone against bundled Zig stubs; Tamarin/ProVerif confirmed fully wired (were stale-listed as "planned").

**P0 immediate:** Wave-2 CI verification (next nightly); Real-Chapel CI job.

**P1 L3 finishers:** Wave-3 (9 Containerfiles), Wave-4 (19 placeholder + rationale), Dafny deep-wiring, VeriSimDB schema.

**P2 L1:** Not started. Gated on L3 hand-off.

**P3 L2:** POC present + self-link fix landed; actual `src/chapel/` modules not started. Gated on L1.
