<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: MPL-2.0 -->
# Changelog

All notable changes to ECHIDNA will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed

- ci(chapel): pin runs-on to ubuntu-22.04 for Chapel 2.8.0 libclang-cpp.so.14 ABI compatibility (#183). Chapel 2.8.0's debian package is built against LLVM-14 / Ubuntu 22.04; on Ubuntu 24.04 (`ubuntu-latest`) apt resolves the unmet dependency with libclang-cpp-18, leaving `chpl` unable to load. Also switched install to `apt-get install -y /tmp/chapel.deb` so libclang-cpp14 / libllvm14 are resolved declaratively in one pass.

### Added — Saturation campaign 2026-06-01

Branch `prover-corpus-saturation` (commits f73ee00..cb8caff). Owner-directed marginal-benefit push across corpus, vocabulary, arbitration, exchange, and wire-schema surfaces. See `docs/decisions/2026-06-01-saturation-campaign.md`.

- **13 new corpus adapters** under `src/rust/corpus/` (`isabelle`, `metamath`, `mizar`, `hol_light`, `hol4`, `dafny`, `why3`, `fstar`, `acl2_books`, `tptp`, `smtlib`, `proofnet`, `minif2f`). Total corpus adapter coverage: 4 → **17** (4.25×). See `docs/CORPUS-ADAPTERS.md`.
- **9 new per-prover synonym TOMLs** (`isabelle_afp`, `metamath`, `mizar`, `hol_light`, `hol4`, `dafny`, `why3`, `fstar`, `acl2`). Total: 5 → **14** per-prover tables.
- **3 cross-prover taxonomic dictionaries** (underscore-prefix): `_msc2020.toml` (87 codes), `_wordnet_math.toml` (~80 lemmas), `_conceptnet_seed.toml` (~55 edges, offline-resilient).
- **3 new arbitration mechanisms** under `src/rust/verification/`: `bayesian_arbiter` (log-odds posterior), `dempster_shafer` (HighConflict trip at k > 0.95), `pareto_arbiter` (4-axis Pareto frontier).
- **4 new exchange bridges** under `src/rust/exchange/`: `tptp`, `smtlib`, `smtcoq` (stub bridge), `lambdapi`.
- **Formal VeriSim E-R schema** at `docs/architecture/VERISIM-ER-SCHEMA.md` (12 entities + 7 relationships, crosswalk Rust↔Cap'n Proto↔ClickHouse) + Cap'n Proto wire schema `crates/echidna-wire/schemas/verisim_er.capnp` (@0xe4dc7b1f01a06001).
- **Chapel + Julia integration hooks** at `docs/architecture/CHAPEL-SATURATION-HOOKS.md` + `docs/architecture/JULIA-SATURATION-HOOKS.md` (specifications only — wave3 chapel + GNN-training-trigger files deliberately untouched).
- **New Julia helper modules** `src/julia/corpus_loader.jl` + `src/julia/saturation_synonyms.jl` (bridge Rust corpus JSON + saturation synonym TOMLs into the GNN training pipeline).
- **Saturation campaign ADR** at `docs/decisions/2026-06-01-saturation-campaign.md`.
- **Handover lane doc** at `docs/handover/PROVER-CORPUS-SATURATION-LANE.md` (collision-avoidance contract with `wave3/161-162-bench-telemetry-corpus`).
- **Corpus adapter index** at `docs/CORPUS-ADAPTERS.md`.
- **Justfile recipes**: `corpus-ingest-saturation`, `corpus-stats-all`, `synonym-load-test`, `test-saturation`, `arbiter-smoke`, `er-schema-drift-check`.
- **139 new unit tests** across the saturation modules (1 ignored heuristic-limit).

### Changed

- `src/rust/suggest/synonyms.rs`: `load_all` extended to 14 provers; new `CrossProverDicts` + `load_cross_prover_dicts()` + `SynonymTable::merge_external()`.
- `src/rust/corpus/mod.rs`, `verification/mod.rs`, `exchange/mod.rs`: register new modules (additive).
- Module-level doc comments on `corpus/mod.rs`, `verification/mod.rs`, `verisim_bridge.rs` cite the new schemas + arbiters.

### Documentation

- Wiki updated (Home, Architecture, Getting-Started, Guides, FAQ, Troubleshooting) to reflect the new surface.
- README.adoc + EXPLAINME.adoc updated with new headline counts + per-module references.
- Machine-readable metadata under `.machine_readable/6a2/` (STATE / META / ECOSYSTEM / NEUROSYM) updated additively.
- 9 RSR-template substitution gaps closed in CODE_OF_CONDUCT.md / SECURITY.md / AUTHORS.md.

### Verification

- `cargo check --lib` clean (~24s).
- `cargo test --lib -- corpus:: verification::{bayesian,dempster_shafer,pareto}_arbiter exchange::{tptp,smtlib,smtcoq,lambdapi}`: **139 passed, 0 failed, 1 ignored** (corpus::dafny::tests::detects_datatype_and_extern — heuristic body-less-extern-method limitation).
- Zero collisions with `wave3/161-162-bench-telemetry-corpus`.

---

## [2.3.0] - 2026-06-01

### Added
- **105 ProverKind variants** (exhaustive HP type-checker ecosystem).
- Updated `ProverKindInjectivity.idr` to prove injectivity for all 105 variants.
- Expanded Isabelle synthetic proof corpus (105 entries).
- Resolved security alerts: Binary-Artifacts (#13), rand (#11, #10), rustls-webpki (#13, #12).
- Atomic repush consolidating corpus expansion and security hardening.

## [2.2.0] - 2026-04-05

### Changed

- **VQL → VCL + verisimdb → verisim rename** (ecosystem-wide, 2026-04-05).
  Internal code, docs, module names, and machine-readable manifests
  adopt the new ecosystem terminology. `verisim_bridge.rs` (was
  `verisimdb_bridge.rs`), `vcl_ut.rs` and `vcl_ut.zig` (were `vql_ut.*`),
  `verisim.a2ml` integration manifest (was `verisimdb.a2ml`). GitHub URL
  `hyperpolymath/verisimdb` preserved.

### Added

- **F\* corpus** (`proofs/fstar/`): 5 arithmetic lemmas (AddComm,
  AddAssoc, MulZero, NonNeg, Refl) discharged by F\*'s SMT backend.
- **TPTP corpus** (`proofs/tptp/`): 8 first-order problems for
  Vampire + E Prover, with known SZS statuses.
- **DIMACS corpus** (`proofs/dimacs/`): 5 SAT/UNSAT problems for
  CaDiCaL + Kissat.
- **Metamath seeds** (`proofs/metamath/tiny.mm`, `broken.mm`):
  smallest valid + deliberate-fail for the `run_metamath` runner.
- **Agda witness** (`proofs/agda/IdentityLaws.agda`): known-good
  natural-number identity proofs against agda-stdlib v2.3.
- **BasicTotality.idr**: small totality proofs that pass
  `idris2 --check` with no external dependencies.

### Fixed

- **Three broken Idris2 proofs repaired** (5/5 now type-check):
  - `AxiomCompleteness.idr`: 23× `prf = impossible` (invalid RHS)
    rewritten to `Refl impossible`.
  - `DispatchOrdering.idr`: rewritten as a minimal working proof
    (6-stage dispatch pipeline with LT witnesses for adjacent stages).
    Original had invalid constructor signatures with named args in
    return-type position.
  - `ProverKindInjectivity.idr`: replaced 48× `lteSuccRight $ ... $
    LTERefl` chains (unification failed) with direct `LTESucc (...)`
    constructor nesting. Type signature switched from
    `maxDiscriminant` alias to literal `48` so Idris2 can unfold
    `S ?right`. Added `import Data.Nat`.
- **Agda scoping bugs** in `Basic.agda`, `List.agda`, `Nat.agda`,
  `Propositional.agda`: files defined datatypes inside `where`
  clauses, putting them out of scope for outer signatures. All four
  rewritten as clean agda-stdlib-backed proofs (5/6 `.agda` files
  now compile).
- **TPTP precedence** in `proofs/tptp/transitivity.p`: added explicit
  parens around `(lt(X,Y) & lt(Y,Z))` before `=>` so E Prover parses
  it. Now Theorem-certified by both Vampire and E Prover.
- **`/api/verify` false-positive guard**: server-level check in
  `prove_handler` and `verify_handler` now returns `valid: false`
  when `parse_string` produces an empty `ProofState` (no goals,
  theorems, definitions, axioms, or variables) on non-empty input.
  Partial fix for the parse+export round-trip bug documented in
  `TEST-NEEDS.md`. Verified live: garbage to Coq/Lean now returns
  `valid: false` (was `true`); real proofs unaffected.
- **Isabelle prover backend de-stubbed** (`src/rust/provers/isabelle.rs`).
  `parse_string` previously discarded its `content` argument and always
  emitted a single `Term::Const("True")` goal, which `verify_proof` then
  short-circuited to `Ok(true)` — Isabelle was never actually invoked.
  It now extracts the theory name and top-level `theorem|lemma|corollary`
  declarations with nested-comment-aware scanning, stashes the raw `.thy`
  content in `ProofState.metadata["raw_thy_content"]`, and `verify_proof`
  writes that content to a unique per-invocation temp directory under the
  correct filename (Isabelle requires `<theory_name>.thy`) before invoking
  `isabelle process -l Main -e 'use_thys ["<path>"]'`.
- **Stale scaffolded temp-file path** in Isabelle's fallback verification
  path: previously wrote `echidna_verify.thy` containing
  `theory GeneratedProof`, causing filename/theory-name mismatch rejection
  by `isabelle build`. Now writes `GeneratedProof.thy` in a unique temp dir.

### Added

- `strip_isabelle_comments` helper for the Isabelle backend (handles nested
  `(* ... *)` blocks).
- 9 new unit tests for the Isabelle theory-header parsers (`test_strip_*`,
  `test_extract_theory_name_*`, `test_extract_lemma_names_*`) and the
  `parse_string` contract (metadata populated, goals non-trivial, context
  theorems enumerated, empty-theory fallback goal).
- Parser verified against a real 788-line `Tropical.thy` (tropical semiring
  formalisation): extracts theory name and all 55 theorems/lemmas.

### Notes

- Deployment of this fix to `echidna-nesy` on Fly.io requires rebuilding
  the container with the `isabelle` binary on `$PATH`. Without it,
  `verify_proof` returns `Ok(false)` with a `"Failed to run Isabelle
  process"` context error.
- Audit of all 50 prover backends confirmed Isabelle was the only truly
  stubbed one. `metamath.rs` and `typed_wasm.rs` are intentionally pure-Rust
  in-process verifiers (no subprocess needed by design). The remaining 47
  external-solver backends all spawn real solver subprocesses via
  `Command::new`.

---

## [1.6.1] - 2026-03-23

### Fixed

- Fixed `tamarin.rs` Definition type (added missing struct fields)
- Fixed non-exhaustive match arms in `main.rs`
- Removed unused imports across codebase
- Fixed `rustfmt.toml` for stable Rust (removed unstable options)
- Fixed `resolvers.rs` syntax error
- Applied `cargo fmt` across entire codebase

### Changed

- 389 tests passing (up from 306+)
- Project now compiles cleanly on stable Rust toolchain

---

## [1.6.0] - 2026-03-08

### Major Features

#### Zig FFI Layer (4 Shared Libraries)
- `libechidna_ffi.so` — Core prover management (init, shutdown, status, verify)
- `libechidna_overlay.so` — Overlay networks (Tor, IPFS, Ethereum)
- `libechidna_boj.so` — BoJ cartridge protocol
- `libechidna_typell.so` — TypeLL type-level operations
- All functions use dual `pub export fn` for both Zig `@import` and C linker access
- Bidirectional callbacks: init/prover-change/error/verify-complete (core), status/error/progress/circuit/pin (overlay)

#### Idris2 ABI Formal Proofs (7 Modules, Zero `believe_me`)
- `EchidnaABI.Types` — 30 ProverKind, FfiStatus, TrustLevel, Handle with So non-null proof
- `EchidnaABI.Layout` — DivisibleBy proof witnesses for 6 struct memory layouts (FfiStringSlice, FfiOwnedString, FfiSerializedTerm, FfiProverConfig, FfiTactic, FfiTacticResult)
- `EchidnaABI.Foreign` — Core FFI function declarations
- `Overlay`, `Overlay.Foreign` — Overlay network types and FFI
- `Boj.Foreign`, `TypeLL.Foreign` — BoJ and TypeLL FFI declarations
- All 7 modules type-check with idris2 v0.8.0

#### Generated C Headers
- `echidna_ffi.h` — 23 functions, 5 enums, 2 structs, 4 callback types
- `echidna_overlay.h`, `echidna_boj.h`, `echidna_typell.h`

#### zig REST Adapters
- Core adapter (ports 8100-8102: REST, gRPC, GraphQL)
- Overlay adapter (port 8103)
- BoJ adapter (port 7700)
- TypeLL adapter (port 7800)
- Tentacles adapter (port 8300)

#### Tentacles FFI/ABI Layer (7-Tentacles Agent System)
- `TentaclesForeign.idr` — Idris2 ABI definitions for 7-Tentacles agents with dependent type proofs
- `tentacles.zig` → `libechidna_tentacles.so` — Zig FFI with 7 agent management, OODA loop dispatch, and event callbacks
- `echidna_tentacles.h` — Generated C header for tentacles agent interface
- `tentacles.v` — zig REST adapter on port 8300 exposing agent management and OODA endpoints

### Added

- 30+ native Zig tests (`test-core-native`, `test-overlay-native`)
- VerifiedLayout record bundling fields + totalSize + structAlign + erased proof
- Round-trip enum proofs (OverlayKind, CidVersion, etc.)
- Platform pointer size proofs (ptrSize64, ptrSizeWASM)
- ABI-FFI-README.md with ECHIDNA-specific architecture documentation

### Fixed

- Idris2 Types.idr: Replaced `DecEq ProverKind` (30-constructor catch-all) with `Eq` via ordinal comparison
- Idris2 Types.idr: Rewrote Handle to use `choose (not (ptr == 0))` pattern
- Idris2 Layout.idr: Complete rewrite — `So`-based proofs replaced with `DivisibleBy` witnesses (Idris2 v0.8 limitation: So proofs don't reduce through named definitions)
- Idris2 Overlay.idr: Trailing `|||` doc comment changed to `--` comments

---

## [1.5.0] - 2026-02-12

### Major Features

#### Trust & Safety Pipeline
Complete implementation of 13-component trust-hardening system:
- ✅ Solver binary integrity (SHAKE3-512 + BLAKE3 checksums)
- ✅ SMT portfolio solving with cross-checking
- ✅ Proof certificate validation (Alethe, DRAT/LRAT, TSTP)
- ✅ Axiom usage tracking (4 danger levels: Safe, Noted, Warning, Reject)
- ✅ Solver sandboxing (Podman, bubblewrap, none)
- ✅ 5-level trust hierarchy for confidence scoring
- ✅ Mutation testing for specifications
- ✅ Unified prover dispatch pipeline
- ✅ Cross-prover proof exchange (OpenTheory, Dedukti)
- ✅ Pareto frontier for multi-objective proof search
- ✅ Statistical confidence tracking with Bayesian timeout estimation

#### Gitbot-Fleet Integration
- ✅ Integrated with gitbot-fleet orchestration system
- ✅ Registered as Tier 1 Verifier bot
- ✅ 5 finding rule types (ECHIDNA-VERIFY-001 through 005)
- ✅ Shared context layer for cross-bot coordination
- ✅ Findings flow to Hypatia learning engine
- ✅ Full test coverage (4 integration tests)
- ✅ Documentation: echidnabot/FLEET-INTEGRATION.md

### Added

**Prover Backends** (30 total):
- All backends fully implemented with substantial code
- Tier 1: Agda, Coq/Rocq, Lean 4, Isabelle/HOL, Z3, CVC5
- Tier 2: Metamath, HOL Light, Mizar
- Tier 3: PVS, ACL2, HOL4, Idris2, F*, Dafny, Why3, TLAPS, Twelf, Nuprl, Minlog, Imandra
- ATPs: Vampire, E Prover, SPASS, Alt-Ergo
- Constraint Solvers: GLPK, SCIP, MiniZinc, Chuffed, OR-Tools

**API Interfaces**:
- GraphQL API (async-graphql, port 8081)
- gRPC API (tonic, port 50051)
- REST API (axum + OpenAPI, port 8000)

**Documentation**:
- PERFORMANCE.md - Prover creation benchmarks (avg 2.5µs)
- SECURITY-SCAN-FINAL.md - Security audit results
- ROADMAP-v2.0.md - v2.0 feature roadmap
- ECOSYSTEM-INTEGRATION.md - Ecosystem service integration
- echidnabot/FLEET-INTEGRATION.md - Fleet integration guide

**Configuration**:
- .echidnabot.toml - Self-verification configuration

### Fixed

**Security** (39% reduction in weak points):
- Documented all 24 unsafe blocks in src/rust/ffi/mod.rs (FFI interop)
- Documented all 7 unsafe blocks in src/rust/proof_search.rs (Chapel FFI)
- Converted HTTP URLs to HTTPS in echidna-owned code (32 fixes)
- Verified bash variable quoting (11 scripts checked)
- Cleaned up TODO/FIXME technical debt markers (5 files)
- Final scan: 50 weak points (down from 82)

### Performance

**Prover Creation Benchmarks**:
- Fastest: MiniZinc (116ns)
- Slowest: Isabelle (15.5µs)
- Average: ~2.5µs

### Testing

- 306+ tests (all passing)
- Fleet integration: 4 tests
- Trust pipeline: Integration tests for all components

## [1.0.0] - 2025-12-01

### Initial Release

- 30 prover backend stubs
- Basic trust pipeline
- GraphQL/gRPC/REST APIs
- Julia ML scaffolding

---

[1.6.1]: https://github.com/hyperpolymath/echidna/compare/v1.6.0...v1.6.1
[1.6.0]: https://github.com/hyperpolymath/echidna/compare/v1.5.0...v1.6.0
[1.5.0]: https://github.com/hyperpolymath/echidna/compare/v1.0.0...v1.5.0
[1.0.0]: https://github.com/hyperpolymath/echidna/releases/tag/v1.0.0
