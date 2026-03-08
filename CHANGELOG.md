# Changelog

All notable changes to ECHIDNA will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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

#### V-lang REST Adapters
- Core adapter (ports 8100-8102: REST, gRPC, GraphQL)
- Overlay adapter (port 8103)
- BoJ adapter (port 7700)
- TypeLL adapter (port 7800)

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
- GraphQL API (async-graphql, port 8080)
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

[1.6.0]: https://github.com/hyperpolymath/echidna/compare/v1.5.0...v1.6.0
[1.5.0]: https://github.com/hyperpolymath/echidna/compare/v1.0.0...v1.5.0
[1.0.0]: https://github.com/hyperpolymath/echidna/releases/tag/v1.0.0
