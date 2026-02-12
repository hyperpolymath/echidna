# Changelog

All notable changes to ECHIDNA will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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

[1.5.0]: https://github.com/hyperpolymath/echidna/compare/v1.0.0...v1.5.0
[1.0.0]: https://github.com/hyperpolymath/echidna/releases/tag/v1.0.0
