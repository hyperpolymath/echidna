[![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-pink?logo=github)](https://github.com/sponsors/hyperpolymath)

// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

= ECHIDNA

image:https://img.shields.io/badge/OpenSSF-Best_Practices-green?logo=opensourcesecurity[OpenSSF Best Practices,link="https://www.bestpractices.dev/en/projects/new?repo_url=https://github.com/hyperpolymath/echidna"]
image:https://img.shields.io/badge/License-PMPL--1.0-blue.svg[License: PMPL-1.0,link="https://github.com/hyperpolymath/palimpsest-license"]
image:https://img.shields.io/badge/Provers-12_core_/_79_advertised-green.svg[Provers: 12 core / 79 advertised]
image:https://img.shields.io/badge/Tests-1059-brightgreen.svg[Tests: 1059]
image:https://api.thegreenwebfoundation.org/greencheckimage/nesy-prover.dev[Green Hosting,link="https://www.thegreenwebfoundation.org/green-web-check/?url=nesy-prover.dev"]

*E*xtensible *C*ognitive *H*ybrid *I*ntelligence for *D*eductive *N*eural *A*ssistance

A neurosymbolic theorem proving platform with a trust-hardened
verification pipeline, multi-objective proof search, and 100+ prover
backend implementations.

== Prover Surface

ECHIDNA's `ProverKind` enum has 141 variants and the repository ships
102 backend implementation files. The advertised roster
(`ProverKind::all()`) is 79 backends. The REST API
(`GET /api/provers`) exposes the 12-prover **core** set
(`ProverKind::all_core()`) by default. See
link:docs/SUPPORTED_PROVERS.md[`docs/SUPPORTED_PROVERS.md`] for the
core list, required external binaries, and how to surface additional
backends through the API.

== Distinguishing Features

* **Trust-hardened pipeline** — every proof passes through solver
  integrity verification, axiom tracking, certificate checking, and
  Bayesian confidence scoring before the result is returned.
* **Cross-prover arbitration** — mathematical object identity resolution
  across heterogeneous prover backends.
* **Neurosymbolic architecture** — Julia ML layer suggests tactics;
  formal provers always have the final word.
* **OpenTheory + Dedukti integration** — universal proof exchange.
* **Axiom-usage tracking** — four danger levels (Safe, Noted, Warning,
  Reject) applied uniformly across every backend.

== Overview

ECHIDNA orchestrates theorem provers, SMT solvers, first-order ATPs,
and constraint solvers through a unified Rust core. Every proof result passes
through a trust-hardening pipeline that checks solver integrity, tracks axiom
usage, verifies proof certificates, and assigns a 5-level confidence score.

Neural premise selection (via Julia) suggests tactics, but formal provers
always have the final word. ECHIDNA never produces unsound proofs.

== Features

=== Prover Backends

The 12-prover **core** set exposed via `GET /api/provers`:

* *Interactive proof assistants*: Agda, Coq, Lean 4, Isabelle/HOL,
  HOL Light, HOL4, Mizar, PVS, ACL2
* *SMT solvers*: Z3, CVC5
* *Pure-Rust in-process*: Metamath (no external binary needed)

`ProverKind::all()` advertises a further 67 backends including
interactive provers (Idris2, Lean3, F\*, Rocq), first-order ATPs
(Vampire, E Prover, SPASS, iProver, Prover9, Zipperposition),
SAT/SMT (CaDiCaL, Kissat, MiniSat, OpenSMT, SmtRat, AltErgo, dReal,
Princess), auto-active verifiers (Dafny, Why3, F\*, Cameleer, Liquid
Haskell, GNATprove, Stainless), constraint/optimisation (GLPK, SCIP,
MiniZinc, Chuffed, OR-Tools), model checkers (SPIN, NuSMV, TLC, Alloy,
Prism, UPPAAL, Storm, ProB), C/hardware verifiers (CBMC, SeaHorn,
Frama-C, ABC, Viper, KeY, GPUVerify, Faial), security protocol tools
(Tamarin, ProVerif, EasyCrypt, CryptoVerif), and specialised systems
(TLAPS, Twelf, Nuprl, Minlog, Imandra, KeYmaeraX, MetiTarski, Cubical
Agda, MizAR, Dedukti, Boogie, Athena, Naproche, Matita, Arend, Mercury,
λProlog, Nitpick, Nunchaku, Leo III, Satallax, Lash, agsyHOL, mleanCoP,
ileanCoP, NanoCoP, MetTeL2, ELK, Konclude, TypedWasm, UPPAAL Stratego).

All advertised backends implement the `ProverBackend` trait: parse,
verify, export, tactic suggestion, and theorem search. File extension
detection covers 30+ formats (`.v`, `.lean`, `.smt2`, `.tptp`, `.dfy`,
`.mzn`, etc.).

=== Trust & Safety Hardening (v1.5)

The verification pipeline applies the following checks to every proof:

* *Solver Binary Integrity* (`integrity/`): SHAKE3-512 provenance hashing and
  BLAKE3 fast runtime re-verification. Solver binaries are checked against a
  TOML manifest at startup; tampered binaries are rejected.

* *SMT Portfolio Solving* (`verification/portfolio.rs`): Cross-checks proofs
  across multiple solvers (e.g. Z3 + CVC5 + Alt-Ergo). Flags disagreements
  for human review. Supports SMT, ATP, and ITP solver pools.

* *Proof Certificate Checking* (`verification/certificates.rs`): Verifies
  Alethe (CVC5), DRAT/LRAT (SAT solvers), TSTP (first-order ATPs), Lean4
  kernel, and Coq kernel certificate formats. Certificates are hashed with
  BLAKE3 and stored for audit trails.

* *Axiom Usage Tracking* (`verification/axiom_tracker.rs`): Scans proof
  content for dangerous constructs across provers. Four danger levels:
  - *Safe*: Standard library axioms
  - *Noted*: Classical axioms in constructive systems (e.g. `Axiom` in Coq)
  - *Warning*: Incomplete proof markers (`sorry`, `Admitted`, `postulate`)
  - *Reject*: Known unsound constructs (`--type-in-type`, `mk_thm`,
    `believe_me`)
  Comments are not flagged.

* *Solver Sandboxing* (`executor/sandbox.rs`): Runs solvers in isolated
  environments. Three modes: Podman containers (preferred, `--network=none`,
  read-only, memory/CPU/disk limits), bubblewrap namespaces (fallback), or
  unsandboxed (development only, requires explicit opt-in). Auto-detection
  selects the strongest available option.

* *5-Level Trust Hierarchy* (`verification/confidence.rs`): Every proof result
  receives a trust level:
  - Level 1: Large-TCB system, unchecked, or dangerous axioms used
  - Level 2: Single prover, no dangerous axioms
  - Level 3: Single prover with verified proof certificate
  - Level 4: Small-kernel prover (Lean, Coq, Isabelle, Agda, Metamath,
    HOL Light, HOL4, Idris2, F*, Twelf, Nuprl, Minlog) with verified
    certificate
  - Level 5: Cross-checked by 2+ independent small-kernel systems with
    certificates

* *Mutation Testing* (`verification/mutation.rs`): Deliberately weakens
  specifications (remove preconditions, weaken postconditions, negate
  subterms, replace constants) to verify the pipeline catches them. Computes
  a mutation score with a default 95% threshold.

* *Cross-Prover Proof Exchange* (`exchange/`): Export and import proofs in
  universal formats: OpenTheory (HOL family interop) and Dedukti/Lambdapi
  (universal proof kernel based on lambda-Pi calculus modulo rewriting).

* *Pareto Optimisation* (`verification/pareto.rs`): Multi-objective ranking
  of proof candidates across four axes: proof time, trust level, memory
  usage, and proof size. Computes the Pareto frontier and optionally applies
  weighted scoring for single-best selection.

* *Statistical Confidence Tracking* (`verification/statistics.rs`):
  Per-prover, per-domain success rates and timing statistics. Bayesian timeout
  estimation (mean + 2 sigma). Wilson score intervals for mutation score
  confidence. Prover ranking by composite score (success rate, timeout rate,
  speed). JSON serialisation for persistence.

* *Dispatch Pipeline* (`dispatch.rs`): Orchestrates the full pipeline:
  create prover -> parse -> verify -> axiom scan -> confidence scoring.
  Supports single-prover and cross-checked (portfolio) modes with configurable
  minimum trust levels.

=== Additional Capabilities

* *Neurosymbolic ML* (Julia layer): Logistic regression tactic prediction
  trained on 332 proofs / 1,603 tactics. Serves predictions via HTTP (port 8090).
* *Aspect Tagging*: Intelligent proof categorisation and domain analysis
* *Anomaly Detection*: ML-based overconfidence detection
* *Agentic Proof Search*: Actor-based autonomous proof exploration
* *Chapel Parallel Layer* (optional): Coforall-based parallel proof dispatch
* *3 API Interfaces*:
  - GraphQL (async-graphql, port 8081)
  - gRPC (tonic + Protocol Buffers, port 50051)
  - REST (axum + OpenAPI/Swagger, port 8000)
* *ReScript UI*: 33 compiled components for proof exploration (zero TypeScript)
* *REPL*: Interactive proof session via rustyline

== Quick Start

=== Prerequisites

* *Rust* nightly (managed via asdf)
* *Julia* 1.10+ (for ML layer)
* *Deno* (for ReScript UI)
* *Podman* (NOT Docker) -- recommended for solver sandboxing
* *Just* command runner

=== Build and Test

[source,bash]
----
# Clone
git clone https://github.com/hyperpolymath/echidna.git
cd echidna

# Build
just build
# or: cargo build

# Run all tests (1059 passing on default build)
just test
# or: cargo test

# Run ECHIDNA REPL
just run
----

=== Prove your first goal

[source,bash]
----
# Install at least one solver — Z3 is the smallest dependency
sudo apt install z3        # Debian/Ubuntu (or `brew install z3`)

# Start the REST API server with CORS enabled
cargo run --bin echidna -- server --cors

# In another terminal, POST a satisfiable SMT-LIB goal
curl -X POST http://127.0.0.1:8081/api/prove \
  -H 'Content-Type: application/json' \
  -d '{"prover":"Z3",
       "content":"(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
       "timeout":30}'
# → {"success":true,"goals":1,"message":"Proof verified successfully"}
----

For a minimal browser UI, open `src/ui/public/prove.html` directly in
any modern browser and point the "API base" field at the running
server. No build step is required.

See link:docs/SUPPORTED_PROVERS.md[`docs/SUPPORTED_PROVERS.md`] for the
12-prover core set, required binaries, and how to expose additional
backends through the API.

=== Using Podman Container

[source,bash]
----
podman build -f Containerfile -t echidna:latest .
podman run -it echidna:latest
----

== Architecture

=== Technology Stack

* *Rust*: Core logic, prover backends, trust pipeline, CLI, REPL, API servers
* *Julia*: ML inference (tactic prediction, premise selection)
* *ReScript + Deno*: UI components
* *Chapel*: Optional parallel proof dispatch

=== Key Modules

[source]
----
src/rust/
  provers/          # 102 prover backend implementation files (ProverBackend trait)
  verification/     # Trust-hardening subsystem
    portfolio.rs    # SMT portfolio solving / cross-checking
    certificates.rs # Proof certificate checking (Alethe, DRAT/LRAT, TSTP)
    axiom_tracker.rs# Axiom usage scanning and policy enforcement
    confidence.rs   # 5-level trust hierarchy
    mutation.rs     # Mutation testing for specifications
    pareto.rs       # Pareto frontier computation
    statistics.rs   # Per-prover statistical tracking
  integrity/        # Solver binary integrity (SHAKE3-512, BLAKE3)
  executor/         # Sandboxed solver execution (Podman, bubblewrap)
  exchange/         # Cross-prover proof exchange (OpenTheory, Dedukti)
  dispatch.rs       # Full trust-hardening dispatch pipeline
  agent/            # Agentic proof search (actor model)
  neural.rs         # Neural premise selection integration
  aspect.rs         # Aspect tagging system
  anomaly_detection.rs
  proof_search.rs   # Chapel parallel proof search
  core.rs           # Core types (Term, ProofState, Tactic, Goal, etc.)
  parsers/          # Proof file parsers
  ffi/              # Foreign function interface
  server.rs         # HTTP API server
  repl.rs           # Interactive REPL
  main.rs           # CLI entry point
  lib.rs            # Library root
----

=== API Usage

[source,rust]
----
use echidna::provers::{ProverFactory, ProverKind, ProverConfig};

// Create a prover backend
let backend = ProverFactory::create(ProverKind::Lean, ProverConfig::default())?;
let state = backend.parse_string("theorem foo : 1 + 1 = 2 := by omega").await?;
let verified = backend.verify_proof(&state).await?;
----

[source,rust]
----
use echidna::dispatch::{ProverDispatcher, DispatchConfig};
use echidna::provers::ProverKind;

// Use the trust-hardening dispatch pipeline
let dispatcher = ProverDispatcher::with_config(DispatchConfig {
    cross_check: true,
    track_axioms: true,
    ..Default::default()
});

// Cross-checked verification
let result = dispatcher.verify_proof_cross_checked(
    ProverKind::Z3,
    "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)",
    &[ProverKind::CVC5],
).await?;

println!("Verified: {}, Trust: {}", result.verified, result.trust_level);
----

== Test Suite

1059 library tests passing on the default build
(`cargo test --lib`, 2 ignored). The `--features verisim` build adds
further integration tests for the VeriSim bridge.

* Smoke E2E integration tests across the core prover backends
* Property-based tests (PropTest)
* Criterion benchmarks across all critical paths

[source,bash]
----
cargo test              # Run all tests
cargo test --lib        # Unit tests only
cargo test --test integration_tests
----

== Development

=== Quality Checks

[source,bash]
----
just check      # All quality checks
just lint       # REUSE, rustfmt, clippy
just security   # Trivy, cargo-audit
just coverage   # Test coverage
just mvp        # MVP smoke checks (reports missing provers, non-fatal)
----

== Current Status

*v1.5.0 -- Trust & Safety Hardening Complete*

[cols="1,3", options="header"]
|===
| Area | Status

| Prover backends | 30/30 operational
| Trust pipeline | All 13 tasks complete
| Unit tests | 232 passing
| Integration tests | 38 passing
| Property tests | 21 passing (PropTest)
| API interfaces | GraphQL, gRPC, REST
| ML layer | Julia logistic regression
| UI | ReScript, 33 components
| CI/CD | 17 workflows
|===

*Completed in v2.2 (epistemic hardening)*:

* Typed `ProverOutcome` taxonomy — 8 mutually-exclusive statuses replacing `Result<bool>`
* Z3 `check()` override: inconsistency pre-check before trivial-goal short-circuit
* Z3 output parsing uses last non-empty line (not whole-output `contains()`)
* Z3 goal-set inconsistency detection (goals cannot all hold simultaneously)
* Why3 timeout bug fixed (+5s undocumented slack removed)
* Pre-colleague sanity suite: 37 tests covering full taxonomy with Z3 integration
* `/api/verify` REST endpoint now returns typed `outcome` field alongside `valid: bool`
* echidnabot `ProofStatus` extended to full 8-variant taxonomy, backward compatible

*Roadmap — v2.3 (single-session Z3)*:

* Replace two-process inconsistency check with single Z3 session using `(push)/(pop)` —
  atomic, halves subprocess overhead
* `check_raw_smt()` trait method for backends that accept pre-built content directly
  (bypasses lossy `parse_string()` round-trip)

*Roadmap — v2.4 (typed override coverage)*:

Priority backends for typed `check()` overrides (currently use heuristic fallback):
CVC5, Lean 4, Coq/Rocq, Isabelle. Each adds accurate `INCONSISTENT_PREMISES` and
`UNSUPPORTED_FEATURE` detection for that backend.

*Planned for v3.0*:

* Deep learning models (Transformers via Flux.jl)
* Production deployment configuration
* Tamarin/ProVerif bridge for cipherbot

== Documentation

* link:CONTRIBUTING.md[Contributing Guidelines]
* link:CODE_OF_CONDUCT.md[Code of Conduct]
* link:SECURITY.md[Security Policy]
* link:CHANGELOG.adoc[Changelog]
* link:ROADMAP.adoc[Roadmap]

== Critical Constraints

* *NO PYTHON* -- Julia for ML, Rust for systems, ReScript for UI
* *RSR/CCCP Compliance* -- Rhodium Standard Repository guidelines
* *Justfile PRIMARY* -- Use Just, not Make
* *Podman not Docker* -- Always Podman
* *License*: MPL-2.0

== License

This project is licensed under the link:LICENSE[Palimpsest Meta-Project License (MPL-2.0)].

== Citation

[source,bibtex]
----
@software{echidna2026,
  title = {ECHIDNA: Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance},
  author = {Jewell, Jonathan D.A.},
  year = {2026},
  url = {https://github.com/hyperpolymath/echidna},
  license = {MPL-2.0}
}
----

== Contact

* *GitHub Issues*: https://github.com/hyperpolymath/echidna/issues
* *Pull Requests*: https://github.com/hyperpolymath/echidna/pulls

---

*Version*: 1.5.0 +
*Status*: Trust & Safety Hardening Complete +
*Author*: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> +
*Last Updated*: 2026-02-08
