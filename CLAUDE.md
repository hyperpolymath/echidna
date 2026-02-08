# CLAUDE.md

This document provides guidelines and context for working with Claude Code on the ECHIDNA project.

## Project Overview

**ECHIDNA** (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a trust-hardened neurosymbolic theorem proving platform supporting 30 prover backends with a comprehensive verification pipeline.

**Repository**: https://github.com/hyperpolymath/echidna
**Version**: 1.5.0
**License**: PMPL-1.0-or-later

## Repository Structure

```
echidna/
├── src/
│   ├── rust/               # Rust core (30 provers, trust pipeline)
│   │   ├── provers/        # 30 prover backend implementations
│   │   ├── verification/   # Trust pipeline (portfolio, certificates, axioms, confidence, mutation, pareto, statistics)
│   │   ├── integrity/      # Solver binary integrity (SHAKE3-512, BLAKE3)
│   │   ├── executor/       # Sandboxed solver execution (Podman, bubblewrap)
│   │   ├── exchange/       # Cross-prover proof exchange (OpenTheory, Dedukti)
│   │   ├── dispatch.rs     # Full trust-hardening dispatch pipeline
│   │   ├── agent/          # Agentic proof search (actor model)
│   │   ├── neural.rs       # Neural premise selection
│   │   ├── aspect.rs       # Aspect tagging
│   │   ├── core.rs         # Core types (Term, ProofState, Tactic, Goal)
│   │   ├── parsers/        # Proof file parsers
│   │   ├── ffi/            # Foreign function interface
│   │   ├── server.rs       # HTTP API server
│   │   ├── repl.rs         # Interactive REPL
│   │   ├── main.rs         # CLI entry point
│   │   └── lib.rs          # Library root
│   ├── interfaces/         # API interfaces (workspace members)
│   │   ├── graphql/        # GraphQL (async-graphql, port 8080)
│   │   ├── grpc/           # gRPC (tonic, port 50051)
│   │   └── rest/           # REST (axum + OpenAPI, port 8000)
│   ├── julia/              # Julia ML components
│   ├── rescript/           # ReScript+Deno UI (28 files)
│   └── mercury/            # Mercury/Logtalk logic (optional)
├── .machine_readable/      # SCM files (STATE.scm, META.scm, ECOSYSTEM.scm)
├── .github/workflows/      # 17 CI/CD workflows
├── Cargo.toml              # Rust workspace root
├── Justfile                # Primary build system
└── Containerfile           # Podman container
```

## Working with Claude Code

### General Guidelines

1. **Code Quality**: Maintain high code quality standards with proper error handling, tests, and documentation
2. **Git Workflow**: Follow conventional commit messages and keep commits atomic
3. **Security**: Be vigilant about security vulnerabilities
4. **Dependencies**: Document all dependencies and their purposes

### Commit Message Format

Follow conventional commit format:
- `feat:` - New features
- `fix:` - Bug fixes
- `docs:` - Documentation changes
- `refactor:` - Code refactoring
- `test:` - Adding or updating tests
- `chore:` - Maintenance tasks

## Project-Specific Context

### Tech Stack

- **Rust**: Core logic, 30 prover backends, trust pipeline, CLI, REPL, API servers
- **Julia**: ML inference (tactic prediction, premise selection, port 8090)
- **ReScript + Deno**: UI components (28 files)
- **Chapel**: Optional parallel proof dispatch

### Prover Support (30 Total - ALL IMPLEMENTED)

- **Interactive Proof Assistants**: Agda, Coq/Rocq, Lean 4, Isabelle/HOL, Idris2, F*
- **SMT Solvers**: Z3, CVC5, Alt-Ergo
- **Auto-Active Verifiers**: Dafny, Why3
- **Specialised**: Metamath, HOL Light, Mizar, HOL4, PVS, ACL2, TLAPS, Twelf, Nuprl, Minlog, Imandra
- **First-Order ATPs**: Vampire, E Prover, SPASS
- **Constraint Solvers**: GLPK, SCIP, MiniZinc, Chuffed, OR-Tools

### Trust & Safety Pipeline

The v1.5 trust hardening added:
1. Solver binary integrity verification (SHAKE3-512 + BLAKE3)
2. SMT portfolio solving / cross-checking
3. Proof certificate checking (Alethe, DRAT/LRAT, TSTP)
4. Axiom usage tracking (4 danger levels: Safe, Noted, Warning, Reject)
5. Solver sandboxing (Podman, bubblewrap, none)
6. 5-level trust hierarchy for confidence scoring
7. Mutation testing for specifications
8. Prover dispatch pipeline
9. Cross-prover proof exchange (OpenTheory, Dedukti)
10. Pareto frontier computation for multi-objective proof search
11. Statistical confidence tracking with Bayesian timeout estimation

### Key Components

- `src/rust/provers/mod.rs`: ProverBackend trait, ProverKind enum (30 variants), ProverFactory
- `src/rust/dispatch.rs`: Full trust-hardening dispatch pipeline
- `src/rust/verification/`: Portfolio, certificates, axiom tracker, confidence, mutation, pareto, statistics
- `src/rust/integrity/`: Solver binary integrity (SHAKE3-512, BLAKE3)
- `src/rust/executor/`: Sandboxed solver execution
- `src/rust/exchange/`: OpenTheory, Dedukti proof exchange
- `src/rust/core.rs`: Core types (Term, ProofState, Tactic, Goal, Context, Theorem)
- `src/rust/agent/`: Agentic proof search (actor model)

### Current Status

**Completed (v1.5.0)**:
- 30/30 prover backends
- Trust & safety hardening (13 tasks complete)
- 306+ tests (232 unit, 38 integration, 21 property-based)
- 3 API interfaces (GraphQL, gRPC, REST)
- Julia ML layer (logistic regression)
- ReScript UI (28 files)
- 17 CI/CD workflows

**Next (v2.0)**:
- FFI/IPC bridge (API interfaces to Rust prover backends)
- Deep learning models (Transformers via Flux.jl)
- Tamarin/ProVerif bridge

## Useful Commands

```bash
# Build System (Justfile is PRIMARY)
just build              # Build the project
just test               # Run tests (306+)
just check              # Run all quality checkers

# Cargo commands
cargo build             # Build Rust code
cargo test              # Run all tests
cargo test --lib        # Unit tests only (232)
cargo test --test integration_tests  # Integration tests (38)

# Container Management (Podman, not Docker)
podman build -f Containerfile .   # Build container
podman run echidna                # Run container

# Quality Checks
cargo clippy                      # Rust lints
cargo fmt --check                 # Format check
```

## Critical Constraints

- **NO PYTHON** - use Julia for ML/data, Rust for systems, ReScript for apps
- **RSR/CCCP Compliance Required** - follow Rhodium Standard Repository guidelines
- **Justfile PRIMARY** - never use Make or other build systems
- **Podman not Docker** - always use Podman for containers
- **License**: PMPL-1.0-or-later (not AGPL, not dual MIT/Palimpsest)
- **Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>

---

**Last Updated**: 2026-02-08
**Maintained By**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
