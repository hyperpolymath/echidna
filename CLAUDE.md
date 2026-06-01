# CLAUDE.md

Guidelines and context for working with Claude Code on the ECHIDNA project.

## Project Overview

**ECHIDNA** (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a trust-hardened neurosymbolic theorem-proving platform with a polyglot backend surface and a comprehensive verification pipeline.

- **Repository**: https://github.com/hyperpolymath/echidna
- **Version + release history**: [`CHANGELOG.md`](CHANGELOG.md) (single source of truth; do not duplicate version strings elsewhere)
- **License**: MPL-2.0
- **Architecture overview**: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
- **Canonical prover count + tier table**: [`docs/PROVER_COUNT.md`](docs/PROVER_COUNT.md)
- **Environment variables**: [`docs/ENV-VARS.md`](docs/ENV-VARS.md)
- **RSR / CCCP compliance statement**: [`RSR_COMPLIANCE.adoc`](RSR_COMPLIANCE.adoc)
- **Receipts for README claims**: [`EXPLAINME.adoc`](EXPLAINME.adoc)
- **Contributor guide**: [`CONTRIBUTING.adoc`](CONTRIBUTING.adoc)

## Repository Structure

```
echidna/
├── src/
│   ├── rust/               # Rust core + ProverKind enum + ProverFactory
│   │   ├── provers/        # Per-backend ProverBackend impls (see docs/PROVER_COUNT.md for the tier table)
│   │   ├── verification/   # Trust pipeline (portfolio, certificates, axioms, confidence, mutation, pareto, statistics)
│   │   ├── integrity/      # Solver binary integrity (SHAKE3-512, BLAKE3)
│   │   ├── executor/       # Sandboxed solver execution (Podman, bubblewrap)
│   │   ├── exchange/       # Cross-prover proof exchange (OpenTheory, Dedukti)
│   │   ├── dispatch.rs     # Full trust-hardening dispatch pipeline
│   │   ├── agent/          # Agentic proof search (actor model)
│   │   ├── gnn/            # GNN integration (graph construction, embeddings, client, guided search)
│   │   ├── neural.rs       # Neural premise selection (text-based, complements GNN)
│   │   ├── aspect.rs       # Aspect tagging
│   │   ├── core.rs         # Core types (Term, ProofState, Tactic, Goal)
│   │   ├── parsers/        # Proof file parsers
│   │   ├── ffi/            # Foreign function interface
│   │   ├── server.rs       # HTTP API server
│   │   ├── repl.rs         # Interactive REPL
│   │   ├── main.rs         # CLI entry point
│   │   └── lib.rs          # Library root
│   ├── interfaces/         # API interfaces (workspace members)
│   │   ├── graphql/        # GraphQL (async-graphql, port 8081)
│   │   ├── grpc/           # gRPC (tonic, port 50051)
│   │   └── rest/           # REST (axum + OpenAPI, port 8000)
│   ├── abi/                # Idris2 formal ABI (EchidnaABI.TacticRecord, …)
│   ├── chapel/             # Optional parallel proof dispatch (--features chapel)
│   ├── julia/              # Julia ML components
│   ├── rescript/, src/ui/  # UI — ReScript → AffineScript-TEA migration in flight
│   └── zig_ffi/, ffi/zig/  # Zig FFI bridge (C-ABI surface for backends)
├── .machine_readable/      # A2ML metadata, contractiles (MUST/ADJUST/TRUST/INTENT)
├── .github/workflows/      # CI/CD workflows
├── .containerization/      # Per-prover image tree (Containerfile.wave3)
├── Cargo.toml              # Rust workspace root
├── Justfile                # Primary build system (RSR-H14)
└── Containerfile           # Podman container (RSR-H15; do not use Dockerfile)
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

- **Rust**: Core logic, prover backends, trust pipeline, CLI, REPL, API servers
- **Julia**: ML inference (tactic prediction, premise selection)
- **Idris2**: Formal ABI specifications + totality proofs (`src/abi/`); zero `believe_me`, zero postulates, zero admits, enforced by `idris2-abi-ci.yml`
- **Zig**: C-ABI FFI bridge (`ffi/zig/`, `src/zig_ffi/`)
- **Chapel**: Optional parallel proof dispatch (`--features chapel`)
- **AffineScript + Deno** (canonical UI target; ReScript components are being ported)

### Prover Support

Backend tiers, member lists, and the canonical answer to "how many provers?" all live in [`docs/PROVER_COUNT.md`](docs/PROVER_COUNT.md). The Tier-1 _core_ set is exposed by default through `GET /api/provers`; the rest are reachable via `ProverKind` and the dispatch pipeline. Do not duplicate counts in this file — they drift.

### Trust & Safety Pipeline

The trust-hardening pipeline applies the following checks before any proof result leaves the dispatcher:

1. Solver binary integrity verification (SHAKE3-512 + BLAKE3)
2. SMT portfolio solving / cross-checking
3. Proof certificate checking (Alethe, DRAT/LRAT, TSTP, Lean4 kernel, Coq kernel)
4. Axiom usage tracking (4 danger levels: Safe, Noted, Warning, Reject)
5. Solver sandboxing (Podman, bubblewrap, unsandboxed-with-explicit-opt-in)
6. 5-level trust hierarchy for confidence scoring
7. Mutation testing for specifications
8. Prover dispatch pipeline
9. Cross-prover proof exchange (OpenTheory, Dedukti)
10. Pareto frontier computation for multi-objective proof search
11. Statistical confidence tracking with Bayesian timeout estimation

### Key Components

- `src/rust/provers/mod.rs`: `ProverBackend` trait, `ProverKind` enum, `ProverFactory`
- `src/rust/dispatch.rs`: Full trust-hardening dispatch pipeline
- `src/rust/verification/`: Portfolio, certificates, axiom tracker, confidence, mutation, pareto, statistics
- `src/rust/integrity/`: Solver binary integrity (SHAKE3-512, BLAKE3)
- `src/rust/executor/`: Sandboxed solver execution
- `src/rust/exchange/`: OpenTheory, Dedukti proof exchange
- `src/rust/core.rs`: Core types (Term, ProofState, Tactic, Goal, Context, Theorem)
- `src/rust/gnn/`: GNN integration (graph construction, embeddings, inference client, guided search)
- `src/rust/agent/`: Agentic proof search (actor model)
- `src/abi/EchidnaABI/`: Idris2 ABI specifications + totality proofs (TacticRecord, AxiomTracker, Gnn, Provers, CapnSchemas)

### Current Status

The authoritative status surface is [`CHANGELOG.md`](CHANGELOG.md) (released versions) plus the git log + open issues (in-flight work). Do not duplicate version-keyed status here — it drifts.

Shape, by area:

- **Trust pipeline**: solver integrity, certificate checking, axiom tracking, sandboxing, mutation testing, Pareto ranking, Bayesian confidence — wired into `dispatch.rs`.
- **Idris2 ABI**: `EchidnaABI.TacticRecord` (fixed-point confidence, total-order proofs, in-range round-trip lemmas) + sibling modules; type-checked on every push by `idris2-abi-ci.yml`.
- **GNN integration**: graph construction (7 node kinds, 8 edge kinds), 32-dim local term embeddings, GNN inference client, hybrid GNN + symbolic scoring, Julia `/gnn/rank` with cosine fallback.
- **Chapel parallel layer (`--features chapel`)**: `ChapelParallelSearch` invoked by `dispatch.rs::verify_proof_parallel`; per-prover cwd/filename hooks in `tryProver`; L2.3 cancel-token preemption shipped; `parallelProofSearchSpeculative` (first-success-wins atomic-CAS) alongside best-of `parallelProofSearch`; `proofs/agda/ParallelSoundness.agda` formalises soundness, completeness, and cancellation-safety with zero postulate / admit / believe_me. L2.4+ (mutation parallelism, multi-locale, numeric hot paths, bench) gated on L1 Cap'n Proto and (for L2.5) a cluster runtime — see [`docs/handover/TODO.md`](docs/handover/TODO.md).
- **Wave-3 container infrastructure**: per-prover images in `.containerization/Containerfile.wave3`; weekly cron in `container-ci.yml` runs stub-sentinel detection across all 8 Tier-3 cells.
- **Julia ML layer**: logistic-regression tactic prediction shipped; Flux.jl scaffolds for GNN/Transformer training present but not yet trained on real data — corpus ready under `training_data/`.
- **Migrations in flight**: ReScript → AffineScript-TEA (UI); npm → Deno (`echidna-playground`); CI workflow consolidation under the governance ruleset.

## Useful Commands

```bash
# Build System (Justfile is PRIMARY — RSR-H14)
just build              # Build the project
just test               # Run tests
just check              # Run all quality checkers
just doctor             # Verify toolchain
just heal               # Auto-install missing tools
just tour               # Codebase tour

# Cargo
cargo build             # Build Rust code
cargo test              # Run all tests
cargo test --lib        # Unit tests only
cargo test --tests      # Integration suites
cargo bench             # Criterion benchmarks
cargo clippy            # Rust lints
cargo fmt --check       # Format check

# Idris2 ABI
idris2 --build src/abi/echidnaabi.ipkg   # Type-check the ABI package

# Container Management (Podman, not Docker — RSR-H15)
podman build -f Containerfile .          # Minimal image
podman run echidna                        # Run minimal image
# Per-prover images live under .containerization/Containerfile.wave3
```

## Critical Constraints

- **No Python** outside `salt/` (RSR-H4) — Julia for ML, Rust for systems, AffineScript/ReScript for UI.
- **RSR / CCCP compliance** — see [`RSR_COMPLIANCE.adoc`](RSR_COMPLIANCE.adoc) for the full hard-rule list and out-of-template adaptations.
- **Justfile primary** (RSR-H14) — Just is the build entry point; no Make.
- **Podman not Docker** (RSR-H15) — always Podman; `Containerfile` (not `Dockerfile`); `.containerization/Containerfile.wave3` for per-prover images.
- **License**: MPL-2.0 across the documentation surface (intentional doc stance; see [`feedback_echidna_license_docs_mpl_intentional`](https://github.com/hyperpolymath/echidna/issues?q=license) — historical drift on individual files is owner-managed and not reconciled in routine PRs).
- **Author**: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>.

---

**Maintained by**: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>.
This file is kept count-free and date-free in prose; CHANGELOG.md and the git log carry the live timeline.
