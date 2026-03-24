<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- LLM warmup context — USER level (<200 lines) -->
<!-- Feed this to an LLM before asking questions about ECHIDNA -->

# ECHIDNA — User Context

## What it is

ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance)
is a trust-hardened neurosymbolic theorem proving platform with 48 prover backends.

It accepts proof obligations, dispatches them to the best-fit prover, verifies
the result through a trust pipeline, and returns confidence-scored theorems.

## Architecture overview

```
CLI / REPL / REST / GraphQL / gRPC
        |
  Rust core (dispatch + trust pipeline)
        |
  48 prover backends (SMT, ITP, ATP, constraint)
        |
  Trust verification: integrity → portfolio → certificates → axioms → confidence
        |
  Julia ML (tactic prediction, premise selection)
```

## Prover categories (48 total)

| Category | Examples |
|----------|---------|
| Interactive proof assistants | Coq, Lean 4, Isabelle, Agda, Idris2, F* |
| SMT solvers | Z3, CVC5, Alt-Ergo |
| First-order ATPs | Vampire, E Prover, SPASS |
| Auto-active verifiers | Dafny, Why3 |
| Specialised | Metamath, HOL Light, Mizar, PVS, ACL2, TLAPS |
| Constraint solvers | GLPK, SCIP, MiniZinc, OR-Tools |

## Key files

| Path | Purpose |
|------|---------|
| `src/rust/main.rs` | CLI entry point |
| `src/rust/repl.rs` | Interactive REPL |
| `src/rust/server.rs` | HTTP API server |
| `src/rust/provers/` | 30 prover backend implementations |
| `src/rust/verification/` | Trust pipeline |
| `src/rust/dispatch.rs` | Full dispatch pipeline |
| `src/interfaces/` | GraphQL + gRPC + REST APIs |
| `src/julia/` | ML tactic prediction |
| `Cargo.toml` | Rust workspace root |

## Quick commands

```bash
just build          # Build debug binary
just test           # Run 232 unit tests
just test-all       # Run all 389 tests
just run repl       # Interactive theorem prover
just run serve      # Start REST API (port 8000)
just doctor         # Check prerequisites
```

Prerequisites: Rust (nightly), just, pkg-config, openssl-devel.

## Trust pipeline

Every proof goes through:

1. **Integrity** — Solver binary hash verification (SHAKE3-512 + BLAKE3)
2. **Portfolio** — Cross-check with multiple solvers
3. **Certificates** — Verify proof certificates (Alethe, DRAT/LRAT, TSTP)
4. **Axioms** — Track axiom usage (4 danger levels)
5. **Confidence** — Bayesian confidence scoring (5-level hierarchy)
6. **Mutation** — Mutation testing for specifications
7. **Exchange** — Cross-prover proof exchange (OpenTheory, Dedukti)

## Sandboxed execution

Provers run in sandboxes:
- **Podman** — Full container isolation
- **bubblewrap** — Lightweight namespace isolation
- **none** — Direct execution (trusted provers only)

## API endpoints

| Interface | Port | Tech |
|-----------|------|------|
| REST | 8000 | axum + OpenAPI |
| GraphQL | 8081 | async-graphql |
| gRPC | 50051 | tonic |

## Container images

```bash
just container-build       # Minimal (Z3, CVC5, Lean, Idris2)
just container-build-full  # All provers + Julia ML
```

## License

PMPL-1.0-or-later. Author: Jonathan D.A. Jewell.

## Ecosystem position

- **Depends on**: proven (verified safety), Z3/CVC5/Lean/etc. (solver binaries)
- **Used by**: hypatia (CI/CD intelligence), ecosystem-wide proof checking
- **Siblings**: panic-attacker (scanning), verisimdb (data layer)
