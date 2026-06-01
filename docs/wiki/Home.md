# ECHIDNA Wiki

**ECHIDNA** — Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance — is a trust-hardened neurosymbolic theorem-proving platform supporting **128 prover backends** (12 core, exposed by default API; see [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md) for the tier breakdown).

**License**: MPL-2.0 (documentation surface) · authoritative version pinned in [`Cargo.toml`](https://github.com/hyperpolymath/echidna/blob/main/Cargo.toml) and [`CHANGELOG.md`](https://github.com/hyperpolymath/echidna/blob/main/CHANGELOG.md)

## Quick navigation

- [Getting Started](Getting-Started) — install, build, first proof
- [Architecture](Architecture) — components, trust pipeline, polyglot layout
- [Guides](Guides) — adding provers, API usage, ML training
- [FAQ](FAQ) — common questions
- [Troubleshooting](Troubleshooting) — build issues, prover failures

## Canonical in-repo documents

When the wiki and the repo disagree, **the repo wins**:

- [`README.adoc`](https://github.com/hyperpolymath/echidna/blob/main/README.adoc) — primary project README
- [`CLAUDE.md`](https://github.com/hyperpolymath/echidna/blob/main/CLAUDE.md) — codebase orientation
- [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md) — current architecture
- [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md) — tier table
- [`docs/ENV-VARS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ENV-VARS.md) — environment variables
- [`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) — stage map and sprint targets
- [`docs/handover/HANDOVER-INDEX.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/HANDOVER-INDEX.md) — handover/ navigation
- [`RSR_COMPLIANCE.adoc`](https://github.com/hyperpolymath/echidna/blob/main/RSR_COMPLIANCE.adoc) — RSR / CCCP compliance statement
- [`.machine_readable/6a2/STATE.a2ml`](https://github.com/hyperpolymath/echidna/blob/main/.machine_readable/6a2/STATE.a2ml) — machine-readable state

## Core invariants

1. **ML suggests; provers verify.** Neural components rank, route, propose. Formal provers carry the trust.
2. **Trust is checked, not asserted.** Solver binaries are SHAKE3-512 / BLAKE3 integrity-checked; certificates (Alethe, DRAT/LRAT, TSTP) are independently reproduced where formats allow.

## Key concepts

- **128 backends, 12 core** — 89 external prover bindings + 39 TypeChecker disciplines via TypedWasm Sigma.
- **11-step trust pipeline** — integrity → portfolio → certificates → axioms → confidence → mutation → pareto → statistics → emission (see Architecture page).
- **Polyglot stack** — Rust core, Julia ML sidecar, Idris2/Agda formal proofs, Zig FFI, Chapel parallel, AffineScript/Deno UI (migrating from ReScript).
- **Guix-primary package management** — sealed-container escape hatch for the non-free tail. Nix fallback was deprecated in 2026-05-18 estate ruling.
- **Justfile, not Make. Podman, not Docker.**
