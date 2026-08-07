<!--
  SPDX-License-Identifier: CC-BY-SA-4.0
  SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

  docs/ARCHITECTURE.md is canonical. This file previously held generic
  scaffold text ("modular, maintainable architecture designed for clarity,
  scalability...") that contained no project-specific content — it described
  no part of ECHIDNA and duplicated nothing real. Replaced with a pointer
  rather than deleted, because the path is referenced externally.
-->

# Architecture

The architecture documentation for ECHIDNA lives in
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — the polyglot layout, the
dispatch path, the trust-hardening pipeline, and how the Rust core, Julia ML
sidecar, Idris2 ABI, Zig FFI and optional Chapel parallel layer fit together.

Related canonical documents:

- [`docs/PROVER_COUNT.md`](docs/PROVER_COUNT.md) — backend tier table and what
  each published count actually counts
- [`docs/ROADMAP.md`](docs/ROADMAP.md) — stage map and current direction
- [`docs/DEBT.md`](docs/DEBT.md) — known licence, documentation and code debt
- [`.machine_readable/descriptiles/META.a2ml`](.machine_readable/descriptiles/META.a2ml)
  — the machine-readable architecture record
