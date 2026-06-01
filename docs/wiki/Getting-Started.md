# Getting Started

The canonical quickstart docs live in the repo:

- [`QUICKSTART-USER.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-USER.adoc) — first proof, REPL, simple verification
- [`QUICKSTART-DEV.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-DEV.adoc) — development workflow, Justfile-first
- [`QUICKSTART-MAINTAINER.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-MAINTAINER.adoc) — release, packaging, CI

This page is a short orientation; defer to those for current details.

## Prerequisites

- **Rust** stable (MSRV pinned in `rust-toolchain.toml`; nightly accepted, not required)
- **Julia 1.10+** (for the ML sidecar — optional; the core compiles without it)
- **Just** (task runner — primary build system per RSR-H14)
- **Guix** (primary package manager; sealed-container escape hatch at `.containerization/Containerfile.wave3`)
- **Podman** (containers — RSR-H15; **do not** use Docker)

> Note: Nix as a fallback was deprecated in the 2026-05-18 estate ruling and fully removed estate-wide on 2026-06-01. Use Guix or the sealed container only.

## Quick setup

```bash
git clone https://github.com/hyperpolymath/echidna.git
cd echidna

just setup            # installs deps via Guix manifest where possible
just doctor           # diagnose any missing components
just build            # cargo build --release
```

## First proof

```bash
# Interactive REPL
just repl

# Verify a proof file
just verify examples/simple.v
```

## Install prover backends

The 12 core (Tier 1) backends need their binaries on PATH. See
[`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md)
for the tier table. The Guix manifest at `manifests/live-provers.scm` covers
the bulk; the sealed container at `.containerization/Containerfile.wave3`
covers the non-free / not-in-Guix tail.

```bash
# Inside a Guix environment:
guix shell -m manifests/live-provers.scm -- just test-live

# Or inside the container:
podman build -f .containerization/Containerfile.wave3 -t echidna:wave3 .
podman run --rm -it echidna:wave3 just test
```

## ML sidecar (optional, gates GNN features)

```bash
# Train on the static corpus (CPU smoke)
just train-cpu

# Or on GPU with the full 553 MB corpus
just train

# Evaluate the trained weights against the held-out validation split
just eval
```

See [`docs/handover/S5-VERIFICATION-RUNBOOK.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/S5-VERIFICATION-RUNBOOK.md)
for the end-to-end verification flow.

## What's next

- [Guides](Guides) — adding a backend, API usage, training the model
- [Architecture](Architecture) — how the pieces fit
- [`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) — what's being built next
