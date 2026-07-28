---
title: ECHIDNA Platform Documentation
description: Architecture, features, and API quick start
date: 2026-07-28
template: default
---

# Platform Documentation

**Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance**

A trust-hardened neurosymbolic theorem proving platform supporting a broad
portfolio of prover backends with a comprehensive verification pipeline.

## Features

- **Prover portfolio**: Coq, Lean 4, Isabelle/HOL, Z3, CVC5, Agda, Idris2, and many more — see the canonical tier table in the repository's `docs/PROVER_COUNT.md`
- **Trust pipeline**: solver integrity, proof certificates, axiom tracking, confidence scoring
- **API interfaces**: REST (OpenAPI), GraphQL, gRPC
- **Neural premise selection**: Julia ML layer with tactic prediction
- **Proof exchange**: cross-prover via OpenTheory and Dedukti

## API Quick Start

The hosted core server at `https://api.nesy-prover.dev` exposes the
primary HTTP API:

```bash
curl https://api.nesy-prover.dev/api/health
curl https://api.nesy-prover.dev/api/provers
```

Verifying an SMT script takes a prover name and its source:

```bash
curl -X POST https://api.nesy-prover.dev/api/verify \
  -H "Content-Type: application/json" \
  -d '{"prover": "Z3", "content": "(assert (forall ((x Int)) (= (+ x 0) x)))(check-sat)"}'
```

See the [core server API reference](/docs/api/core.html) for every
route. A self-hosted instance serves the same routes over plain HTTP on
the port passed to `--port` (default 8081) — front it with a TLS proxy
before exposing it.

Three further interface services ship as separate optional binaries,
each binding loopback over plain HTTP:

### REST interface (port 8000)

An OpenAPI-documented `/api/v1` surface — see the
[REST interface reference](/docs/api/rest.html).

### GraphQL interface (port 8081)

Endpoint and interactive playground both at the server root — see the
[GraphQL interface reference](/docs/api/graphql.html).

### gRPC interface (port 50051)

See the [gRPC interface reference](/docs/api/grpc.html) and the proto
definition at `src/interfaces/grpc/proto/echidna.proto`.

## Architecture

ECHIDNA follows a trust-hardened architecture:

1. **Solver Binary Integrity** — SHAKE3-512 + BLAKE3 verification
2. **SMT Portfolio Solving** — cross-checking across solvers
3. **Proof Certificate Checking** — Alethe, DRAT/LRAT, TSTP
4. **Axiom Usage Tracking** — 4 danger levels (Safe, Noted, Warning, Reject)
5. **Solver Sandboxing** — Podman, bubblewrap, or none
6. **Confidence Scoring** — 5-level trust hierarchy
7. **Mutation Testing** — specification robustness testing

## License

AGPL-3.0-or-later. Source at
[github.com/hyperpolymath/echidna](https://github.com/hyperpolymath/echidna).

[Back to home](/index.html)
