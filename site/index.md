---
title: ECHIDNA — Neurosymbolic Theorem Proving
description: Trust-hardened neurosymbolic theorem proving platform
date: 2026-07-28
template: default
---

# ECHIDNA

**Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance**

ECHIDNA is a trust-hardened neurosymbolic theorem-proving platform. A Rust
core orchestrates a broad portfolio of interactive proof assistants, SMT
solvers, first-order ATPs, and constraint solvers behind a single dispatch
pipeline, with neural premise selection and tactic prediction provided by a
Julia ML layer.

Every proof result passes through a trust-hardening pipeline before it is
reported: solver-binary integrity verification, portfolio cross-checking,
proof-certificate checking, axiom-usage tracking, sandboxed execution, and
statistical confidence scoring.

## Explore

- [Platform documentation](/docs/index.html) — architecture, features, and API quick start
- [Core server API](/docs/api/core.html) — the API served at api.nesy-prover.dev
- [REST interface](/docs/api/rest.html)
- [GraphQL interface](/docs/api/graphql.html)
- [gRPC interface](/docs/api/grpc.html)
- [Coq playground](/playground/) — prove theorems in your browser with jsCoq

## Live API

A public instance of the ECHIDNA core server is available at
`https://api.nesy-prover.dev`.

Check service health:

```bash
curl https://api.nesy-prover.dev/api/health
```

List the core prover backends:

```bash
curl https://api.nesy-prover.dev/api/provers
```

Verify a small SMT goal with Z3:

```bash
curl -X POST https://api.nesy-prover.dev/api/verify \
  -H 'Content-Type: application/json' \
  -d '{"prover": "Z3", "content": "(assert (forall ((x Int)) (= (+ x 0) x)))(check-sat)"}'
```

The public instance is rate-limited and intended for evaluation. For
sustained or private use, run your own instance — the container image is
published at `ghcr.io/hyperpolymath/echidna`.

## Source and license

ECHIDNA is free software, licensed under AGPL-3.0-or-later. Development
happens at
[github.com/hyperpolymath/echidna](https://github.com/hyperpolymath/echidna),
where issues and contributions are welcome.
