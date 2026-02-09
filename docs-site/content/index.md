---
title: ECHIDNA - Neurosymbolic Theorem Proving
date: 2026-02-09
template: default
---

# ECHIDNA

**Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance**

A trust-hardened neurosymbolic theorem proving platform supporting 30 prover backends
with a comprehensive verification pipeline.

## Features

- **30 Prover Backends**: Coq, Lean 4, Isabelle/HOL, Z3, CVC5, Agda, Idris2, and more
- **Trust Pipeline**: Solver integrity, proof certificates, axiom tracking, confidence scoring
- **API Interfaces**: REST (OpenAPI), GraphQL, gRPC
- **Neural Premise Selection**: Julia ML layer with tactic prediction
- **Proof Exchange**: Cross-prover via OpenTheory and Dedukti

## API Quick Start

### REST API (Port 8000)

List all provers:

```bash
curl https://localhost:8000/api/v1/provers
```

Submit a proof:

```bash
curl -X POST https://localhost:8000/api/v1/proofs \
  -H "Content-Type: application/json" \
  -d '{"prover": "coq", "goal": "forall n, n + 0 = n"}'
```

### GraphQL (Port 8080)

Query provers and submit proofs via the GraphQL playground.

### gRPC (Port 50051)

See the proto definition at `src/interfaces/grpc/proto/echidna.proto`.

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

PMPL-1.0-or-later
