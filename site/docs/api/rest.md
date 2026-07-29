---
title: REST Interface Reference
date: 2026-07-28
template: default
---

# REST Interface Reference

The `echidna-rest` binary is an optional self-hosted service that
exposes an OpenAPI-documented `/api/v1` surface, separate from the
[core server API](/docs/api/core.html). It binds `127.0.0.1:8000` over
plain HTTP — put it behind a TLS-terminating proxy before exposing it.

Documented from `src/interfaces/rest/{main,handlers,models}.rs`.

## Endpoints

### Health check

```
GET /health
```

Note that health sits at the server root, not under `/api/v1`.

### Provers

```
GET /api/v1/provers
GET /api/v1/provers/{kind}
```

Each entry carries the prover kind, version string, tier, complexity,
and whether the backend binary is available on this host:

```json
{ "kind": "Coq", "version": "8.19", "tier": 1, "complexity": 3, "available": true }
```

`{kind}` is a `ProverKind` variant name, for example `Coq`, `Lean`, `Z3`.

### Proofs

```
POST   /api/v1/proofs
GET    /api/v1/proofs
GET    /api/v1/proofs/{id}
DELETE /api/v1/proofs/{id}
```

Submit request — the timeout field is `timeout_seconds` and is optional:

```json
{
  "goal": "forall n : nat, n + 0 = n",
  "prover": "Coq",
  "timeout_seconds": 30
}
```

Response:

```json
{
  "id": "proof-uuid",
  "prover": "Coq",
  "goal": "forall n : nat, n + 0 = n",
  "status": "Verified",
  "proof_script": ["induction n", "reflexivity"],
  "time_elapsed": 0.42
}
```

`error_message` is present only on failure.

### Tactics

```
POST /api/v1/proofs/{id}/tactics
```

The request is a tactic name plus its arguments; `args` is required and
may be an empty array:

```json
{ "name": "induction", "args": ["n"] }
```

The response wraps the updated proof state:

```json
{ "success": true, "proof_state": { "id": "proof-uuid", "status": "InProgress" } }
```

### Exchange and consultation

```
GET  /api/v1/proofs/{id}/export
POST /api/v1/exchange/import
POST /api/v1/consult
```

`export` and `import` move proofs across provers via the exchange
layer; `consult` runs a portfolio consultation.

[Documentation index](/docs/index.html)
