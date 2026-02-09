---
title: REST API Reference
date: 2026-02-09
template: default
---

# REST API Reference

Base URL: `https://localhost:8000/api/v1`

## Endpoints

### Health Check

```
GET /health
```

Returns server health status.

### Provers

#### List All Provers

```
GET /api/v1/provers
```

Returns all 30 supported prover backends with tier and complexity information.

#### Get Prover Details

```
GET /api/v1/provers/:kind
```

Returns details for a specific prover backend.

**Path Parameters:**
- `kind` — Prover identifier (e.g., `coq`, `lean`, `z3`, `isabelle`)

### Proofs

#### Submit a Proof

```
POST /api/v1/proofs
```

**Request Body:**
```json
{
  "prover": "coq",
  "goal": "forall n : nat, n + 0 = n",
  "timeout_ms": 30000
}
```

**Response:**
```json
{
  "id": "proof-uuid",
  "status": "verified",
  "prover": "coq",
  "goals_remaining": 0
}
```

#### List Active Proofs

```
GET /api/v1/proofs
```

Returns all active proof sessions.

#### Get Proof Status

```
GET /api/v1/proofs/:id
```

#### Cancel a Proof

```
DELETE /api/v1/proofs/:id
```

### Tactics

#### Apply a Tactic

```
POST /api/v1/proofs/:id/tactics
```

**Request Body:**
```json
{
  "tactic": "induction n"
}
```

#### Suggest Tactics

```
GET /api/v1/proofs/:id/tactics/suggest
```

Returns ML-suggested tactics for the current proof state.
Uses Julia ML service (port 8090) with fallback to prover built-in suggestions.

## Prover Kinds

| Kind | Tier | Category |
|------|------|----------|
| agda | core | Interactive Proof Assistant |
| coq | core | Interactive Proof Assistant |
| lean | core | Interactive Proof Assistant |
| isabelle | core | Interactive Proof Assistant |
| idris2 | core | Interactive Proof Assistant |
| fstar | core | Interactive Proof Assistant |
| z3 | core | SMT Solver |
| cvc5 | core | SMT Solver |
| alt_ergo | core | SMT Solver |
| dafny | core | Auto-Active Verifier |
| why3 | core | Auto-Active Verifier |
| metamath | core | Specialised |
| hol_light | core | Specialised |
| mizar | core | Specialised |
| hol4 | core | Specialised |
| pvs | core | Specialised |
| acl2 | core | Specialised |
| tlaps | core | Specialised |
| twelf | core | Specialised |
| nuprl | core | Specialised |
| minlog | core | Specialised |
| imandra | core | Specialised |
| vampire | core | First-Order ATP |
| eprover | core | First-Order ATP |
| spass | core | First-Order ATP |
| glpk | core | Constraint Solver |
| scip | core | Constraint Solver |
| minizinc | core | Constraint Solver |
| chuffed | core | Constraint Solver |
| or_tools | core | Constraint Solver |
