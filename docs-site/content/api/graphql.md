---
title: GraphQL API Reference
date: 2026-02-09
template: default
---

# GraphQL API Reference

Endpoint: `https://localhost:8080/graphql`

Playground: `https://localhost:8080/playground`

## Schema

### Queries

#### List Provers

```graphql
query {
  provers {
    kind
    tier
    complexity
  }
}
```

Returns all 30 prover backends.

#### Get Proof State

```graphql
query {
  proofState(sessionId: "session-uuid") {
    goals {
      conclusion
      hypotheses
    }
    status
    proofScript
  }
}
```

#### List Active Proofs

```graphql
query {
  listProofs {
    sessionId
    proverKind
    status
    startedAt
  }
}
```

#### Suggest Tactics

```graphql
query {
  suggestTactics(sessionId: "session-uuid") {
    name
    description
    confidence
  }
}
```

### Mutations

#### Submit a Proof

```graphql
mutation {
  submitProof(
    proverKind: COQ
    goal: "forall n : nat, n + 0 = n"
  ) {
    sessionId
    status
    goals {
      conclusion
    }
  }
}
```

#### Apply a Tactic

```graphql
mutation {
  applyTactic(
    sessionId: "session-uuid"
    tactic: "induction n"
  ) {
    result
    goals {
      conclusion
      hypotheses
    }
  }
}
```

#### Cancel a Proof

```graphql
mutation {
  cancelProof(sessionId: "session-uuid")
}
```

## Prover Kind Enum

```graphql
enum ProverKind {
  AGDA
  COQ
  LEAN
  ISABELLE
  Z3
  CVC5
  METAMATH
  HOL_LIGHT
  MIZAR
  PVS
  ACL2
  HOL4
  IDRIS2
  VAMPIRE
  EPROVER
  SPASS
  ALT_ERGO
  FSTAR
  DAFNY
  WHY3
  TLAPS
  TWELF
  NUPRL
  MINLOG
  IMANDRA
  GLPK
  SCIP
  MINIZINC
  CHUFFED
  OR_TOOLS
}
```
