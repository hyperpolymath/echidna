---
title: GraphQL Interface Reference
date: 2026-07-28
template: default
---

# GraphQL Interface Reference

The `echidna-graphql` binary is an optional self-hosted service. It
binds `127.0.0.1:8081` over plain HTTP and serves both the GraphQL
endpoint and the interactive playground at the server root — a `POST`
to `/` executes operations, a `GET` renders the playground. There is a
separate `GET /health`.

Documented from `src/interfaces/graphql/{main,schema}.rs`.

## Queries

### provers

```graphql
query {
  provers {
    kind
    version
    tier
    complexity
    available
  }
}
```

### proofState

Takes `id`, not a session identifier:

```graphql
query {
  proofState(id: "proof-uuid") {
    id
    prover
    goal
    status
    proofScript
    goalsRemaining
    timeElapsed
    errorMessage
  }
}
```

### listProofs

```graphql
query {
  listProofs(limit: 20) {
    id
    prover
    status
    goalsRemaining
  }
}
```

### suggestTacticsByProofId

The query form of tactic suggestion, keyed by an existing proof:

```graphql
query {
  suggestTacticsByProofId(proofId: "proof-uuid", limit: 5) {
    name
    args
    description
    confidence
  }
}
```

### proverStatus

```graphql
query {
  proverStatus(prover: "Coq") {
    available
  }
}
```

## Mutations

### submitProof

```graphql
mutation {
  submitProof(goal: "forall n : nat, n + 0 = n", prover: COQ) {
    id
    status
    goalsRemaining
  }
}
```

### applyTactic

`proofId`, `tactic`, and `args` are all required; pass an empty list
when the tactic takes no arguments:

```graphql
mutation {
  applyTactic(proofId: "proof-uuid", tactic: "induction", args: ["n"]) {
    id
    status
    proofScript
    goalsRemaining
  }
}
```

### verifyProof

Verifies prover source directly, without a proof session:

```graphql
mutation {
  verifyProof(prover: "Z3", content: "(check-sat)") {
    status
    message
    proverOutput
    durationMs
    artifacts
  }
}
```

### suggestTactics

Tactic suggestion is a **mutation**, not a query, and takes a goal
state rather than a proof identifier:

```graphql
mutation {
  suggestTactics(prover: "Coq", context: "", goalState: "forall n : nat, n + 0 = n") {
    tactic
    confidence
    explanation
  }
}
```

### cancelProof

```graphql
mutation {
  cancelProof(proofId: "proof-uuid")
}
```

[Documentation index](/docs/index.html)
