---
title: API Reference
date: 2025-01-01
template: default
---

# GraphQL API Reference

echidnabot exposes a GraphQL API for querying and controlling proof verification.

## Endpoint

```
POST /graphql
```

## Queries

### repository

Fetch a registered repository.

```graphql
query {
  repository(platform: GITHUB, owner: "org", name: "repo") {
    id
    platform
    owner
    name
    enabledProvers
    webhookConfigured
  }
}
```

### repositories

List all registered repositories.

```graphql
query {
  repositories(platform: GITHUB) {
    id
    owner
    name
    enabledProvers
  }
}
```

### job

Fetch a specific proof job.

```graphql
query {
  job(id: "uuid-here") {
    id
    repoId
    commitSha
    prover
    status
    result {
      success
      message
      durationMs
      verifiedFiles
      failedFiles
    }
  }
}
```

### jobsForRepo

List jobs for a repository.

```graphql
query {
  jobsForRepo(repoId: "uuid-here", limit: 10) {
    id
    commitSha
    prover
    status
    queuedAt
  }
}
```

### availableProvers

List available theorem provers.

```graphql
query {
  availableProvers {
    kind
    displayName
    extensions
    tier
  }
}
```

## Mutations

### registerRepository

Register a new repository for proof verification.

```graphql
mutation {
  registerRepository(input: {
    platform: GITHUB
    owner: "org"
    name: "repo"
    enabledProvers: [COQ, LEAN4]
    webhookSecret: "optional-secret"
  }) {
    id
    webhookUrl
  }
}
```

### triggerCheck

Manually trigger proof verification.

```graphql
mutation {
  triggerCheck(
    repoId: "uuid-here"
    commitSha: "abc123"
    provers: [COQ, LEAN4]
  ) {
    id
    status
    queuedAt
  }
}
```

### updateRepoSettings

Update repository settings.

```graphql
mutation {
  updateRepoSettings(
    repoId: "uuid-here"
    settings: {
      enabledProvers: [COQ, LEAN4, AGDA]
      autoCheck: true
    }
  ) {
    id
    enabledProvers
  }
}
```

## Types

### Platform

```graphql
enum Platform {
  GITHUB
  GITLAB
  BITBUCKET
  CODEBERG
}
```

### ProverKind

```graphql
enum ProverKind {
  COQ
  LEAN4
  AGDA
  ISABELLE
  Z3
  CVC5
  METAMATH
  HOL_LIGHT
  MIZAR
}
```

### JobStatus

```graphql
enum JobStatus {
  QUEUED
  RUNNING
  COMPLETED
  FAILED
  CANCELLED
}
```

## Authentication

Include your API token in the Authorization header:

```
Authorization: Bearer <your-token>
```

## Rate Limits

- 1000 requests per hour per token
- 10 concurrent proof jobs per repository
