---
title: echidnabot Documentation
date: 2025-01-01
template: default
---

# echidnabot

Proof-aware CI bot that automatically verifies mathematical theorems in your codebase.

## What is echidnabot?

echidnabot is an intelligent CI orchestration layer for formal mathematics and verified software. When you push code containing formal proofs—whether in Coq, Lean 4, Agda, Isabelle/HOL, Z3, Metamath, or other theorem provers—echidnabot automatically dispatches verification jobs to ECHIDNA Core and reports results directly in your pull requests.

Think of it as **GitHub Actions for mathematical certainty**.

## Key Features

- **Multi-Platform**: GitHub, GitLab, Bitbucket, Codeberg
- **Multi-Prover**: Coq, Lean, Agda, Isabelle, Z3, Metamath, and more
- **Type-Safe**: Written entirely in Rust with async Tokio
- **GraphQL API**: Query and control via modern API
- **ML-Powered**: Tactic suggestions via ECHIDNA's Julia ML backend

## Quick Start

```bash
# Install echidnabot
cargo install echidnabot

# Register a repository
echidnabot register --platform github --repo owner/name

# Trigger a manual check
echidnabot check --commit HEAD
```

## Architecture

```
GitHub/GitLab/Bitbucket
        ↓ webhooks
    echidnabot (Rust)
        ↓ GraphQL
    ECHIDNA Core
        ├→ Coq, Lean, Agda...
        └→ Julia ML
        ↓ results
    echidnabot
        ↓ Check Runs
    Platform
```

## Supported Provers

| Tier | Provers | Status |
|------|---------|--------|
| 1 | Agda, Coq, Lean 4, Isabelle/HOL, Z3, CVC5 | Ready |
| 2 | Metamath, HOL Light, Mizar | MVP |
| 3 | PVS, ACL2, HOL4 | Planned |

## License

PMPL-1.0-or-later OR LicenseRef-Palimpsest-0.5
