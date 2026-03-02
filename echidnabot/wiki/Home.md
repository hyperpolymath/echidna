# echidnabot Wiki

Welcome to the **echidnabot** wiki — your comprehensive guide to proof-aware CI.

## What is echidnabot?

echidnabot is a CI bot that automatically verifies mathematical theorems and formal proofs in your codebase. When you push code containing proofs in Coq, Lean, Agda, Isabelle, Z3, or other theorem provers, echidnabot dispatches verification jobs and reports results directly in your pull requests.

**Think of it as GitHub Actions for mathematical certainty.**

## Quick Navigation

### For Users
- [[Getting Started]] — Install and configure echidnabot
- [[Configuration Reference]] — All configuration options
- [[Supported Provers]] — List of theorem provers
- [[Platform Integration]] — GitHub, GitLab, Bitbucket setup

### For Developers
- [[Architecture]] — System design and components
- [[API Reference]] — GraphQL and REST API docs
- [[Contributing]] — How to contribute
- [[Development Setup]] — Local development environment

### Reference
- [[FAQ]] — Frequently asked questions
- [[Troubleshooting]] — Common issues and solutions
- [[Changelog]] — Version history
- [[Roadmap]] — Future plans

## Why echidnabot?

### The Problem

You're writing formally verified software. Your proofs ensure correctness at a mathematical level. But your CI pipeline doesn't understand proofs:

- ❌ Tests pass, but proofs are broken
- ❌ PRs merge with unverified theorems
- ❌ No one notices until a dependent build fails
- ❌ Manual verification is slow and error-prone

### The Solution

echidnabot bridges the gap:

```
Push/PR → echidnabot → ECHIDNA Core → Proof Result → Check Run ✓/✗
```

Every commit with proof files gets verified. Broken proofs block merges. ML-powered suggestions help fix failing proofs.

## Key Features

| Feature | Description |
|---------|-------------|
| **Multi-Prover** | Coq, Lean 4, Agda, Isabelle, Z3, CVC5, Metamath |
| **Multi-Platform** | GitHub, GitLab, Bitbucket, Codeberg |
| **Bot Modes** | Verifier, Advisor, Consultant, Regulator |
| **ML Suggestions** | Tactic suggestions for failing proofs |
| **GraphQL API** | Query and control programmatically |
| **Self-Hosting** | Run your own instance |

## Related Projects

- [ECHIDNA](https://github.com/hyperpolymath/echidna) — The theorem proving platform
- [Oikos Bot](https://github.com/hyperpolymath/oikos) — Ecological & economic code analysis
- [RSR](https://github.com/hyperpolymath/rhodium-standard-repositories) — Repository quality standards

## About hyperpolymath

[hyperpolymath](https://github.com/hyperpolymath) builds politically autonomous software for ecologically and economically conscious development.

Our principles:
- **Formal correctness** — Proofs over tests
- **Sustainability** — Carbon-aware computing
- **Independence** — No Big Tech dependencies
- **Openness** — AGPL/PMPL-1.0 licensing

---

*echidnabot is licensed under PMPL-1.0-or-later*
