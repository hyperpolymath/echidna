# FAQ

## How many provers are supported?

**128 total** ProverKind variants: 89 external prover bindings plus 39 TypeChecker disciplines routed via TypedWasm Sigma.

Of these, **12 core** are exposed by the default REST API: Coq/Rocq, Lean 4, Agda, Isabelle/HOL, Idris 2, F\*, Z3, CVC5, Alt-Ergo, Dafny, Vampire, E Prover. The remaining 116 are reachable via explicit `ProverKind` selection in CLI / REPL / GraphQL.

The full tier table lives in [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md).

## Are proofs sandboxed?

Yes. Each prover runs in Podman or bubblewrap with no host filesystem or network access. Resource limits (CPU, memory, wall time) are enforced per `DispatchConfig`. See [`src/rust/executor/`](https://github.com/hyperpolymath/echidna/tree/main/src/rust/executor).

## How is trust scored?

Five-tier Bayesian confidence model (`src/rust/verification/confidence.rs`). Proofs verified by multiple independent provers receive higher trust. Cross-prover certificate verification (Alethe / DRAT-LRAT / TSTP, replayed independently) elevates trust further. Solver binaries are SHAKE3-512 + BLAKE3 integrity-checked against `config/solver-manifest.toml` before invocation.

## Can I add my own prover?

Yes. Implement the `ProverBackend` trait in `src/rust/provers/your_prover.rs`, add a variant to `ProverKind`, register in `ProverFactory`, and add fixtures under `tests/`. See [Guides](Guides) for the step-by-step.

## What's the ML layer?

Julia sidecar (port 8090). A GNN ranks premises; a logistic regression head suggests tactics. Both can be retrained from accumulated proof outcomes stored in VeriSimDB. The architecture is "ML suggests; provers verify" — a wrong suggestion costs a CPU cycle, not soundness.

See [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md) for the data flow.

## Is the wiki authoritative?

No. **The repo wins** when the wiki and the in-repo docs disagree. The wiki is a navigation aid pointing at the canonical sources. Pages here are refreshed periodically but lag the repo.

Canonical sources of truth:
- [`CLAUDE.md`](https://github.com/hyperpolymath/echidna/blob/main/CLAUDE.md) for codebase orientation
- [`.machine_readable/6a2/STATE.a2ml`](https://github.com/hyperpolymath/echidna/blob/main/.machine_readable/6a2/STATE.a2ml) for current state
- [`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) for direction

## Why MPL-2.0 and not MIT or AGPL?

Practical balance: weak copyleft at the file level (modifications to MPL'd files must be open) without copyleft-by-linking (so downstream commercial use is straightforward). The project migrated from a dual MIT/Palimpsest-0.6 licence in 2026; `NOTICE` and `LICENSE` reflect the current state.

## How do I report a security issue?

See [`SECURITY.md`](https://github.com/hyperpolymath/echidna/blob/main/SECURITY.md) and [`.well-known/security.txt`](https://github.com/hyperpolymath/echidna/blob/main/.well-known/security.txt). Do not disclose publicly until addressed.
