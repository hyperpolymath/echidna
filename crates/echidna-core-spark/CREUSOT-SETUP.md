<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Creusot Setup Guide

How to run formal verification on `echidna-core-spark` using Creusot.

## Prerequisites

Creusot requires a pinned Rust **nightly** toolchain and a Why3 installation
with SMT solvers.  Stable Rust builds this crate without Creusot; the
`--features creusot` flag is only needed for the verifier pass.

## 1 — Install a Rust nightly toolchain

Creusot pins to specific nightly versions.  Check the Creusot repository
(`https://github.com/creusot-rs/creusot`) for the current supported nightly
and add it:

```bash
rustup toolchain install nightly-2024-05-01   # example — check current pin
rustup override set nightly-2024-05-01 --path crates/echidna-core-spark
```

`rust-toolchain.toml` is at the crate root (added Stage 8c-M1) and pins
`nightly-2024-05-01`.  Check the Creusot repository for the current supported
nightly and update both `rust-toolchain.toml` and the `formal-verification.yml`
workflow when bumping.

## 2 — Install Creusot

```bash
cargo +nightly install creusot
```

This installs `creusot-rustc` (the annotated Rust compiler) alongside the
standard `cargo` toolchain.

## 3 — Install Why3 + SMT solvers

Creusot translates annotated Rust to Why3 ML, which is then discharged by
Z3/CVC5/Alt-Ergo.  Echidna already ships these solvers as prover backends,
so they should already be available.

```bash
# Fedora / RHEL (adjust for your distro)
sudo dnf install why3 z3 cvc5 alt-ergo

# Or via opam (OCaml package manager)
opam install why3
```

Verify:

```bash
why3 --version
z3 --version
```

## 4 — Run verification

From the repository root:

```bash
cargo +nightly creusot \
    -p echidna-core-spark \
    -- \
    --features creusot \
    --why3 $(which why3)
```

Or use the Justfile recipe (added in Stage 8c-M1):

```bash
just verify-trust-pipeline
```

## 5 — Interpreting output

Creusot emits Why3 obligations; Why3 reports each obligation as:

- `Valid` — SMT solver discharged the proof obligation.
- `Unknown` / `Timeout` — solver could not discharge within the time limit.
  Increase the limit with `--timeout <seconds>` or simplify the contract.
- `Invalid` — the contract is wrong or there is a real bug.

All obligations in `impl_invariants` are designed to discharge quickly
(< 30 s each on a modern workstation).

## 6 — CI integration

`.github/workflows/formal-verification.yml` runs two jobs, both merge gates:

- `stable-tests`: `cargo test -p echidna-core-spark` on stable Rust (~10 s).
- `creusot-verify`: `cargo +nightly creusot` with Why3 + Z3 discharge.
  Requires `apt-get install why3 z3 alt-ergo` in the runner (Ubuntu 22.04+).

Both were promoted to hard gates in Stage 8c-M3 (no `continue-on-error`).

## Annotation style

Creusot contracts in this crate are written in two complementary forms:

1. **Doc-comment code blocks** — always compiled and visible in `rustdoc`;
   describe the contract in human-readable form; not executed by the compiler.
2. **`#[cfg_attr(feature = "creusot", ...)]` attributes** — machine-readable;
   active when Creusot runs (`--features creusot`); no-ops on stable Rust.

### Stage status

| Milestone | Contents | Status |
|---|---|---|
| 8c-M1 | `rust-toolchain.toml`, `formal-verification.yml`, `just verify-trust-pipeline` | **done** |
| 8c-M2 | `dominates` marked `#[pure]`; `compute` ensures with `^candidates`; inner-loop `#[invariant]` for `dominated` | **done** |
| 8c-M3 | Outer-loop invariant (`snapshot!` + prefix classification); Why3 CI hard gate | **done** |

All three milestones are complete.  The `compute` function now carries the
full two-level invariant structure:

- **Outer**: `snapshot!(candidates)` at entry + `#[invariant]` asserting
  (a) objectives unchanged for all k, (b) `is_pareto_optimal[k]` correctly
  set for k < i.
- **Inner**: `dominated == (∃ k < j, k ≠ i : dominates(k, i))`.

The CI workflow (`formal-verification.yml`) is a hard gate: both
`stable-tests` and `creusot-verify` must pass for a merge.  If the nightly
pin drifts, bump `rust-toolchain.toml` + the workflow's `toolchain:` field
together.

This keeps the crate buildable on stable Rust at all times while still
expressing every proof obligation in machine-verifiable syntax.

## References

- Creusot repository: https://github.com/creusot-rs/creusot
- Why3 documentation: https://www.why3.org/
- SPARK Adoption Plan: `docs/design/SPARK_ADOPTION_PLAN.md`
- Echidna ROADMAP Stage 8c: `docs/ROADMAP.md`
