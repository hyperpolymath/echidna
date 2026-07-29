<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Onboarding a new HP type-discipline backend

This is the working checklist for adding a new HP-ecosystem type
discipline to echidna. The 41 existing variants (TypeLL,
KatagoriaVerifier, TropicalTypeChecker, EchoTypeChecker, ...) all
followed this same pattern.

For background on what already exists, see
`docs/handover/B7-AUDIT-CORRECTION.md`.

## Where the wiring lives

Adding a new discipline `Foo` (i.e. `ProverKind::FooTypeChecker`)
touches exactly four files:

| File                                            | What to add                                                       |
|-------------------------------------------------|-------------------------------------------------------------------|
| `src/rust/provers/mod.rs`                       | Enum variant + parser arm + is_hp_ecosystem + default_executable  |
| `src/rust/provers/hp_ecosystem.rs::upstream()`  | One match arm: `Foo => ("typell", "foo")`                         |
| `src/rust/provers/typed_wasm.rs::type_info_for` | `TypeInfo` selector for the discipline (the typed_wasm route)     |
| `tests/fixtures/hp/foo_trivial.tll`             | One smoke fixture exercising the new wire                         |

If the discipline ships its own CLI (i.e. not `typell --discipline=foo`
but a standalone binary), it routes through `HPEcosystemBackend` and
the `upstream()` arm returns `("foo-cli", "foo")`. If it lives under
`typell`, it routes through `TypedWasmBackend` via the discipline
parameter.

The deciding question: **does the upstream maintainer ship a separate
binary?** Examples:

- `KatagoriaVerifier`  → standalone `katagoria` binary → `HPEcosystemBackend`.
- `TropicalTypeChecker` → standalone `tropical-type-check` binary → either path (currently `TypedWasmBackend`).
- `EchoTypeChecker`     → bundled under `typell`                  → `TypedWasmBackend`.

## Step-by-step

### 1. Add the enum variant

`src/rust/provers/mod.rs`, in the `ProverKind` enum (around line 294):

```rust
pub enum ProverKind {
    // ...
    FooTypeChecker,
    // ...
}
```

### 2. Parser arm

Same file, around line 567 (the string-to-ProverKind parser):

```rust
"footypechecker" | "foo" => Ok(ProverKind::FooTypeChecker),
```

### 3. `is_hp_ecosystem` arm

Same file, around line 434:

```rust
pub fn is_hp_ecosystem(&self) -> bool {
    matches!(self,
        // ...
        | ProverKind::FooTypeChecker
    )
}
```

### 4. `default_executable` arm

Same file, around line 1360. Either:

```rust
ProverKind::FooTypeChecker => "typell",       // bundled
// or
ProverKind::FooTypeChecker => "foo-cli",      // standalone
```

### 5. Factory routing arm

Same file, `ProverFactory::create` (around line 1822). Add to the
appropriate match arm:

- Standalone binary: add to the `HPEcosystemBackend` arm at line
  1776-1778.
- Bundled discipline: add to the `TypedWasmBackend` arm at lines
  1784-1822.

### 6. (Bundled discipline only) `upstream()` arm

`src/rust/provers/hp_ecosystem.rs`, the `upstream()` match around
line 63:

```rust
ProverKind::FooTypeChecker => ("typell", "foo"),
```

### 7. `TypeInfo` selector

`src/rust/provers/typed_wasm.rs::type_info_for` — return the discipline's
parametric `TypeInfo` so the unified verifier knows what to check.

### 8. Smoke fixture

`tests/fixtures/hp/foo_trivial.tll`:

```
# SPDX-License-Identifier: CC-BY-SA-4.0
#discipline: foo

theorem foo_identity : ... .
Proof.
  foo_refl.
Qed.
```

### 9. Run the smoke

`tests/gnn_augment_integration.rs::test_hp_ecosystem_gnn_wires_top_premise`
already loops over `is_hp_ecosystem()` kinds, so the new variant gets
GNN-wiring coverage for free. A direct backend smoke takes one more
line in `tests/common/mod.rs` if you want it.

## What you DON'T need to touch

- **Confidence levels** — the trust bridge reads
  `is_hp_ecosystem()` once; no per-discipline tuning.
- **Corpus extractors** — the HP corpus is built by
  `crates/typed_wasm` and indexed by Sigma parameters; new disciplines
  inherit the existing pipeline.
- **Result formatter** — `result_formatter.rs` reads `ProverKind`
  via Display; the variant name is the user-facing label.

## When the upstream binary doesn't ship

For early-development disciplines where the upstream tool isn't yet
buildable (e.g. an unreleased Wokelang variant), the backend will
return a "binary not found" runtime error. That is the right
behaviour — echidna's trust bridge surfaces it as
`ProverOutcome::Unsupported` and the caller sees a clear signal.

Do **not** stub the backend to return spurious success. Estate
consumers (per the C12 per-repo manifest) configure `[provers]
disabled = ["foo"]` to opt out cleanly.
