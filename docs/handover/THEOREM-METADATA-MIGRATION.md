<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: MPL-2.0 -->

# Theorem Metadata Migration (deferred)

## Purpose

`Theorem.aspects` currently serves two unrelated roles:

1. **Math-domain tags** — dotted keys like `"arithmetic.natural_numbers"` produced by
   `Aspect::dotted_key()`. These drive the learning loop, GNN domain hints, and
   coprocessor routing.
2. **Structural / provenance meta-tags** — plain strings like `"axiom"`, `"constructor"`,
   `"dedukti-import"` injected by parsers. These describe the *kind* of theorem, not
   its mathematical content.

The D1 boundary filter (`s.contains('.')`) prevents structural tags from leaking into
the learning-loop key space, so correctness is preserved. However, mixing the two kinds
in a single `Vec<String>` field is a hygiene problem. This document tracks the deferred
migration.

## Current state — 8 parser sites using structural tags

| File | Line(s) | Tag(s) used |
|------|---------|-------------|
| `src/rust/provers/agda.rs` | 297 | `"axiom"` |
| `src/rust/provers/metamath.rs` | 316, 328 | `"axiom"`, `"theorem"` |
| `src/rust/provers/idris2.rs` | 522, 550, 586 | `"constructor"`, `"projection"`, `"interface-method"` |
| `src/rust/provers/hol_light.rs` | 457 | `"hol_light"` |
| `src/rust/exchange/dedukti.rs` | 101, 118 | `"dedukti-import"`, `"has-definition"` |
| `src/rust/exchange/opentheory.rs` | 84 | `"opentheory-import"` |

These are **not migrated** in D1. The boundary filter contains the damage.

## Proposed target structure

```rust
pub enum TheoremKind {
    Axiom,
    Theorem,
    Definition,
    Constructor,
    Projection,
    InterfaceMethod,
}

pub struct Theorem {
    // ... existing fields ...
    pub kind: TheoremKind,
    pub import_source: Option<String>,   // e.g. "dedukti", "opentheory"
    pub prover_source: Option<ProverKind>,
    pub has_proof: bool,
    // aspects contains ONLY dotted math-domain keys after migration
    pub aspects: Vec<String>,
}
```

## Scope of migration work

- **8 parser sites**: replace `aspects: vec!["axiom"]` etc. with `kind: TheoremKind::Axiom`.
- **Callers that read `Theorem.aspects` for structural meaning**: find with
  `rg "theorem.*\.aspects" src/` — expected ~4-6 call sites.
- **Remove boundary filter** once no structural tags can appear in `aspects`.

Estimated effort: ~3-4 hours of mechanical work. No algorithmic changes required.

## Not blocking

The boundary filter introduced in D1 (`src/rust/provers/mod.rs::gnn_augment_tactics`
and `src/rust/agent/meta_controller.rs::primary_domain`) is sufficient to prevent
correctness issues. This migration is hygiene, not a correctness fix. Schedule
opportunistically alongside the next `Theorem` struct refactor.
