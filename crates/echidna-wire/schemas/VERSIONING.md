<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# ECHIDNA Wire Schema Versioning Policy (`crates/echidna-wire`)

Every root message MUST carry `schemaVersion :UInt16`. Current: **1**.
File-level capnp IDs (`@0x…;`) are generated once and NEVER changed.

## Compatibility model

Cap'n Proto is structurally forward/backward-compatible within a major
version provided the rules below are respected. Major version bumps are
breaking and require a coordinated rollout across Rust core, Julia,
Chapel, and UI peers.

## Adding a field (SAFE — no version bump)

- Append new fields at the next unused `@N`.
- New fields MUST either:
  - (a) have a default value (e.g. `@N :Bool = false`), OR
  - (b) be paired with a `has<Name> :Bool` sibling for optional semantics.
- New union variants may be appended at the end of an existing union.
- New nested structs may be added freely.

## Removing / changing a field (UNSAFE — major bump)

- Reordering `@N` IDs of existing fields.
- Changing a field's wire type (e.g. `UInt32` → `UInt64`).
- Removing a non-optional field.
- Reordering union discriminants.
- Changing the stable `ProverKind` discriminant mapping
  (mirrored in `src/rust/ffi/mod.rs`).

## Deprecation flow

1. Mark the field obsolete in this file and in a comment on the `.capnp`
   line. Add a new replacement field at the next `@N`.
2. Wait ONE minor version before removal candidacy (L1.0 → L1.1).
3. Field removal = major bump (L1.x → L2.0). Must ship an
   `echidna-wire v2` alongside v1 for at least one release cycle.

## Connection-time negotiation

Every transport session opens with a `Hello` exchange (schema deferred
to L1.1 in `version.capnp`):

```
client → server : Hello    { supportedMajors :List(UInt16); preferredMajor :UInt16; }
server → client : HelloAck { agreedMajor :UInt16; agreedMinor :UInt16; }
```

If no overlap: server returns `HelloAck { agreedMajor = 0 }` and closes.

## ProverKind discriminant governance

Appending a new variant to `ProverKind` (`src/rust/provers/mod.rs`) is
SAFE iff:

- the next contiguous `u16` is used (currently 105),
- `kind_from_u8` / `kind_to_u8` are updated in lockstep
  (`src/rust/ffi/mod.rs`),
- this file records the assignment.

Holes in the discriminant space are FORBIDDEN — the invertibility test
at `src/rust/ffi/mod.rs` (see `kind_to_u8_injective` / round-trip tests)
must keep passing.

## Current assignments

- Schema major: **1**. Minor: **0**.
- File IDs:
  - `common.capnp` = `@0xf2f7187fddaa9139`
  - `proof.capnp`  = `@0xfa73f2ec7415f450`
  - `prover.capnp` = `@0xf1841ae6bbc44651`
  - `gnn.capnp`    = `@0xfbb66b8481def8a0`
- Deprecations in flight: none.
