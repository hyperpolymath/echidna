<!--
SPDX-License-Identifier: PMPL-1.0-or-later
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Cap'n Proto Schema Versioning Policy

Schema file: `schemas/echidna.capnp`
Schema ID: `@0xd3b45f8ae1c79012` (immutable — generated once, never changed)

## Wire Compatibility Guarantee

Cap'n Proto's wire format is **forward- and backward-compatible by default**,
but only if the following rule is obeyed without exception:

> **Add fields at the end of a struct only. Never reorder, rename, or remove
> existing fields. Never change an existing field's type or ordinal number.**

Each field carries an explicit ordinal (`@N`). The ordinal is its wire identity.
Renaming a field in the `.capnp` source is safe (it only changes the generated
symbol name). Changing `@N` or the field type is a **breaking change**.

## Non-Breaking Changes (safe to make freely)

| Change | Why it is safe |
|--------|----------------|
| Add a new field at the end of a struct (`@N` where N > current max) | Older readers ignore unknown fields; older writers produce zero for missing fields |
| Add a new struct or enum anywhere in the file | Unused by older code |
| Add a new enum variant at the end | Older code sees it as an unknown discriminant |
| Rename a field or type (source only) | Ordinals and wire layout unchanged |
| Change a default value in the schema | Wire encoding unaffected; generated code picks up the new default |
| Add a new `annotation` | Not encoded on the wire |

## Breaking Changes (require a new struct name or a bumped `schemaVersion` field)

| Change | Why it breaks |
|--------|---------------|
| Remove or reorder a field | Changes the ordinal-to-meaning mapping |
| Change a field's type | Existing wire bytes are misinterpreted |
| Change a field's ordinal number | Direct wire breakage |
| Remove an enum variant | Existing discriminant values become invalid |
| Reorder enum variants | Discriminant values shift |

If a breaking change is truly necessary, **create a new top-level struct**
(e.g. `GnnRankRequestV2`) and increment the `schemaVersion` content field.
Do not alter `@0xd3b45f8ae1c79012`.

## Content Versioning (`schemaVersion` field)

The schema ID identifies the file-level wire format and is fixed. For
application-level content versioning, add a `schemaVersion @N :UInt32`
field to any message that needs it (default `1`). Consumers check this field
and reject or transform messages from unexpected versions. Current L1 messages
omit it — add when the first breaking content change is needed.

## Adding a New Message Type

1. Append the new struct or enum at the **end** of `echidna.capnp`.
2. Add a section-header comment (see existing style).
3. Run `just capnp-gen` to regenerate all language bindings.
4. Update `src/abi/EchidnaABI/CapnSchemas.idr` (see §Idris2 below).
5. If the new type is part of a breaking redesign, bump `schemaVersion` in
   the affected request/response structs rather than changing the schema ID.

## Regenerating Bindings (`just capnp-gen`)

After every schema change — including non-breaking additions — run:

```sh
just capnp-gen
```

This regenerates `src/rust/ipc/echidna_capnp.rs` (and future Zig/Julia targets
as they are wired into the recipe). **Commit generated bindings.** They are
checked in so that consumers without a local `capnp` installation can build.
A CI check (`just capnp-gen-check`) verifies committed bindings match the
schema; failing it is a merge blocker.

## Multi-Language Consumers

| Language | Binding mechanism | Status |
|----------|------------------|--------|
| **Rust** | `capnpc-rust` (generated `echidna_capnp.rs`) | L1 wave 1 target |
| **Idris2** | `src/abi/EchidnaABI/CapnSchemas.idr` — type mirror + proofs | Present; update alongside schema |
| **Julia** | `CapnProto.jl` or Zig C-ABI shim (TBD — see open question in TODO.md) | `src/julia/ipc.jl` stub present |
| **Zig** | C-ABI bridge in `ffi/zig/src/capnp_bridge.zig` | Stub present; real impl in L1 wave 1 |

## Idris2 ABI Proofs (`src/abi/EchidnaABI/CapnSchemas.idr`)

`CapnSchemas.idr` mirrors enum cardinalities and struct field counts as Idris2
types and proves bounded-representation invariants. When adding a field or
enum variant:

1. Add the corresponding constructor to the Idris2 mirror type.
2. Update the `allXxx` Vect witness and its `xxxCountCorrect : length … = n` proof.
3. Re-run `%search` on the `xxxBounded : LTE n 256` proof (it will still hold).
4. Zero `believe_me` is a hard invariant — all proofs must be constructive.

## Quick Reference

```
Safe:    add field at end, add struct, add enum variant at end, rename
Unsafe:  remove, reorder, change type, change ordinal
If breaking: new struct name + increment schemaVersion field
After any change: just capnp-gen && commit generated bindings
Update CapnSchemas.idr to match
```
