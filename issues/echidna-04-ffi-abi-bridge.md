<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# ECH-04: feat(ffi): C-ABI / Zig bridge specification for embedding ParadisEO metaheuristics engine with Idris2 contracts

- **Repository:** hyperpolymath/echidna
- **Labels:** enhancement, area:abi, zig, idris2, ffi
- **Area:** ABI / FFI / Multi-Language

## Summary

Write the specification for a C-ABI boundary through which a metaheuristics engine (ParadisEO or a compatible implementation) can be called from ECHIDNA's Rust core, with the Zig layer as the bridge and Idris2 providing the contracts. This issue is a **specification and a minimal proof-of-boundary**, not a full integration.

## Context

- `src/abi/` holds the Idris2 ABI (`echidnaabi.ipkg`, `EchidnaABI/`, `Types.idr`, `Layout.idr`, and per-subsystem `*Foreign.idr` modules such as `CoprocessorForeign.idr`, `OverlayForeign.idr`, `TentaclesForeign.idr`).
- `ffi/zig/` (`build.zig`, `src/main.zig`, `src/boj.zig`, `src/capnp_bridge.zig`, `src/provers/`) and `src/zig_ffi/` (`chapel_bridge.zig`, `chapel_ffi_exports.h`) are the existing Zig bridges.
- `CLAUDE.md` states that Idris2 ABI modules must have zero `believe_me`, zero postulates and zero admits, enforced by `idris2-abi-ci.yml`. The specification must satisfy the same gate.
- The Rust side has an existing `src/rust/ffi/` module. Reuse its conventions for pointer ownership and error codes.
- No ParadisEO code is present in the repository. Its licence must be checked before any source or binary is vendored or linked.

## Proposed Work

1. **Specification document** (`docs/design/` or `src/abi/`, consistent with existing ABI docs) defining:
   - The minimal call surface: create engine, configure (algorithm id, parameters, seed), step / run with budget, query best solutions, destroy.
   - Data layout for objective vectors and candidate identifiers, with explicit sizes and alignment, and a version field.
   - Ownership rules: who allocates, who frees, lifetimes across the boundary.
   - Error model: integer status codes mapped to a closed Idris2 sum type.
2. **Idris2 contracts** in `src/abi/` (new module, e.g. `MetaheuristicsForeign.idr`):
   - Total functions for layout size/alignment computation.
   - Proofs that status-code mapping is total and that every handle is destroyed at most once (typed handle state, or a linear-style discipline if supported by the Idris2 version in use).
   - No `believe_me`, postulates or admits.
3. **Zig bridge skeleton** in `ffi/zig/src/` exporting the specified symbols with a stub implementation (no external engine linked). Symbols must match the Idris2 declarations exactly.
4. **Rust side**: an `extern "C"` declaration module plus a test that calls the stub through the bridge and checks the status-code round-trip.

## Acceptance Criteria

- [ ] Specification states every exported symbol, its C signature, ownership and error behaviour.
- [ ] `idris2` type-checks the new ABI module with zero holes, zero `believe_me`, zero postulates and zero admits.
- [ ] Layout proofs cover the objective-vector record: size and alignment match the Zig `extern struct` and the Rust `#[repr(C)]` type (checked by a test or static assertion).
- [ ] Zig build (`ffi/zig/build.zig`) produces the stub library; `zig build test` passes.
- [ ] Rust test links the stub and round-trips at least one call per status code.
- [ ] Existing `idris2-abi-ci.yml` gate passes.
- [ ] No ParadisEO source or binary is added to the repository.

## Out of Scope

- Linking a real ParadisEO build.
- Cross-language memory sharing beyond the specified layouts.
- Performance tuning of the boundary.

## Open Questions

- Is ParadisEO's licence compatible with the repository's MPL-2.0 licence for linking, and does that affect whether the bridge can ship in-tree?
- Should the engine boundary reuse the existing `ffi/zig` naming, or live in a new `ffi/metaheuristics/` directory?
