<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-->

# FFI Boundary Audit

**Auditor**: Jonathan D.A. Jewell  
**Date**: 2026-04-26  
**Scope**: all `unsafe` blocks in the echidna Zig/SPARK/Chapel FFI boundary

---

## §1 — `src/rust/ffi/mod.rs` (UnsafeCode, ResourceLeak)

The ffi/mod.rs module exports 24 documented `unsafe` blocks for the Zig FFI
layer.  Each unsafe block has an inline `// SAFETY:` comment.  The patterns:

- **C-ABI exports** (`pub unsafe extern "C" fn …`) — required by Zig and
  any C consumer to call Rust across the ABI boundary.
- **Raw pointer → Rust reference** (`CStr::from_ptr`, `slice::from_raw_parts`)
  — caller contract: non-null, correctly-aligned, valid-lifetime pointer
  supplied by the Zig shim (enforced by the Zig wrapper in `src/zig_ffi/`).
- **ResourceLeak**: The one finding is a raw pointer returned from
  `Box::into_raw`; the callee (Zig side) owns the allocation and calls
  `rust_free_*` to drop it.  This is the standard Rust→C ownership-transfer
  pattern, not an actual leak.

**Classification**: legitimate FFI.  No remediation required.

---

## §2 — `src/rust/ffi/spark_axiom.rs` (UnsafeCode)

Two `extern "C"` callouts to SPARK-compiled policy enforcement routines
(`echidna_spark_enforce_policy`, `echidna_spark_worst_danger`,
`echidna_spark_max_usages`).  The module docstring confirms:

- Never passes null — `slice.as_ptr()` on a non-empty slice is always non-null.
- Length is bounded by `wire.len()` which comes from a bounded Vec.
- SPARK-side preconditions checked with Ada contracts.

**Classification**: legitimate FFI (Rust→SPARK via C ABI).  No remediation required.

---

## §3 — `src/rust/proof_search.rs` (UnsafeCode, feature-gated Chapel)

Seven unsafe blocks, ALL behind `#[cfg(feature = "chapel")]`.  Patterns:

- `CString::new(goal).context(…)` — only unsafe via the `extern "C"` call site.
- `CStr::from_ptr` on Chapel-returned strings — caller contract: Chapel runtime
  guarantees null-terminated string lifetime until next Chapel call.
- `extern "C"` callouts to the Chapel parallel search runtime.

If `chapel` feature is not enabled, no unsafe code compiles in.

**Classification**: legitimate FFI (Rust→Chapel via Zig shim, feature-gated).  No remediation required.

---

## §4 — `src/interfaces/*/ffi_wrapper.rs` (UnsafeCode × 6)

The three interface crates (graphql, grpc, rest) each contain an `ffi_wrapper.rs`
that calls into the core Rust FFI layer via `CStr`/`CString` and raw pointer
manipulation.  All six findings are structurally identical to §1 — they are
wrappers that adapt the C-ABI output of `src/rust/ffi/mod.rs` to Rust-safe
types for the interface handlers.

**Classification**: legitimate FFI (interface-layer wrappers over §1 boundary).  No remediation required.

---

## §5 — `src/rust/provers/z3.rs` (UnsafeCode, PanicPath)

No actual `unsafe` blocks present.  panic-attack reports:
- **unwrap_calls**: 18 × `unwrap_or_else()` in parser recovery (lines 119, 125, 215) — normal S-expression parser fallback patterns
- **allocations**: 54 units for proof state and SMT-LIB parsing buffers

The parser `.expect(token)` method calls (lines 727+) are parser combinators
that return `Result`, not panic sites.  Error propagation via `?` operator.

**Classification**: legitimate SMT solver backend implementation.  No remediation required.

---

## §6 — `src/rust/provers/pvs.rs` (UnsafeCode)

Large PVS (Prototype Verification System) backend: 3168 LoC, 105 variants for
PVSExpr, PVSType, and proof state handling.  No `unsafe` blocks present.

panic-attack reports:
- **allocations**: 204 units for recursive AST construction (record expressions,
  lambda bindings, quantifiers, case selections — see lines 46-100).
- **file_size**: 5 units (normal for a full prover backend).

The large allocations are expected: PVS is a rich type system with dependent
types, predicate subtypes, and complex pattern matching.

**Classification**: legitimate proof assistant backend.  No remediation required.

---

## §7 — `src/rust/provers/hol4.rs` (UnsafeCode, PanicPath)

Large HOL4 (Higher-Order Logic) backend: 2621 LoC, with tactic evaluation,
type parser, and bidirectional proof state conversion.  No `unsafe` blocks.

panic-attack reports:
- **panic_sites**: 1 from process spawn error (line 1430 `.spawn()`), reported but
  error is caught and propagated via `?` operator.
- **allocations**: 174 units for HOL4 tactic vectors (`Metis(vec![])`,
  `Simp(vec![])`) and bidirectional term conversion (lines 1644-1738).

All struct-to-vec conversions return `Result`, no panic on unwrap.

**Classification**: legitimate proof assistant backend.  No remediation required.

---

## §8 — `src/rust/provers/mod.rs` (UnsafeCode)

Central prover module: 105 prover backends, module declarations (lines 22-94),
ProverKind enum (96+ variants), and ProverFactory dispatch logic.  No `unsafe` blocks.

panic-attack reports:
- **allocations**: 148 units from enum variants and module exports.
- **file_size**: 3 units (normal for a registry file).

This is structural overhead from the 105-prover architecture, not FFI or
memory mismanagement.

**Classification**: legitimate backend registry.  No remediation required.

---

## §9 — `src/rust/coprocessor/flint.rs` (UnsafeCode × 17) — FLINT C bigint bindings

**Added**: 2026-06-01 (post-#104 panic-attack re-sweep, issue #177)

FLINT (Fast Library for Number Theory, LGPL-3) is the only CAS backend in
ECHIDNA that links the library in-process rather than shelling out (earning
`CoprocessorTrustTier::LibraryWrapped`, Tier 3).  Feature-gated via
`--features flint`; without it the module compiles out entirely and
`CoprocessorFactory::native(CoprocessorKind::FlintMath)` returns `None`.

The 17 `unsafe` blocks (lines 145, 158, 168, 172, 173, 180, 199, 204, 214,
233, 251, 327, 335, 349, 356, 366, 376) fall into four well-bounded patterns:

- **`fmpz_init` / `fmpz_clear` / `fmpz_poly_init` / `fmpz_poly_clear`**:
  RAII bookkeeping — each `Fmpz` / `FmpzPoly` Rust wrapper owns exactly one
  FLINT object; `Drop` runs `fmpz_clear` / `fmpz_poly_clear` exactly once.
  Pointers passed are always `&mut self.inner`, never null, never aliased
  (Rust's borrow checker prevents the latter).
- **`fmpz_set_str` / `fmpz_get_str`**: string round-trip through CString /
  CStr.  Inputs are validated CStrings (no interior nul); outputs are
  immediately copied into owned `String` and the FLINT-allocated buffer is
  released via `flint_free` (line 173) — no leak, no use-after-free.
- **`fmpz_poly_*` arithmetic** (`gcd`, `mul`, `pseudo_rem`, `content`,
  `set_coeff_fmpz`, `get_coeff_fmpz`, `length`): all called on `&mut`
  pointers to RAII-owned `FmpzPolyStruct` instances created on the same
  blocking thread, used, and dropped before the thread returns.
- **`fmpz_root` / `fmpz_bin_uiui`**: integer k-th root and binomial.
  Input bounds (`n`, `k` as `u64`) are validated by callers before the
  FFI call; FLINT itself returns 0/1 status to indicate exact-vs-approximate
  result (line 366: `exact = fmpz_root(...)`).

**Thread safety**: FLINT is thread-safe from version 2.4 onwards provided
each thread owns its `fmpz` / `fmpz_poly` instances exclusively.  All FLINT
objects in this module are created on the blocking thread, used, and dropped
before the thread returns — no sharing occurs (module docstring lines 38-43).

**Type-layout invariants**: `FmpzPolyStruct` (`#[repr(C)]`, lines 75-80) is
a faithful mirror of FLINT's `fmpz_poly_struct` on 64-bit Linux (3 pointer-
sized fields, 24 bytes).  We never read or write the fields directly — all
access goes through FLINT functions (lines 73-74 docstring).

**Classification**: legitimate FFI (Rust→FLINT C library via in-process
linkage, feature-gated).  No remediation required.

---

## §10 — Zig FFI bridges (`src/zig/ffi/axiom_spark_bridge.zig`, `src/zig_ffi/chapel_bridge.zig`) — UnsafeFFI × 2

**Added**: 2026-06-01 (post-#104 panic-attack re-sweep, issue #177)

Two Zig modules that bridge between two non-Rust backends (SPARK/Ada and
Chapel) and the Rust FFI surface.  Each contains exactly one `@cImport`
directive — the only construct panic-attack flags as `UnsafeFFI` for Zig.

### §10.1 — `src/zig/ffi/axiom_spark_bridge.zig`

Zig C-ABI shim over the SPARK axiom-policy layer, sitting between the
Ada/SPARK static library (`libechidna_spark.a`) and the Rust FFI surface
defined in `src/rust/ffi/spark_axiom.rs` (already audited in §2).

```
SPARK/Ada (axiom_policy.ads/.adb)
  → C exports (axiom_c_bridge.ads/.adb: echidna_spark_enforce_policy_inner)
  → this Zig shim (input validation + C-ABI re-export)
  → Rust extern "C" (src/rust/ffi/spark_axiom.rs)
```

The `@cImport({})` (line 20) is intentionally empty — the shim's job is to
re-export the SPARK symbols with predictable C ABI (no name mangling,
predictable layout) and provide a compile-time `MAX_USAGES = 1024` size
assertion that Rust's `bindgen` cannot see across the Ada boundary
(module header, lines 4-17).

Safety invariants:
- `danger_levels: [*]const u8` + `count: usize` is the standard
  pointer+length C slice; validated non-empty before crossing the Rust
  boundary in `spark_axiom.rs` (see §2).
- Output `policy_out` / `status_out` are `*i32` to caller-allocated
  storage; the Ada side guarantees they are always written before the
  call returns (SPARK contract).

### §10.2 — `src/zig_ffi/chapel_bridge.zig`

Type-safe Zig bridge between Chapel's parallel-search runtime and the
Rust FFI surface, gated by the `chapel` Cargo feature (see §3).

```
Chapel (C API: chapel_ffi_exports.h)
  → Zig (@cImport, this module)
  → Rust (safe calls via src/rust/proof_search.rs)
```

The `@cImport({ @cInclude("chapel_ffi_exports.h"); })` (lines 18-20) pulls
in the Chapel-exported C declarations for 30 prover backends.  The Zig
wrappers (`ProverKind`, `ProverCategory`, `ProofResult`) translate
Chapel's C types into Zig-safe enums and structs, owning all string copies
(`fromChapel` at line 143 takes `std.mem.Allocator` and copies before
returning).

Safety invariants:
- Enum-from-int boundaries are bounds-checked (line 156: `c_result.prover_id
  >= 0 and c_result.prover_id < @as(c_int, ProverKind.count)` before
  `@enumFromInt`).
- All string references returned from Chapel are copied into Zig-owned
  storage before the Chapel call returns (per module header line 7).
- Chapel runtime guarantees null-terminated string lifetime until next
  Chapel call (see §3 for the corresponding Rust-side contract).

**Classification (both files)**: legitimate FFI (Zig bridge layer between
Ada/SPARK & Chapel backends and Rust core; both feature-gated).  No
remediation required.

---

## §11 — `ffi/zig/src/*` overlay layer (UnsafeCode × 3) — pointer casts on static error buffers

**Added**: 2026-06-01 (post-#104 panic-attack re-sweep, issue #177)

Three Zig modules in the `ffi/zig/src/` overlay (the Idris2-ABI → Zig-FFI →
C-ABI surface for BoJ cartridges, the overlay subsystem, and the TypeLL
type-language) each contain exactly one `@ptrCast` flagged by panic-attack
as `UnsafeCode`.

| File                         | Line | Function                              |
|------------------------------|------|---------------------------------------|
| `ffi/zig/src/boj.zig`        | 456  | `echidna_boj_last_error`              |
| `ffi/zig/src/overlay.zig`    | 684  | `echidna_overlay_last_error`          |
| `ffi/zig/src/typell.zig`     | 333  | `echidna_typell_last_error`           |

All three are the **identical pattern**: a `last_error` getter that returns
a C-ABI null-terminated string pointer to a module-private static error
buffer:

```zig
pub export fn echidna_<subsystem>_last_error() ?[*:0]const u8 {
    if (error_len == 0) return null;
    return @ptrCast(&error_buf);
}
```

Where `error_buf: [ERROR_BUF_SIZE]u8` (typically 512 bytes) is a
module-private static array and `error_len: usize` is its current
fill-length.

Safety invariants:
- `error_buf` is module-static — its address is fixed at program load and
  never freed; the returned pointer is always valid for the program
  lifetime.
- The cast is from `*[N]u8` (array reference) to `[*:0]const u8`
  (sentinel-terminated many-item pointer); the buffer is guaranteed to
  contain a trailing nul because all writers (`setError` helpers in each
  module) explicitly write a nul terminator before incrementing
  `error_len`.
- Return type is `?[*:0]const u8` (optional); a null-fast-path
  (`if (error_len == 0) return null;`) guards against returning a pointer
  to an empty buffer, so consumers can distinguish "no error" from
  "empty-string error".
- Read-only on the Rust/Idris2 side — the pointer is `const`; callers
  must not write through it.

**Concurrency note**: the static error buffer is not thread-safe; each
subsystem's contract is that errors are read on the same thread that
triggered them (consistent with the "BoJ client" / "overlay" / "TypeLL"
single-threaded request-response model).  Multi-threaded callers must
serialise error retrieval externally.

**Classification**: legitimate FFI (idiomatic C-style `last_error` getters
for three FFI subsystems sharing a common pattern).  No remediation required.
