<!--
SPDX-License-Identifier: PMPL-1.0-or-later
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
