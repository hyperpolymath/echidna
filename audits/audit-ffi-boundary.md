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
