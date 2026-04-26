// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Coprocessor trust-tier classification.
//!
//! Mirrors the prover `TrustLevel` in `verification/confidence.rs` but for
//! coprocessor dispatch.  A coprocessor's tier governs how MetaController
//! aggregates its answer into the trust-pipeline output: a Tier 5 result
//! can stand on its own; a Tier 2 result must be cross-checked or audited.
//!
//! The ordering is fixed and preserved across the SPARK boundary
//! (`src/ada/spark/coprocessor_safety.ads`) so that no Rust-side change can
//! silently weaken the tier of an already-classified backend.

use serde::{Deserialize, Serialize};

/// Trust tier for a coprocessor backend.
///
/// Strictly ordered: `PureFormal > NativeKernel > LibraryWrapped >
/// JuliaBridged > ExternalSubprocess`.  The `PartialOrd` derivation reflects
/// the variant order, so `assert!(PureFormal > ExternalSubprocess)` holds.
///
/// The discriminants are pinned (`repr(u8)`) because the SPARK and Idris2
/// ABI layers consume them as raw bytes.  Reordering is an ABI break.
#[repr(u8)]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub enum CoprocessorTrustTier {
    /// Tier 5 — answer is constructively certified at the type level.
    /// Used when the op is dispatched through a path with an Idris2 ABI
    /// proof that the input/output shape is correct *and* a Coq/Lean
    /// kernel-level proof of the mathematical fact.  Reserved for Phase 7
    /// MetaController integration.
    PureFormal = 5,

    /// Tier 4 — implementation is in SPARK and proved by GNATprove.
    /// Currently used by the axiom-policy enforcement path (see
    /// `axiom_policy.ads`).  Coprocessor ops will earn this tier once the
    /// Phase 6 native-kernel SPARK layer lands.
    NativeKernel = 4,

    /// Tier 3 — call into a vetted, statically-versioned library with a
    /// permissive licence (FLINT, our own `num-bigint` build, etc.) under
    /// a thin Rust wrapper.  The current `Math` backend lives here.
    LibraryWrapped = 3,

    /// Tier 2 — call traverses the Rust ↔ Julia bridge to reach a backend
    /// implemented in Julia (LowLevel.jl, ProvenCrypto.jl, …).  Bridge
    /// failures degrade gracefully; correctness depends on the Julia code.
    JuliaBridged = 2,

    /// Tier 1 — call shells out to an external subprocess (Sage, GAP,
    /// Maxima, KeYmaera X, …).  Result must be cross-checked or wrapped in
    /// a re-verification step before being trusted in a high-trust pipeline.
    ExternalSubprocess = 1,
}

impl CoprocessorTrustTier {
    /// Numeric encoding for FFI / SPARK / Idris2.  Preserves the tier order.
    pub fn as_u8(self) -> u8 {
        self as u8
    }

    /// Whether this tier suffices for the prover-side trust-hardening
    /// pipeline (`dispatch.rs`) to accept a coprocessor result without an
    /// independent cross-check.  Tier 3 and above qualify; Tier 2 and Tier
    /// 1 require cross-validation, matching the prover-side rule that
    /// non-small-kernel single-prover results never reach Level 5.
    pub fn is_self_sufficient(self) -> bool {
        self >= CoprocessorTrustTier::LibraryWrapped
    }
}
