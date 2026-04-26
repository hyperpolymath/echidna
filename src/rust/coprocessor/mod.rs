// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Coprocessor abstraction.
//!
//! Companion to the prover backend system: where `ProverBackend` represents
//! a discrete *theorem* engine that consumes a `ProofState` and emits a
//! verdict, `Coprocessor` represents a *computation* engine that consumes a
//! `CoprocessorOp` and emits a `CoprocessorOutcome`.  Coprocessors serve
//! provers (for example: factoring a modulus that the SMT theory of
//! arithmetic cannot decide alone) and the meta-controller (for example:
//! tensor / vector ops backing GNN-guided proof search).
//!
//! Currently provided:
//! - `Math` backend (in-process, Rust + `num-bigint` family).
//! - Generic `JuliaCoprocessorBridge` transport for any Julia-side backend
//!   that registers at `http://127.0.0.1:8090/coprocessor/dispatch`.
//!
//! Planned (Phase 6, each landing with its full implementation — never as
//! a stub):
//! - `Physics`   — integration with InvestigativeJournalist.jl numerics
//! - `Dsp`       — DSP.jl + LowLevel.jl
//! - `Fpga`      — Yosys/Verilator integration via `ffi/zig`
//! - `Tensor`    — Tensors.jl + StaticArrays
//! - `Vector`    — Rust `std::simd` portable SIMD
//! - `Crypto`    — ProvenCrypto.jl + RustCrypto under SPARK boundary
//! - `Graphics`  — wgpu compute path
//! - `Audio`     — DSP.jl audio extensions
//! - `Io`        — LowLevel.jl IOPU
//!
//! Each variant lands in its own commit with a fully working implementation,
//! tests, capability declaration, trust tier classification, and Idris2 ABI
//! entry — never with `unimplemented!()` placeholders.
//!
//! The trust pipeline (`dispatch.rs`) consults the coprocessor's trust tier
//! when folding a coprocessor result into a prover-side trust calculation;
//! see `coprocessor::trust::CoprocessorTrustTier`.

use anyhow::Result;
use async_trait::async_trait;

pub mod crypto;
pub mod julia_bridge;
pub mod math;
pub mod physics;
pub mod tensor;
pub mod trust;
pub mod types;
pub mod vector;

pub use crypto::CryptoBackend;
pub use julia_bridge::JuliaCoprocessorBridge;
pub use math::MathBackend;
pub use physics::PhysicsBackend;
pub use tensor::TensorBackend;
pub use trust::CoprocessorTrustTier;
pub use types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
pub use vector::VectorBackend;

/// Universal coprocessor backend trait.
///
/// Mirrors the shape of `ProverBackend` (small, async, factory-constructed)
/// but operates on `CoprocessorOp` rather than `ProofState`.
#[async_trait]
pub trait Coprocessor: Send + Sync {
    /// Which kind of coprocessor this backend implements.
    fn kind(&self) -> CoprocessorKind;

    /// Self-reported capabilities — used by `MetaController` to avoid
    /// dispatching ops to backends that don't support them.
    fn capabilities(&self) -> &CoprocessorCapabilities;

    /// Current liveness.  Bridges to external runtimes update this from
    /// `probe()` calls; pure in-process backends usually return `Healthy`.
    fn health(&self) -> CoprocessorHealth;

    /// Trust tier.  See `CoprocessorTrustTier` for the ladder.
    fn trust_tier(&self) -> CoprocessorTrustTier;

    /// Dispatch an op.  On a `Failure` outcome the op was well-formed but
    /// the backend declined to or could not produce an answer; on `Err`
    /// the transport itself failed.
    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome>;
}

/// Factory mirroring `ProverFactory`.
///
/// Phase 0 only constructs the `Math` backend natively.  Phase 6 backends
/// add their own arms here as they land.  The Julia bridge is constructed
/// separately because it parameterises by the *Julia-side* backend kind,
/// not by a fixed Rust impl.
pub struct CoprocessorFactory;

impl CoprocessorFactory {
    /// Construct a native (Rust) coprocessor by kind.
    ///
    /// Returns `None` when the requested kind has no native Rust backend
    /// — caller should fall through to a Julia bridge or external
    /// subprocess backend in Phases 6-7.
    pub fn native(kind: CoprocessorKind) -> Option<Box<dyn Coprocessor>> {
        match kind {
            CoprocessorKind::Math => Some(Box::new(MathBackend::new())),
            CoprocessorKind::Vector => Some(Box::new(VectorBackend::new())),
            CoprocessorKind::Tensor => Some(Box::new(TensorBackend::new())),
            CoprocessorKind::Crypto => Some(Box::new(CryptoBackend::new())),
            CoprocessorKind::Physics => Some(Box::new(PhysicsBackend::new())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn factory_constructs_math() {
        let backend = CoprocessorFactory::native(CoprocessorKind::Math)
            .expect("Math backend always available");
        assert_eq!(backend.kind(), CoprocessorKind::Math);
        assert_eq!(backend.health(), CoprocessorHealth::Healthy);
        assert_eq!(backend.trust_tier(), CoprocessorTrustTier::LibraryWrapped);
    }

    #[tokio::test]
    async fn math_round_trip_via_factory() {
        let backend = CoprocessorFactory::native(CoprocessorKind::Math).unwrap();
        let outcome = backend
            .dispatch(CoprocessorOp::BigIntGcd {
                a: "48".into(),
                b: "18".into(),
            })
            .await
            .unwrap();
        match outcome {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "6"),
            _ => panic!("unexpected outcome"),
        }
    }

    #[test]
    fn trust_tier_ordering() {
        // Sanity check the tier ladder.
        assert!(CoprocessorTrustTier::PureFormal > CoprocessorTrustTier::NativeKernel);
        assert!(
            CoprocessorTrustTier::NativeKernel > CoprocessorTrustTier::LibraryWrapped
        );
        assert!(
            CoprocessorTrustTier::LibraryWrapped > CoprocessorTrustTier::JuliaBridged
        );
        assert!(
            CoprocessorTrustTier::JuliaBridged
                > CoprocessorTrustTier::ExternalSubprocess
        );
        assert!(CoprocessorTrustTier::LibraryWrapped.is_self_sufficient());
        assert!(!CoprocessorTrustTier::JuliaBridged.is_self_sufficient());
    }
}
