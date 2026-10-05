// SPDX-License-Identifier: MPL-2.0

//! ECHIDNA canonical type surface.
//!
//! Holds the types that any client of ECHIDNA (local or over the wire) must
//! agree on:
//!
//! - [`core::Term`], [`core::Goal`], [`core::ProofState`], [`core::Tactic`]
//!   and the optional [`types::TypeInfo`] decoration;
//! - [`prover_kind::ProverKind`], the backend enumeration;
//! - [`prove_result::ProveResult`], the `echidna.prove.result/1` contract
//!   printed by `echidna prove --output json`;
//! - [`trust`], the trust kernel (trust levels, axiom scanner), re-exported
//!   from `echidna-core-creusot`.
//!
//! Kept small on purpose. Downstream crates (`echidna` itself, `vcl-ut`,
//! echidnabot, proof-burrower) depend on this crate rather than duplicating
//! the definitions. See `crates/echidna-core/README.adoc` for the stability
//! policy and the git-dependency recipe.
//!
//! Internal cross-references (`crate::core::Term`, `crate::types::TypeInfo`)
//! work unchanged because both modules live in this crate.

pub mod core;
pub mod prove_result;
pub mod prover_kind;
pub mod types;

/// The ECHIDNA trust kernel: [`trust::TrustLevel`], [`trust::compute_trust_level`],
/// [`trust::axiom_tracker`] and [`trust::pareto`].
///
/// Re-exported unchanged from `echidna-core-creusot`. Its Creusot
/// annotations are stated, not proved; the stable-Rust tests mirror them.
pub mod trust {
    pub use echidna_core_creusot::*;
}

pub use prove_result::{ProveResult, ProveStatus, ProveTrust};
pub use prover_kind::ProverKind;
