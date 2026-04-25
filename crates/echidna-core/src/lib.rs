// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA canonical type surface.
//!
//! Holds the types that any client of ECHIDNA (local or over the wire) must
//! agree on: [`core::Term`], [`core::Goal`], [`core::ProofState`],
//! [`core::Tactic`], and the optional [`types::TypeInfo`] decoration.
//!
//! Kept minimal on purpose — only `serde` and `serde_json`. Downstream crates
//! (`echidna` itself, `vcl-ut`, future clients) depend on this crate rather
//! than duplicating the definitions.
//!
//! Internal cross-references (`crate::core::Term`, `crate::types::TypeInfo`)
//! work unchanged because both modules live in this crate.

pub mod core;
pub mod types;
