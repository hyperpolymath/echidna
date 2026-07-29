// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Cross-prover proof exchange module
//!
//! Supports importing and exporting proofs in universal formats:
//! - OpenTheory (HOL family cross-checking)
//! - Dedukti/Lambdapi (universal proof format)
//! - SMTCoq bridge (SMT proofs replayed in Coq)
//!
//! ## Saturation campaign 2026-06-01
//!
//! Four new bridges added: `tptp`, `smtlib`, `smtcoq`, `lambdapi`.
//! Each defines a local `ExchangeError` enum (isomorphic across the
//! four). Consolidation to a single shared error type is deferred —
//! the four enums share an identical variant set, so cross-bridge
//! interop just needs a small `From` impl wherever a downstream call
//! converts between them. See
//! `docs/decisions/2026-06-01-saturation-campaign.md`.

pub mod dedukti;
pub mod lambdapi;
pub mod opentheory;
pub mod smtcoq;
pub mod smtlib;
pub mod tptp;

pub use dedukti::DeduktiExporter;
pub use opentheory::OpenTheoryExporter;
