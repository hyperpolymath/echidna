// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Cross-prover proof exchange module
//!
//! Supports importing and exporting proofs in universal formats:
//! - OpenTheory (HOL family cross-checking)
//! - Dedukti/Lambdapi (universal proof format)
//! - SMTCoq bridge (SMT proofs replayed in Coq)

pub mod dedukti;
pub mod opentheory;
pub mod tptp;
pub mod smtlib;
pub mod smtcoq;
pub mod lambdapi;

pub use dedukti::DeduktiExporter;
pub use opentheory::OpenTheoryExporter;
