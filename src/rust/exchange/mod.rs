// SPDX-License-Identifier: PMPL-1.0-or-later

//! Cross-prover proof exchange module
//!
//! Supports importing and exporting proofs in universal formats:
//! - OpenTheory (HOL family cross-checking)
//! - Dedukti/Lambdapi (universal proof format)
//! - SMTCoq bridge (SMT proofs replayed in Coq)

pub mod opentheory;
pub mod dedukti;

pub use opentheory::OpenTheoryExporter;
pub use dedukti::DeduktiExporter;
