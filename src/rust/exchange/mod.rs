// SPDX-License-Identifier: MPL-2.0

//! Cross-prover proof exchange module
//!
//! Supports importing and exporting proofs in universal formats:
//! - OpenTheory (HOL family cross-checking)
//! - Dedukti/Lambdapi (universal proof format)
//! - SMTCoq bridge (SMT proofs replayed in Coq)

pub mod dedukti;
pub mod opentheory;

pub use dedukti::DeduktiExporter;
pub use opentheory::OpenTheoryExporter;
