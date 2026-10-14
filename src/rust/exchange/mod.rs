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
//! `docs/decisions/2026-06-01-saturation-campaign.adoc`.

pub mod dedukti;
pub mod lambdapi;
pub mod opentheory;
pub mod smtcoq;
pub mod smtlib;
pub mod tptp;

pub use dedukti::DeduktiExporter;
pub use opentheory::OpenTheoryExporter;

use serde::{Deserialize, Serialize};

/// The exchange-layer formats a cross-prover translation can go through
/// — one per bridge module above. Named by a `KernelTranslation`
/// fidelity certificate (`crate::verification::result_arbiter`, ECH-05).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExchangeFormat {
    OpenTheory,
    Dedukti,
    Lambdapi,
    Tptp,
    SmtLib,
    SmtCoq,
}

impl ExchangeFormat {
    /// Stable tag used for domain separation in [`term_hash`].
    pub fn tag(self) -> &'static str {
        match self {
            ExchangeFormat::OpenTheory => "opentheory",
            ExchangeFormat::Dedukti => "dedukti",
            ExchangeFormat::Lambdapi => "lambdapi",
            ExchangeFormat::Tptp => "tptp",
            ExchangeFormat::SmtLib => "smtlib",
            ExchangeFormat::SmtCoq => "smtcoq",
        }
    }
}

/// BLAKE3 identity of an exchange-layer term, hex-encoded.
///
/// The hash is domain-separated by `format`, so equal hashes imply the
/// same format as well as the same term text. It is taken over the term
/// *as rendered*: no canonicalisation (that is roadmap stage 6c), so two
/// renderings of α-equivalent terms hash differently. The failure mode
/// is therefore a missed `sound` level in arbitration, never a false one.
pub fn term_hash(format: ExchangeFormat, term: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"echidna/exchange-term/v1\0");
    hasher.update(format.tag().as_bytes());
    hasher.update(b"\0");
    hasher.update(term.as_bytes());
    hasher.finalize().to_hex().to_string()
}

#[cfg(test)]
mod term_hash_tests {
    use super::*;

    #[test]
    fn term_hash_is_deterministic_and_format_separated() {
        let t = "forall (n : nat), eq nat (add n zero) n";
        assert_eq!(
            term_hash(ExchangeFormat::Dedukti, t),
            term_hash(ExchangeFormat::Dedukti, t)
        );
        assert_ne!(
            term_hash(ExchangeFormat::Dedukti, t),
            term_hash(ExchangeFormat::Lambdapi, t)
        );
        assert_ne!(
            term_hash(ExchangeFormat::Dedukti, t),
            term_hash(ExchangeFormat::Dedukti, "forall (n : nat), eq nat n n")
        );
        assert_eq!(term_hash(ExchangeFormat::Tptp, t).len(), 64);
    }
}
