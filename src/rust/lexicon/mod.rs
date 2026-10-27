// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Lexicon tooling that works *on* corpora rather than on one synonym table.
//!
//! The synonym tables themselves (`data/synonyms/*.toml`, loaded by
//! [`crate::suggest::synonyms`]) are curated by hand under the Nickel
//! contract `data/synonyms/schema.ncl`. This module only *proposes*: it
//! mines the training corpora for rows a curator may want to add, and every
//! proposal carries `evidence = none` (owner decision D4 in
//! `docs/decisions/2026-10-19-lexicon-v2-and-identity-arbitration.adoc`).

pub mod scan;
