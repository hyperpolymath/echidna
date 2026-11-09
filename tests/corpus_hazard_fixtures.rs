// SPDX-License-Identifier: MPL-2.0
//! The intentionally incomplete corpus inputs are detector controls, never
//! proof receipts. Exercise the checked-in files through the real adapters.

use std::path::Path;

use echidna::corpus::{isabelle, minif2f, Corpus};

fn assert_hazard(corpus: &Corpus, name: &str, expected: bool) {
    let entries: Vec<_> = corpus
        .entries
        .iter()
        .filter(|entry| entry.name == name)
        .collect();
    assert_eq!(
        entries.len(),
        1,
        "expected exactly one fixture declaration: {name}"
    );
    assert_eq!(
        entries[0].axiom_usage.sorry, expected,
        "hazard classification: {name}"
    );
}

#[test]
fn isabelle_fixture_keeps_incomplete_proofs_unqualified() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus_fixtures/isabelle");
    let corpus = isabelle::ingest(&root).expect("parse checked-in Isabelle fixture");
    assert_hazard(&corpus, "double_mono", true);
    assert_hazard(&corpus, "double_zero", false);
}

#[test]
fn minif2f_fixture_keeps_incomplete_proofs_unqualified() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus_fixtures/minif2f");
    let corpus = minif2f::ingest(&root).expect("parse checked-in MiniF2F fixture");
    assert_hazard(&corpus, "imo_1959_p1", true);
    assert_hazard(&corpus, "mathd_algebra_42", false);
}
