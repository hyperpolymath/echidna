// SPDX-License-Identifier: MPL-2.0

//! End-to-end ingest of the estate-language adapters over the checked-in
//! smoke fixtures.
//!
//! The unit tests in `corpus::spark_ada` / `corpus::creusot` parse source
//! strings; this drives the public `ingest(root)` entry point so the
//! walking, module naming and corpus assembly are exercised too. It is
//! the test that would have caught a fixture that parses but walks badly.

use std::path::{Path, PathBuf};

use echidna::corpus::{creusot, spark_ada, Corpus, CorpusEntry};

fn fixtures(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus_fixtures")
        .join(name)
}

fn find<'a>(corpus: &'a Corpus, name: &str) -> Vec<&'a CorpusEntry> {
    corpus.entries.iter().filter(|e| e.name == name).collect()
}

#[test]
fn spark_ada_fixture_ingests_with_hazards() {
    let corpus = spark_ada::ingest(&fixtures("spark_ada")).expect("spark_ada ingest");
    assert_eq!(corpus.adapter, "spark_ada");
    assert_eq!(corpus.modules.len(), 2, "spec + body are two files");

    // Clamp's contract (from the `.ads`) and proof (from the `.adb`) are
    // paired into one entry.
    let clamp = find(&corpus, "Clamp");
    assert_eq!(clamp.len(), 1, "spec/body must pair: {}", clamp.len());
    assert!(clamp[0].statement.contains("Pre => Lo <= Hi"));
    assert!(clamp[0].proof.is_some());
    assert!(!clamp[0].axiom_usage.any(), "Clamp must be hazard-free");

    // The sparklib lemma convention.
    let lemma = find(&corpus, "Lemma_Clamp_Bounds");
    assert_eq!(lemma.len(), 1, "lemma spec/body must pair");
    assert!(lemma[0]
        .axiom_usage
        .other
        .iter()
        .any(|t| t == "sparklib:lemma"));

    // The trusted step: `pragma Assume` in the body.
    let trusted = find(&corpus, "Trusted_Step");
    assert_eq!(trusted.len(), 1);
    assert!(
        trusted[0].axiom_usage.postulate,
        "pragma Assume must surface as a postulate"
    );

    // A plain type declaration still lands in the index.
    assert_eq!(find(&corpus, "Word").len(), 1);
}

#[test]
fn spark_ada_reports_spark_syntax_on_the_module() {
    let corpus = spark_ada::ingest(&fixtures("spark_ada")).expect("spark_ada ingest");
    assert!(
        corpus
            .modules
            .iter()
            .any(|m| m.options.iter().any(|o| o == "SPARK" || o == "SPARK_Mode")),
        "the spec file carries contracts, so it should be marked SPARK"
    );
    assert!(corpus.modules.iter().any(|m| m.name == "Smoke"));
}

#[test]
fn creusot_fixture_ingests_with_contracts_and_trust() {
    let corpus = creusot::ingest(&fixtures("creusot")).expect("creusot ingest");
    assert_eq!(corpus.adapter, "creusot");
    assert_eq!(corpus.modules.len(), 1);

    let inc = find(&corpus, "increment");
    assert_eq!(inc.len(), 1);
    assert!(inc[0].statement.contains("#[requires(x@ < 1000)]"));
    assert!(inc[0].statement.contains("#[ensures(result@ == x@ + 1)]"));
    assert_eq!(inc[0].proof.as_deref(), Some("x + 1"));
    assert!(
        !inc[0].axiom_usage.postulate,
        "a contract is not a postulate: increment is proved, not trusted"
    );
    assert!(inc[0]
        .axiom_usage
        .other
        .iter()
        .any(|t| t == "creusot:requires"));
    assert!(inc[0]
        .axiom_usage
        .other
        .iter()
        .any(|t| t == "creusot:ensures"));

    let trusted = find(&corpus, "trusted_identity");
    assert_eq!(trusted.len(), 1);
    assert!(
        trusted[0].axiom_usage.postulate,
        "#[trusted] must surface as a postulate"
    );

    let double = find(&corpus, "double");
    assert_eq!(double.len(), 1);
    assert!(double[0].axiom_usage.other.iter().any(|t| t == "creusot:logic"));
    assert!(double[0]
        .axiom_usage
        .other
        .iter()
        .any(|t| t == "creusot:pearlite"));

    assert_eq!(find(&corpus, "Counter").len(), 1, "struct is indexed");
    assert!(
        find(&corpus, "not_part_of_the_proved_surface").is_empty(),
        "#[test] functions are not part of the proved surface"
    );
}

#[test]
fn creusot_module_name_follows_the_source_path() {
    let corpus = creusot::ingest(&fixtures("creusot")).expect("creusot ingest");
    assert_eq!(corpus.modules[0].name, "smoke");
    assert!(corpus.by_qualified.contains_key("smoke.increment"));
}

#[test]
fn discipline_tags_survive_the_hazard_pipeline() {
    let corpus = spark_ada::ingest(&fixtures("spark_ada")).expect("spark_ada ingest");
    assert!(
        !corpus.by_name.is_empty() && !corpus.by_qualified.is_empty(),
        "reindex must populate both maps"
    );
    for entry in &corpus.entries {
        assert!(
            entry.module_idx < corpus.modules.len(),
            "{} points at a missing module",
            entry.qualified
        );
        assert!(corpus.by_qualified.contains_key(&entry.qualified));
    }
}
