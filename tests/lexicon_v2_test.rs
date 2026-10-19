// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Lexicon v2: every shipped table loads, v2 fields parse, false friends
//! are never offered as substitutes, and lexicon evidence lifts to the
//! arbiter's fidelity evidence without raising it.
//!
//! The normative shape check is the Nickel contract
//! `data/synonyms/schema.ncl` (`scripts/lexicon-check.sh`); this suite
//! covers what Nickel does not: enum membership of `checked_by` /
//! `format` (serde), and the loader's behaviour.

use std::path::{Path, PathBuf};

use echidna::exchange::ExchangeFormat;
use echidna::provers::ProverKind;
use echidna::suggest::synonyms::{
    load_all, load_cross_prover_dicts, LexiconEvidence, Relation, SynonymTable,
};
use echidna::verification::FidelityEvidence;

fn synonyms_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("data/synonyms")
}

#[test]
fn every_shipped_table_loads() {
    let mut loaded = 0;
    for entry in std::fs::read_dir(synonyms_dir()).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("toml") {
            continue;
        }
        let table =
            SynonymTable::load_path(&path).unwrap_or_else(|e| panic!("{}: {e:#}", path.display()));
        assert!(!table.is_empty(), "{} has no rows", path.display());
        loaded += 1;
    }
    assert!(
        loaded >= 18,
        "expected the 18 shipped tables, found {loaded}"
    );
}

#[test]
fn load_all_and_cross_prover_dicts_succeed() {
    let tables = load_all(&synonyms_dir()).expect("load_all");
    assert!(tables.contains_key(&ProverKind::HOL4), "HOL4 table missing");
    load_cross_prover_dicts(&synonyms_dir()).expect("cross-prover dicts");
}

const V2_TABLE: &str = r#"
[[synonym]]
canonical = "omega"
aliases = ["lia"]

[[synonym]]
canonical = "NN"
aliases = ["NN0"]
relation = "false_friend"
false_friends = [{ name = "Nat", table = "lean4" }]
evidence = { kind = "curated" }

[[synonym]]
canonical = "le_trans"
aliases = ["Rle_trans"]
relation = "specialisation"
fidelity = "lossy"
residue = "Rle_trans fixes the carrier to R"
scope = { library = "Coq.Reals", version = "8.18" }
evidence = { kind = "probe", tests = 12, failures = 0 }

[[synonym]]
canonical = "then thus"
aliases = ["hence"]
relation = "phrase"
phrase = ["then", "thus"]

[[synonym]]
canonical = "add_comm"
aliases = ["Nat.add_comm"]
evidence = { kind = "kernel", format = "dedukti", checked_by = "Dedukti", term_hash = "0000000000000000000000000000000000000000000000000000000000000000" }
"#;

fn v2_table() -> SynonymTable {
    #[derive(serde::Deserialize)]
    struct Raw {
        synonym: Vec<echidna::suggest::synonyms::SynonymEntry>,
    }
    let raw: Raw = toml::from_str(V2_TABLE).expect("v2 fixture parses");
    SynonymTable::from_entries(raw.synonym)
}

#[test]
fn false_friends_are_never_alternatives() {
    let t = v2_table();
    assert!(t.alternatives("NN").is_empty());
    assert!(t.alternatives("NN0").is_empty());
    assert_eq!(
        t.related("NN"),
        vec![("NN0".to_string(), Relation::FalseFriend)]
    );
    // v1 rows keep their meaning.
    assert_eq!(t.alternatives("omega"), vec!["lia".to_string()]);
}

#[test]
fn specialisation_is_related_not_substituted_and_inverts() {
    let t = v2_table();
    assert!(t.alternatives("le_trans").is_empty());
    assert_eq!(
        t.related("le_trans"),
        vec![("Rle_trans".to_string(), Relation::Specialisation)]
    );
    assert_eq!(
        t.related("Rle_trans"),
        vec![("le_trans".to_string(), Relation::Generalisation)]
    );
}

#[test]
fn phrase_spellings_are_interchangeable() {
    let t = v2_table();
    assert_eq!(t.alternatives("hence"), vec!["then thus".to_string()]);
}

#[test]
fn evidence_lifts_without_raising_fidelity() {
    let t = v2_table();
    let by = |c: &str| t.entries.iter().find(|e| e.canonical == c).unwrap();
    assert_eq!(by("omega").evidence, LexiconEvidence::None);
    assert_eq!(by("omega").evidence.to_fidelity(), FidelityEvidence::None);
    assert_eq!(by("NN").evidence.to_fidelity(), FidelityEvidence::None);
    assert_eq!(
        by("le_trans").evidence.to_fidelity(),
        FidelityEvidence::DeclaredCorrespondence {
            consequence_tests: 12,
            failures: 0
        }
    );
    match by("add_comm").evidence.to_fidelity() {
        FidelityEvidence::KernelTranslation {
            format, checked_by, ..
        } => {
            assert_eq!(format, ExchangeFormat::Dedukti);
            assert_eq!(checked_by, ProverKind::Dedukti);
        },
        other => panic!("expected a kernel translation, got {other:?}"),
    }
}

#[test]
fn unknown_fields_and_prover_names_are_rejected() {
    let typo = "[[synonym]]\ncanonical = \"x\"\naliases = []\nrelaton = \"phrase\"\n";
    assert!(SynonymTable::load_path(&write_tmp("typo.toml", typo)).is_err());
    let bad_prover = "[[synonym]]\ncanonical = \"x\"\naliases = []\nevidence = { kind = \"kernel\", format = \"dedukti\", checked_by = \"NoSuchProver\", term_hash = \"00\" }\n";
    assert!(SynonymTable::load_path(&write_tmp("prover.toml", bad_prover)).is_err());
}

fn write_tmp(name: &str, body: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("echidna-lexicon-v2-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, body).unwrap();
    path
}
