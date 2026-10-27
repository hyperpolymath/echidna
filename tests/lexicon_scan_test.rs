// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! `echidna lexicon scan` over small fixture corpora
//! (`tests/lexicon_fixtures/scan/proof_states_*.jsonl`).
//!
//! The HOL fixtures are real rows from `training_data/` for the stage-6a
//! pilot pair. `dk-shape-v1` cannot read HOL notation, so the scan must say
//! so (`unparsed`) rather than invent shape matches. The `lean_mini` /
//! `isabelle_mini` fixtures use syntax the scheme reads completely, so every
//! join and classification can be pinned there.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use echidna::lexicon::scan::{
    self, Candidate, CandidateRecord, Corpus, Join, PairSummary, RunOptions, ScanOptions,
};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lexicon_fixtures/scan")
}

fn load(key: &str) -> Corpus {
    Corpus::load(&fixtures(), key).unwrap_or_else(|e| panic!("{key}: {e:#}"))
}

fn scan(a: &str, b: &str, opts: &ScanOptions) -> (PairSummary, Vec<CandidateRecord>) {
    let (ca, cb) = (load(a), load(b));
    let mut out = Vec::new();
    let summary = scan::scan_pair(&ca, &cb, opts, &mut |r| {
        out.push(r.clone());
        Ok(())
    })
    .expect("scan");
    (summary, out)
}

fn find<'r>(records: &'r [CandidateRecord], a: &str, b: &str) -> &'r CandidateRecord {
    records
        .iter()
        .find(|r| r.a.name == a && r.b.name == b)
        .unwrap_or_else(|| panic!("no record for {a} ~ {b}"))
}

#[test]
fn hol_pilot_pair_is_classified_honestly() {
    let (summary, records) = scan("hol4_mini", "hol_light_mini", &ScanOptions::default());

    // Identical text is a cognate whatever the canonicaliser makes of it.
    assert_eq!(
        find(&records, "ADD_SYM", "ADD_SYM").candidate,
        Candidate::CognateExact
    );
    assert_eq!(
        find(&records, "ADD_0", "ADD_0").candidate,
        Candidate::CognateExact
    );

    // `0 < d` against `&0 < d`: the HOL Light statement is over the reals.
    // dk-shape-v1 cannot read `!` binders, so neither side is complete and
    // the pair is `unparsed`, not a shape cognate and not `differs`.
    let abs = find(&records, "ABS_BETWEEN", "ABS_BETWEEN");
    assert_eq!(abs.candidate, Candidate::Unparsed);
    assert!(!abs.a.complete && !abs.b.complete);

    // Different names, identical text: found by the text join although the
    // canonicaliser drops HOL's `FACT` as a declaration keyword.
    let fact = find(&records, "FACT_0", "FACT");
    assert_eq!(fact.join, Join::Text);
    assert_eq!(fact.candidate, Candidate::CognateExact);

    // `lemma` is shared but generic.
    assert_eq!(summary.generic_names_skipped, 1);
    assert!(!records.iter().any(|r| r.a.name == "lemma"));

    // Nothing in this pair parses completely, so no shape or skeleton join.
    assert_eq!(summary.candidates.shape.total(), 0);
    assert_eq!(summary.candidates.skeleton.total(), 0);
}

#[test]
fn every_join_and_class_on_complete_syntax() {
    let (summary, records) = scan("lean_mini", "isabelle_mini", &ScanOptions::default());

    // Same name, alpha-variants.
    let add_comm = find(&records, "add_comm", "add_comm");
    assert_eq!(add_comm.join, Join::NameExact);
    assert_eq!(add_comm.candidate, Candidate::CognateShape);

    // Names equal only after folding (`nat.mul_comm` / `MUL_COMM`).
    let mul_comm = find(&records, "nat.mul_comm", "MUL_COMM");
    assert_eq!(mul_comm.join, Join::NameFolded);
    assert_eq!(mul_comm.candidate, Candidate::CognateShape);

    // `nat` against `int`: the skeletons agree, the shapes do not.
    let add_zero = find(&records, "add_zero", "add_zero");
    assert_eq!(add_zero.candidate, Candidate::CognateSkeleton);

    // Same name, different statement: a false-friend candidate.
    assert_eq!(
        find(&records, "pow_zero", "pow_zero").candidate,
        Candidate::Differs
    );

    // Different names, the same shape: a synonym candidate.
    let assoc = find(&records, "mul_assoc", "times_assoc");
    assert_eq!(assoc.join, Join::Shape);
    assert_eq!(assoc.candidate, Candidate::CognateShape);

    // `cos 0 = 1` and `exp 0 = 1` share a dk-shape-v1 key (`cos`/`exp` are
    // renamed as variables); the join refuses it as uninformative.
    assert!(!records.iter().any(|r| r.a.name == "cos_zero"));
    assert!(summary.shape_groups_uninformative >= 1);

    // Homonyms: `ext` has 3 Lean and 2 Isabelle statements, 6 pairs.
    let ext = records.iter().filter(|r| r.a.name == "ext").count();
    assert_eq!(ext, 6);

    // Every record is flag-only.
    for r in &records {
        assert_eq!(
            serde_json::to_value(&r.evidence).unwrap(),
            serde_json::json!({"kind": "none"})
        );
    }
}

#[test]
fn homonym_cross_products_over_the_cap_are_counted_not_emitted() {
    let opts = ScanOptions {
        max_pairs_per_name: 4,
        ..ScanOptions::default()
    };
    let (summary, records) = scan("lean_mini", "isabelle_mini", &opts);
    assert!(!records.iter().any(|r| r.a.name == "ext"));
    assert_eq!(summary.name_pairs_capped, 1);
    assert_eq!(summary.statement_pairs_capped, 6);
}

#[test]
fn records_are_jcs_and_ids_ignore_scan_direction() {
    let (_, forward) = scan("lean_mini", "isabelle_mini", &ScanOptions::default());
    let (_, backward) = scan("isabelle_mini", "lean_mini", &ScanOptions::default());

    for r in &forward {
        let line = scan::jcs_line(r).unwrap();
        assert_eq!(*line.last().unwrap(), b'\n');
        let body = &line[..line.len() - 1];
        let reparsed: serde_json::Value = serde_json::from_slice(body).unwrap();
        assert_eq!(serde_json_canonicalizer::to_vec(&reparsed).unwrap(), body);
        assert_eq!(uuid::Uuid::parse_str(&r.id).unwrap().get_version_num(), 8);
    }

    let ids = |rs: &[CandidateRecord]| rs.iter().map(|r| r.id.clone()).collect::<BTreeSet<_>>();
    assert_eq!(ids(&forward), ids(&backward));
    assert_eq!(ids(&forward).len(), forward.len(), "ids are unique");
}

#[test]
fn a_run_writes_the_same_bytes_twice() {
    let base = std::env::temp_dir().join(format!("echidna-lexicon-scan-{}", std::process::id()));
    let run_into = |dir: &str| {
        let out = base.join(dir);
        let report = scan::run(&RunOptions {
            training_dir: fixtures(),
            pairs: vec![
                ("lean_mini".into(), "isabelle_mini".into()),
                ("hol4_mini".into(), "hol_light_mini".into()),
            ],
            out: out.clone(),
            scan: ScanOptions::default(),
            collision_samples: 10,
        })
        .expect("run");
        assert_eq!(report.pairs.len(), 2);
        assert_eq!(report.coverage.len(), 4);
        out
    };
    let (one, two) = (run_into("one"), run_into("two"));
    for file in [
        "summary.jsonl",
        "coverage.jsonl",
        "pairs/lean_mini__isabelle_mini.jsonl",
        "pairs/hol4_mini__hol_light_mini.jsonl",
        "collisions/lean_mini.jsonl",
    ] {
        let (x, y) = (
            std::fs::read(one.join(file)).unwrap(),
            std::fs::read(two.join(file)).unwrap(),
        );
        assert_eq!(x, y, "{file} differs between runs");
    }
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn unknown_corpus_keys_fail_loudly() {
    assert!(Corpus::load(&fixtures(), "no_such_corpus").is_err());
    assert!(Corpus::load(&fixtures(), "../etc").is_err());
}

#[test]
fn a_rerun_with_fewer_pairs_leaves_no_stale_pair_files() {
    let out = std::env::temp_dir().join(format!("echidna-lexicon-rerun-{}", std::process::id()));
    let run_with = |pairs: Vec<(String, String)>| {
        scan::run(&RunOptions {
            training_dir: fixtures(),
            pairs,
            out: out.clone(),
            scan: ScanOptions::default(),
            collision_samples: 10,
        })
        .expect("run")
    };
    run_with(vec![
        ("lean_mini".into(), "isabelle_mini".into()),
        ("hol4_mini".into(), "hol_light_mini".into()),
    ]);
    run_with(vec![("lean_mini".into(), "isabelle_mini".into())]);
    let listed = |dir: &str| {
        let mut names: Vec<String> = std::fs::read_dir(out.join(dir))
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    };
    assert_eq!(listed("pairs"), vec!["lean_mini__isabelle_mini.jsonl"]);
    assert_eq!(
        listed("collisions"),
        vec!["isabelle_mini.jsonl", "lean_mini.jsonl"]
    );
    let _ = std::fs::remove_dir_all(&out);
}
