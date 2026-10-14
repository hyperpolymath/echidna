// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Regression fixture for `ResultArbiter` numeric fusion (ECH-05, PR A).
//!
//! ECH-05 adds a fidelity level (`belief` / `epi` / `sound`) on top of
//! the arbiter's numeric fusion and requires that fusion to be unchanged
//! below the level. This file replays a fixed scenario set under every
//! policy and compares each `ArbitratedVerdict` field by field with
//! `tests/fixtures/arbitration_regression.json`.
//!
//! The fixture was produced by `regenerate_arbitration_fixture` at the
//! pre-ECH-05 commit `29b18ea`, so it records the numbers the arbiter gave
//! before `FidelityEvidence` existed. Every field the fixture holds must
//! match (floats to 1e-12); the only fields allowed beyond the fixture are
//! the ECH-05 additions, and every replayed verdict must sit at level
//! `belief` — the attempts carry no fidelity evidence.
//!
//! Regenerate only at a commit whose numbers are the intended reference:
//!
//! ```sh
//! cargo test --test arbitration_regression_test -- --ignored regenerate
//! ```

use echidna::provers::outcome::ProverOutcome;
use echidna::provers::ProverKind;
use echidna::verification::{ArbitrationPolicy, ProverAttempt, ResultArbiter};
use serde_json::{json, Value};

const FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/arbitration_regression.json"
);

/// Fields ECH-05 adds to `ArbitratedVerdict`; absent from the fixture.
const ECH05_FIELDS: &[&str] = &["level", "retracted", "warranted_term"];

const TOLERANCE: f64 = 1e-12;

fn proved(p: ProverKind, ms: u64) -> ProverAttempt {
    ProverAttempt::new(p, ProverOutcome::Proved { elapsed_ms: ms }, ms)
}

fn no_proof(p: ProverKind, ms: u64) -> ProverAttempt {
    ProverAttempt::new(
        p,
        ProverOutcome::NoProofFound {
            elapsed_ms: ms,
            reason: None,
        },
        ms,
    )
}

fn timeout(p: ProverKind) -> ProverAttempt {
    ProverAttempt::new(p, ProverOutcome::Timeout { limit_secs: 300 }, 300_000)
}

fn inconsistent(p: ProverKind, ms: u64) -> ProverAttempt {
    ProverAttempt::new(p, ProverOutcome::InconsistentPremises { detail: None }, ms)
}

fn prover_error(p: ProverKind) -> ProverAttempt {
    ProverAttempt::new(
        p,
        ProverOutcome::ProverError {
            detail: "internal assertion".into(),
            exit_code: Some(2),
        },
        40,
    )
}

fn system_error(p: ProverKind) -> ProverAttempt {
    ProverAttempt::new(
        p,
        ProverOutcome::SystemError {
            detail: "binary not found".into(),
        },
        1,
    )
}

fn invalid(p: ProverKind) -> ProverAttempt {
    ProverAttempt::new(
        p,
        ProverOutcome::InvalidInput {
            reason: "parse error".into(),
            location: Some(3),
        },
        5,
    )
}

fn unsupported(p: ProverKind) -> ProverAttempt {
    ProverAttempt::new(
        p,
        ProverOutcome::UnsupportedFeature {
            feature: "higher-order".into(),
        },
        5,
    )
}

/// `(name, per-prover timeout in ms, attempts)`.
fn scenarios() -> Vec<(&'static str, u64, Vec<ProverAttempt>)> {
    use ProverKind::*;
    vec![
        (
            "unanimous_proven_three",
            300_000,
            vec![proved(Z3, 100), proved(CVC5, 200), proved(Vampire, 400)],
        ),
        (
            "proven_vs_refuted",
            300_000,
            vec![proved(Z3, 100), no_proof(CVC5, 200)],
        ),
        (
            "proven_with_timeout",
            300_000,
            vec![proved(Z3, 100), proved(CVC5, 200), timeout(Vampire)],
        ),
        ("all_timed_out", 300_000, vec![timeout(Z3), timeout(CVC5)]),
        (
            "inconsistent_premises",
            300_000,
            vec![proved(Z3, 100), inconsistent(CVC5, 50)],
        ),
        ("empty", 300_000, vec![]),
        (
            "two_vs_two_fast",
            300_000,
            vec![
                proved(Z3, 100),
                no_proof(Coq, 100),
                proved(Lean, 100),
                no_proof(Agda, 100),
            ],
        ),
        (
            "two_proven_fast",
            300_000,
            vec![proved(Z3, 100), proved(CVC5, 200)],
        ),
        (
            "pareto_three",
            300_000,
            vec![proved(Vampire, 5_000), proved(Z3, 120), proved(CVC5, 900)],
        ),
        (
            "unanimous_refuted",
            300_000,
            vec![no_proof(Z3, 50), no_proof(CVC5, 70)],
        ),
        (
            "errors_mixed",
            300_000,
            vec![
                proved(Lean, 1_500),
                prover_error(Coq),
                system_error(Isabelle),
                invalid(Agda),
                unsupported(Z3),
            ],
        ),
        (
            "interactive_majority",
            300_000,
            vec![
                proved(Lean, 2_000),
                proved(Isabelle, 3_000),
                proved(Coq, 2_500),
                no_proof(Z3, 40),
            ],
        ),
        (
            "near_timeout",
            300_000,
            vec![proved(Z3, 290_000), proved(CVC5, 299_000)],
        ),
        (
            "short_budget",
            10_000,
            vec![proved(Z3, 9_000), no_proof(Vampire, 500)],
        ),
        ("single_proved", 300_000, vec![proved(Lean, 800)]),
        ("single_refuted", 300_000, vec![no_proof(Coq, 900)]),
    ]
}

fn policies() -> Vec<ArbitrationPolicy> {
    vec![
        ArbitrationPolicy::Portfolio,
        ArbitrationPolicy::Bayesian { prior_p_true: 0.5 },
        ArbitrationPolicy::Bayesian { prior_p_true: 0.9 },
        ArbitrationPolicy::DempsterShafer,
    ]
}

/// One `(scenario, policy, verdict)` record per scenario × policy.
fn replay() -> Vec<Value> {
    let mut cases = Vec::new();
    for (name, timeout_ms, attempts) in scenarios() {
        for policy in policies() {
            let verdict = ResultArbiter::new(policy, timeout_ms).arbitrate(&attempts);
            cases.push(json!({
                "scenario": name,
                "policy": serde_json::to_value(policy).unwrap(),
                "verdict": serde_json::to_value(&verdict).unwrap(),
            }));
        }
    }
    cases
}

/// Recursive comparison: objects by the expected side's keys, floats to
/// `TOLERANCE`, everything else exactly. Returns the first mismatch path.
fn close(expected: &Value, actual: &Value, path: &str) -> Result<(), String> {
    match (expected, actual) {
        (Value::Object(e), Value::Object(a)) => {
            for (k, ev) in e {
                let av = a
                    .get(k)
                    .ok_or_else(|| format!("{path}.{k}: missing in actual"))?;
                close(ev, av, &format!("{path}.{k}"))?;
            }
            Ok(())
        },
        (Value::Array(e), Value::Array(a)) => {
            if e.len() != a.len() {
                return Err(format!("{path}: length {} != {}", e.len(), a.len()));
            }
            for (i, (ev, av)) in e.iter().zip(a).enumerate() {
                close(ev, av, &format!("{path}[{i}]"))?;
            }
            Ok(())
        },
        (Value::Number(e), Value::Number(a)) => {
            let (e, a) = (e.as_f64().unwrap(), a.as_f64().unwrap());
            if (e - a).abs() <= TOLERANCE * e.abs().max(1.0) {
                Ok(())
            } else {
                Err(format!("{path}: {e} != {a}"))
            }
        },
        (e, a) if e == a => Ok(()),
        (e, a) => Err(format!("{path}: {e} != {a}")),
    }
}

#[test]
fn numeric_fusion_unchanged_and_level_is_belief() {
    let raw = std::fs::read_to_string(FIXTURE).expect("fixture present");
    let fixture: Value = serde_json::from_str(&raw).expect("fixture is JSON");
    let expected = fixture["cases"].as_array().expect("cases array");
    let actual = replay();
    assert_eq!(
        expected.len(),
        actual.len(),
        "scenario × policy set changed; the fixture no longer covers it"
    );

    for (e, a) in expected.iter().zip(&actual) {
        assert_eq!(e["scenario"], a["scenario"]);
        assert_eq!(e["policy"], a["policy"]);
        let label = format!("{} / {}", e["scenario"], e["policy"]);
        if let Err(diff) = close(&e["verdict"], &a["verdict"], "verdict") {
            panic!("{label}: numeric fusion changed at {diff}");
        }

        let ev = e["verdict"].as_object().unwrap();
        let av = a["verdict"].as_object().unwrap();
        for k in av.keys() {
            assert!(
                ev.contains_key(k) || ECH05_FIELDS.contains(&k.as_str()),
                "{label}: undocumented new field `{k}`"
            );
        }
        assert_eq!(
            av.get("level"),
            Some(&json!("belief")),
            "{label}: no fidelity evidence, so the level must be belief"
        );
    }
}

/// Writes the fixture from the current arbiter. Ignored: run it only at a
/// commit whose numbers are the intended reference (see module docs).
#[test]
#[ignore]
fn regenerate_arbitration_fixture() {
    let doc = json!({
        "provenance": "ResultArbiter numeric fusion at echidna 29b18ea (pre-ECH-05); \
                       produced by tests/arbitration_regression_test.rs::regenerate_arbitration_fixture",
        "tolerance": TOLERANCE,
        "cases": replay(),
    });
    let mut out = serde_json::to_string_pretty(&doc).unwrap();
    out.push('\n');
    std::fs::write(FIXTURE, out).expect("write fixture");
}
