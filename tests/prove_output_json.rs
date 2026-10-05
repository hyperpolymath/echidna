// SPDX-License-Identifier: MPL-2.0

//! End-to-end tests of `echidna prove --output json` (the
//! `echidna.prove.result/1` contract) against the real binary.
//!
//! The TypedWasm backend is pure Rust, so `verified` and `failed` runs need
//! no external prover. `error` is produced by a missing file and by a file
//! with no detectable backend. `timeout` and `unknown` need a backend that
//! times out or reports inconsistent premises; they are covered by the
//! golden tests in `src/rust/prove_contract.rs` and `echidna-core`.

use echidna_core::prove_result::{ProveResult, ProveStatus, SCHEMA};
use std::path::Path;
use std::process::{Command, Output};

const OK_TWASM: &str = "region Particles { x: f32; y: f32; mass: f64 } [1024]\n\
effect Particles { read; write }\n\
region.get Particles[0] .x\n\
linear.acquire Particles\n\
linear.release Particles\n";

const BAD_TWASM: &str = "region Foo { bar: i32 } [10]\nregion.get Foo[0] .nonexistent\n";

/// Run the echidna binary with `args` in `dir`.
fn echidna(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_echidna"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("run echidna")
}

/// Assert the contract's stdout shape and return the parsed result.
fn contract_result(out: &Output) -> ProveResult {
    let stdout = String::from_utf8(out.stdout.clone()).expect("stdout is UTF-8");
    assert!(
        stdout.ends_with('\n'),
        "stdout must end with one newline: {stdout:?}"
    );
    assert_eq!(
        stdout.matches('\n').count(),
        1,
        "exactly one line: {stdout:?}"
    );
    // parse() also checks the line is byte-identical to its JCS form.
    let r = ProveResult::parse(&stdout).unwrap_or_else(|e| panic!("{e}: {stdout:?}"));
    assert_eq!(r.schema, SCHEMA);
    assert_eq!(r.echidna_version, env!("CARGO_PKG_VERSION"));
    r
}

/// A proof the TypedWasm checker accepts is `verified` and exits 0.
#[test]
fn verified_run_prints_one_canonical_object() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("ok.twasm"), OK_TWASM).unwrap();
    let out = echidna(
        dir.path(),
        &[
            "prove",
            "ok.twasm",
            "--prover",
            "typed-wasm",
            "--output",
            "json",
        ],
    );
    let r = contract_result(&out);
    assert_eq!(r.status, ProveStatus::Verified);
    assert_eq!(r.prover, "TypedWasm");
    assert_eq!(r.goal, "ok.twasm");
    assert_eq!(r.trust.confidence, None);
    assert_eq!(out.status.code(), Some(0));
}

/// A proof the checker rejects is `failed` and exits 1.
#[test]
fn failed_run_is_reported_as_failed() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("bad.twasm"), BAD_TWASM).unwrap();
    let out = echidna(
        dir.path(),
        &[
            "prove",
            "bad.twasm",
            "--prover",
            "typed-wasm",
            "--output",
            "json",
        ],
    );
    assert_eq!(contract_result(&out).status, ProveStatus::Failed);
    assert_eq!(out.status.code(), Some(1));
}

/// A missing file is an `error` object, not a non-JSON message.
#[test]
fn missing_file_is_an_error_object() {
    let dir = tempfile::tempdir().unwrap();
    let out = echidna(
        dir.path(),
        &[
            "prove",
            "nope.twasm",
            "--prover",
            "typed-wasm",
            "--output",
            "json",
        ],
    );
    let r = contract_result(&out);
    assert_eq!(r.status, ProveStatus::Error);
    assert!(!r.message.is_empty());
    assert_eq!(out.status.code(), Some(1));
}

/// No detectable backend is an `error` object with an empty `prover`.
#[test]
fn undetectable_backend_is_an_error_object() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("x.unknownext"), "x").unwrap();
    let out = echidna(dir.path(), &["prove", "x.unknownext", "--output", "json"]);
    let r = contract_result(&out);
    assert_eq!(r.status, ProveStatus::Error);
    assert_eq!(r.prover, "");
    assert_eq!(out.status.code(), Some(1));
}

/// Without `--output json` the human report is unchanged.
#[test]
fn human_output_stays_the_default() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("ok.twasm"), OK_TWASM).unwrap();
    let out = echidna(
        dir.path(),
        &["prove", "ok.twasm", "--prover", "typed-wasm", "--no-color"],
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("Proof verified successfully"), "{stdout}");
    assert!(ProveResult::parse(&stdout).is_err());
    assert_eq!(out.status.code(), Some(0));
}

/// `prove --help` advertises `--output`, which is how consumers detect it.
#[test]
fn help_advertises_the_output_flag() {
    let dir = tempfile::tempdir().unwrap();
    let out = echidna(dir.path(), &["prove", "--help"]);
    let help = String::from_utf8_lossy(&out.stdout);
    assert!(help.split_whitespace().any(|t| t == "--output"), "{help}");
}
