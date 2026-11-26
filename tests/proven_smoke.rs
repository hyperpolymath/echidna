// SPDX-License-Identifier: MPL-2.0
//! SMK (taxonomy category 8): the built `echidna` binary starts, answers and
//! exits cleanly. No external prover is needed, so none of these tests can pass
//! by skipping; each asserts on real output and has a negative control.
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_echidna"))
}

#[test]
fn version_prints_the_package_version() {
    let out = bin().arg("--version").output().expect("spawn echidna");
    assert!(out.status.success(), "exit: {:?}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains(env!("CARGO_PKG_VERSION")),
        "version output {stdout:?} lacks {}",
        env!("CARGO_PKG_VERSION")
    );
}

#[test]
fn help_lists_the_core_subcommands() {
    let out = bin().arg("--help").output().expect("spawn echidna");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    for sub in ["prove", "verify", "list-provers", "server"] {
        assert!(stdout.contains(sub), "--help does not mention `{sub}`");
    }
}

#[test]
fn list_provers_answers_with_at_least_one_backend() {
    let out = bin().arg("list-provers").output().expect("spawn echidna");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.lines().any(|l| l.contains(" - Tier ")),
        "list-provers listed no backend:\n{stdout}"
    );
}

// Negative controls: a smoke test that cannot fail proves nothing.
#[test]
fn unknown_subcommand_exits_nonzero() {
    let out = bin()
        .arg("no-such-subcommand")
        .output()
        .expect("spawn echidna");
    assert!(!out.status.success());
}

#[test]
fn proving_a_missing_file_exits_nonzero() {
    let out = bin()
        .args(["prove", "/nonexistent/proven-smoke-input.v"])
        .output()
        .expect("spawn echidna");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("Failed to parse proof file"),
        "expected the missing-file error, got:\n{stderr}"
    );
}
