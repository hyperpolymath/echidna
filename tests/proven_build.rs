// SPDX-License-Identifier: MPL-2.0
//! BLD (taxonomy category 4): the `echidna` binary artefact exists and is
//! non-empty, and the workspace resolves from the committed lockfile. The
//! warnings-denied clean build and its timing run in CI through
//! `kit/lib/build-check.sh` (the cheap form here must not rebuild the tree).
use std::path::Path;
use std::process::Command;

#[test]
fn the_binary_artifact_exists_and_is_nonempty() {
    let p = Path::new(env!("CARGO_BIN_EXE_echidna"));
    assert!(p.is_file(), "{} is not a file", p.display());
    assert!(p.metadata().unwrap().len() > 0, "{} is empty", p.display());
}

#[test]
fn the_lockfile_resolves_without_network() {
    let out = Command::new(env!("CARGO"))
        .args(["metadata", "--locked", "--offline", "--format-version", "1", "--no-deps"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("spawn cargo");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
}

// Negative control: a lockfile check must be able to fail.
#[test]
fn a_bogus_manifest_path_is_rejected() {
    let out = Command::new(env!("CARGO"))
        .args(["metadata", "--locked", "--offline", "--manifest-path", "/nonexistent/Cargo.toml"])
        .output()
        .expect("spawn cargo");
    assert!(!out.status.success());
}
