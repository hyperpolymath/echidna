// SPDX-License-Identifier: MPL-2.0

//! Dispatch tests for `echidna corpus ingest --adapter <name>`.
//!
//! Every adapter name advertised in the CLI must reach its adapter's
//! `ingest` function rather than the "Unknown corpus adapter" fallback.
//! An empty project root is used so no real prover corpus is needed; the
//! adapters may legitimately find nothing and fail, but the dispatch error
//! must never appear for a supported name.

use std::path::Path;
use std::process::{Command, Output};

const SUPPORTED: &str = "agda coq lean idris2 acl2_books dafny fstar hol4 hol_light isabelle metamath minif2f mizar proofnet smtlib tptp why3";

fn ingest(dir: &Path, adapter: &str) -> Output {
    let root = dir.join("project");
    std::fs::create_dir_all(&root).expect("create project root");
    let out = dir.join(format!("{adapter}.json"));
    Command::new(env!("CARGO_BIN_EXE_echidna"))
        .current_dir(dir)
        .args(["corpus", "ingest", "--root"])
        .arg(&root)
        .args(["--adapter", adapter, "--out"])
        .arg(&out)
        .output()
        .expect("run echidna corpus ingest")
}

fn combined(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn every_advertised_adapter_is_dispatched() {
    let tmp = tempfile::tempdir().expect("tempdir");
    for adapter in SUPPORTED.split_whitespace() {
        let out = ingest(tmp.path(), adapter);
        let text = combined(&out);
        assert!(
            !text.contains("Unknown corpus adapter"),
            "adapter `{adapter}` fell through to the unknown-adapter arm: {text}"
        );
    }
}

#[test]
fn unknown_adapter_is_rejected() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = ingest(tmp.path(), "not_a_real_adapter");
    assert!(!out.status.success(), "unknown adapter must exit non-zero");
    let text = combined(&out);
    assert!(
        text.contains("Unknown corpus adapter 'not_a_real_adapter'"),
        "unexpected error text: {text}"
    );
    for adapter in SUPPORTED.split_whitespace() {
        assert!(
            text.contains(adapter),
            "error should list `{adapter}`: {text}"
        );
    }
}
