// SPDX-License-Identifier: MPL-2.0

//! End-to-end tests of `echidna coprocessor` (the
//! `echidna.coprocessor.*/1` contract) against the real binary.
//!
//! Every exposed backend runs in process, so no external program is needed.
//! The `declined` case is `VectorAdd` on vectors of different length, which
//! `src/rust/coprocessor/vector.rs` answers with `Failure`.

use serde_json::Value;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Output, Stdio};

const GCD: &str = r#"{"schema":"echidna.coprocessor.request/1","kind":"Math","op":{"BigIntGcd":{"a":"12","b":"18"}}}"#;

/// Run the echidna binary with `args` in `dir`, feeding `stdin`.
fn echidna(dir: &Path, args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_echidna"))
        .current_dir(dir)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run echidna");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().expect("wait for echidna")
}

/// Dispatch `request` on stdin.
fn dispatch(request: &str) -> Output {
    let dir = tempfile::tempdir().unwrap();
    echidna(dir.path(), &["coprocessor", "dispatch"], request)
}

/// Assert stdout is exactly one JCS line and return it parsed.
fn one_line(out: &Output, schema: &str) -> Value {
    let stdout = String::from_utf8(out.stdout.clone()).expect("stdout is UTF-8");
    assert!(stdout.ends_with('\n'), "one final newline: {stdout:?}");
    assert_eq!(
        stdout.matches('\n').count(),
        1,
        "exactly one line: {stdout:?}"
    );
    let line = stdout.trim_end_matches('\n');
    let v: Value = serde_json::from_str(line).unwrap_or_else(|e| panic!("{e}: {stdout:?}"));
    assert_eq!(
        serde_json_canonicalizer::to_string(&v).unwrap(),
        line,
        "the line is its own JCS form"
    );
    assert_eq!(v["schema"], schema);
    assert_eq!(v["echidna_version"], env!("CARGO_PKG_VERSION"));
    v
}

/// Assert the result contract and return the parsed object.
fn result(out: &Output) -> Value {
    let v = one_line(out, "echidna.coprocessor.result/1");
    assert_eq!(v["trust"]["proof"], Value::Bool(false), "{v}");
    v
}

/// gcd(12, 18) on stdin is `computed`, outcome `{"BigInt":"6"}`, exit 0.
#[test]
fn gcd_from_stdin_is_computed() {
    let out = dispatch(GCD);
    let v = result(&out);
    assert_eq!(v["status"], "computed");
    assert_eq!(v["outcome"], serde_json::json!({"BigInt": "6"}));
    assert_eq!(v["kind"], "Math");
    assert_eq!(v["op"], "BigIntGcd");
    assert_eq!(v["trust"]["tier"], "LibraryWrapped");
    assert_eq!(v["deterministic"], true);
    assert_eq!(out.status.code(), Some(0));
}

/// `--request FILE` gives the same answer as stdin.
#[test]
fn gcd_from_request_file_is_computed() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("req.json"), GCD).unwrap();
    let out = echidna(
        dir.path(),
        &["coprocessor", "dispatch", "--request", "req.json"],
        "",
    );
    let v = result(&out);
    assert_eq!(v["status"], "computed");
    assert_eq!(v["outcome"], serde_json::json!({"BigInt": "6"}));
    assert_eq!(out.status.code(), Some(0));
}

/// A backend `Failure` is `declined` and exits 1.
#[test]
fn length_mismatch_is_declined() {
    let out = dispatch(
        r#"{"schema":"echidna.coprocessor.request/1","kind":"Vector","op":{"VectorAdd":{"a":[1.0,2.0],"b":[1.0]}}}"#,
    );
    let v = result(&out);
    assert_eq!(v["status"], "declined");
    assert!(v["outcome"]["Failure"].is_string(), "{v}");
    assert!(!v["message"].as_str().unwrap().is_empty());
    assert_eq!(out.status.code(), Some(1));
}

/// A kind outside the allow-list is `unavailable` and exits 1.
#[test]
fn io_kind_is_unavailable() {
    let out = dispatch(
        r#"{"schema":"echidna.coprocessor.request/1","kind":"Io","op":{"IoLineCount":{"path":"/etc/passwd"}}}"#,
    );
    let v = result(&out);
    assert_eq!(v["status"], "unavailable");
    assert!(v["outcome"].is_null());
    assert!(v["trust"]["tier"].is_null());
    assert_eq!(out.status.code(), Some(1));
}

/// Malformed input, an unreadable file, and an op of another kind are `error`, exit 1.
#[test]
fn malformed_input_is_an_error() {
    for (input, op_null) in [
        ("{not json", true),
        ("", true),
        (
            r#"{"schema":"echidna.coprocessor.request/1","kind":"Math","op":{"VectorNorm":{"a":[3.0]}}}"#,
            false,
        ),
    ] {
        let out = dispatch(input);
        let v = result(&out);
        assert_eq!(v["status"], "error", "{input}");
        assert_eq!(v["op"].is_null(), op_null, "{input}: {v}");
        assert_eq!(out.status.code(), Some(1), "{input}");
    }
    let dir = tempfile::tempdir().unwrap();
    let out = echidna(
        dir.path(),
        &["coprocessor", "dispatch", "--request", "missing.json"],
        "",
    );
    assert_eq!(result(&out)["status"], "error");
    assert_eq!(out.status.code(), Some(1));
}

/// `capabilities` prints one line with one entry per kind, and exits 0.
#[test]
fn capabilities_list_every_kind() {
    let dir = tempfile::tempdir().unwrap();
    let out = echidna(dir.path(), &["coprocessor", "capabilities"], "");
    let v = one_line(&out, "echidna.coprocessor.capabilities/1");
    let kinds = v["kinds"].as_array().unwrap();
    assert_eq!(kinds.len(), 16);
    let io = kinds.iter().find(|k| k["kind"] == "Io").unwrap();
    assert_eq!(io["exposed"], false);
    assert_eq!(io["available"], false);
    let math = kinds.iter().find(|k| k["kind"] == "Math").unwrap();
    assert_eq!(math["exposed"], true);
    assert_eq!(math["available"], true);
    assert_eq!(math["trust"]["proof"], false);
    assert_eq!(out.status.code(), Some(0));
}
