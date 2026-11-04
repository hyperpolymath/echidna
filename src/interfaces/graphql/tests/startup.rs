// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell
//! Exercise the actual listener process, including failed startup and the root route.

use std::net::TcpListener;
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

fn server() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_echidna-graphql"));
    command.stdout(Stdio::null()).stderr(Stdio::piped());
    command
}

fn failed_start(mut command: Command) -> Output {
    let mut child = command.spawn().expect("start GraphQL process");
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if child.try_wait().expect("inspect GraphQL process").is_some() {
            let output = child.wait_with_output().expect("read startup error");
            assert!(
                !output.status.success(),
                "invalid startup unexpectedly succeeded"
            );
            let error = String::from_utf8_lossy(&output.stderr);
            assert!(error.contains("ECHIDNA_GRAPHQL_ADDR"), "{error}");
            assert!(!error.contains("panicked at"), "{error}");
            return output;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("invalid startup remained running instead of returning an error");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn malformed_address_returns_a_configuration_error() {
    let mut command = server();
    command.env("ECHIDNA_GRAPHQL_ADDR", "127.0.0.1:not-a-port");
    failed_start(command);
}

#[test]
fn occupied_address_returns_a_bind_error() {
    let occupied = TcpListener::bind("127.0.0.1:0").expect("reserve a local port");
    let mut command = server();
    command.env(
        "ECHIDNA_GRAPHQL_ADDR",
        occupied.local_addr().unwrap().to_string(),
    );
    failed_start(command);
}

#[cfg(unix)]
#[test]
fn non_unicode_address_is_rejected_without_using_the_default() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let mut command = server();
    command.env("ECHIDNA_GRAPHQL_ADDR", OsString::from_vec(vec![0xff]));
    failed_start(command);
}

struct RunningServer(Child);

impl Drop for RunningServer {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[tokio::test]
async fn hostname_override_serves_graphql_at_the_root() {
    let reservation = TcpListener::bind("127.0.0.1:0").expect("choose a local port");
    let port = reservation.local_addr().unwrap().port();
    drop(reservation);

    let mut command = server();
    command.env("ECHIDNA_GRAPHQL_ADDR", format!("localhost:{port}"));
    let mut process = RunningServer(command.spawn().expect("start GraphQL process"));
    let client = reqwest::Client::builder()
        .timeout(Duration::from_millis(250))
        .build()
        .unwrap();
    let base = format!("http://localhost:{port}");
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Ok(response) = client.get(format!("{base}/health")).send().await {
            if response.status().is_success() {
                break;
            }
        }
        assert!(
            process.0.try_wait().unwrap().is_none(),
            "GraphQL process exited before serving health"
        );
        assert!(
            Instant::now() < deadline,
            "GraphQL listener did not become ready"
        );
        tokio::time::sleep(Duration::from_millis(20)).await;
    }

    let response: serde_json::Value = client
        .post(format!("{base}/"))
        .json(&serde_json::json!({"query": "{ __typename }"}))
        .send()
        .await
        .unwrap()
        .error_for_status()
        .unwrap()
        .json()
        .await
        .unwrap();
    assert_eq!(response["data"]["__typename"], "QueryRoot");
    assert_eq!(
        client
            .post(format!("{base}/graphql"))
            .send()
            .await
            .unwrap()
            .status(),
        reqwest::StatusCode::NOT_FOUND
    );
}
