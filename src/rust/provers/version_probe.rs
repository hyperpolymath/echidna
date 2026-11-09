// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//! Subprocess lifetime boundary for short version probes.
//!
//! This runner returns the actual process status and output. Each backend keeps
//! its own interpretation of that response; this is not a proof result.
//! Cancellation terminates the direct child. Tokio owns its eventual reaping.

use anyhow::{Context, Result};
use std::process::{Output, Stdio};
use std::time::Duration;
use tokio::process::Command;

use super::ProverConfig;

/// Run a version probe with closed stdin and a one-to-ten-second deadline.
///
/// Keep this separate from proof execution: a version query must not block the
/// async runtime or consume the caller's input, even with a misbehaving binary.
pub(super) async fn run(config: &ProverConfig, args: &[&str]) -> Result<Output> {
    let limit = Duration::from_secs(config.timeout.clamp(1, 10));
    let mut command = Command::new(&config.executable);
    command.args(args).stdin(Stdio::null()).kill_on_drop(true);
    tokio::time::timeout(limit, command.output())
        .await
        .with_context(|| {
            format!(
                "Version probe at {} timed out after {}s",
                config.executable.display(),
                limit.as_secs()
            )
        })?
        .with_context(|| {
            format!(
                "Failed to execute version probe at {}",
                config.executable.display()
            )
        })
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    mod process {
        use super::super::*;
        use crate::provers::{ProverFactory, ProverKind};
        use std::os::unix::fs::PermissionsExt;
        use tokio::io::AsyncWriteExt;

        const CHILD_BACKEND: &str = "ECHIDNA_VERSION_PROBE_TEST_BACKEND";
        const CHILD_EXECUTABLE: &str = "ECHIDNA_VERSION_PROBE_TEST_EXECUTABLE";
        const CHILD_COMPLETE: &str = "ECHIDNA_VERSION_PROBE_CHILD_COMPLETE";

        fn fixture(script: &str, timeout: u64) -> (tempfile::TempDir, ProverConfig) {
            let directory = tempfile::tempdir().unwrap();
            let executable = directory.path().join("version-probe");
            crate::provers::test_fixture::write_executable(
                &executable,
                &format!(
                    "#!/bin/sh\n[ \"$#\" -eq 1 ] && [ \"$1\" = '--version' ] || exit 64\n{script}\n"
                ),
            );
            let config = ProverConfig {
                executable,
                timeout,
                ..ProverConfig::default()
            };
            (directory, config)
        }

        fn kind(name: &str) -> ProverKind {
            match name {
                "z3" => ProverKind::Z3,
                "cvc5" => ProverKind::CVC5,
                "alt-ergo" => ProverKind::AltErgo,
                "vampire" => ProverKind::Vampire,
                "eprover" => ProverKind::EProver,
                "glpk" => ProverKind::GLPK,
                "minizinc" => ProverKind::MiniZinc,
                "opensmt" => ProverKind::OpenSmt,
                _ => panic!("unexpected fixture backend: {name}"),
            }
        }

        const STATUS_BACKENDS: [(&str, &str); 7] = [
            ("z3", "Z3 version 4.13.4"),
            ("cvc5", "This is cvc5 version 1.1.2"),
            ("alt-ergo", "2.6.2"),
            ("vampire", "Vampire 4.9"),
            ("eprover", "E 3.1"),
            ("glpk", "GLPSOL--GLPK LP/MIP Solver 5.0"),
            ("minizinc", "MiniZinc to FlatZinc converter, version 2.8.7"),
        ];

        #[tokio::test]
        async fn factory_backends_reject_failed_probes_with_identifying_output() {
            for (name, banner) in STATUS_BACKENDS {
                for (exit_code, redirect) in [(1, ""), (7, ">&2")] {
                    let script = format!("printf '%s\\n' '{banner}' {redirect}; exit {exit_code}");
                    let (_directory, config) = fixture(&script, 5);
                    let backend = ProverFactory::create(kind(name), config).unwrap();
                    let error = backend.version().await.expect_err(
                        "version-like text must not turn a failed process into availability",
                    );
                    let message = format!("{error:#}");
                    assert!(
                        message.contains("version probe failed")
                            && message.contains(&format!("exit status: {exit_code}")),
                        "{name}: expected the fixture's actual exit status, got {message}"
                    );
                }
            }
        }

        #[tokio::test]
        async fn successful_factory_probes_preserve_backend_output_selection() {
            for (name, banner) in STATUS_BACKENDS {
                for with_stderr in [false, true] {
                    let mut script = format!("printf '%s\\n' '{banner}' 'additional stdout'");
                    if with_stderr {
                        script.push_str(
                            "\nprintf '%s\\n' 'stderr version banner' 'additional stderr' >&2",
                        );
                    }
                    script.push_str("\nexit 0");
                    let (_directory, config) = fixture(&script, 5);
                    let backend = ProverFactory::create(kind(name), config).unwrap();
                    let actual = backend.version().await.unwrap();
                    let expected = match (name, with_stderr) {
                        ("z3", _) => format!("{banner}\nadditional stdout"),
                        ("vampire", true) => "stderr version banner".to_string(),
                        _ => banner.to_string(),
                    };
                    assert_eq!(actual, expected, "{name}: stderr={with_stderr}");
                }
            }
        }

        #[tokio::test]
        async fn runner_preserves_real_status_and_both_output_streams() {
            let (_directory, config) = fixture(
                "printf 'stdout response\\n'; printf 'stderr response\\n' >&2; exit 7",
                5,
            );
            let output = run(&config, &["--version"]).await.unwrap();
            assert_eq!(output.status.code(), Some(7));
            assert_eq!(output.stdout, b"stdout response\n");
            assert_eq!(output.stderr, b"stderr response\n");
        }

        #[tokio::test]
        async fn runner_rejects_missing_and_non_executable_files() {
            let (_directory, mut config) = fixture("exit 0", 5);
            std::fs::set_permissions(&config.executable, std::fs::Permissions::from_mode(0o600))
                .unwrap();
            assert!(run(&config, &["--version"]).await.is_err());
            config.executable.set_file_name("missing-version-probe");
            assert!(run(&config, &["--version"]).await.is_err());
        }

        // Invoked by the parent test in a separate test-harness process so its
        // stdin is deliberately readable. The normal test run has no child
        // request; only the parent below claims to exercise this path.
        #[tokio::test]
        async fn child_probe_harness() {
            let Ok(name) = std::env::var(CHILD_BACKEND) else {
                return;
            };
            let executable = std::env::var_os(CHILD_EXECUTABLE)
                .expect("child fixture executable")
                .into();
            let backend = ProverFactory::create(
                kind(&name),
                ProverConfig {
                    executable,
                    timeout: 1,
                    ..ProverConfig::default()
                },
            )
            .unwrap();
            assert_eq!(backend.version().await.unwrap(), "fixture version 1.2");
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).unwrap();
            assert_eq!(input, "input reserved for the application\n");
            println!("{CHILD_COMPLETE}:{name}");
        }

        #[tokio::test]
        async fn callers_close_stdin_even_when_the_parent_has_readable_input() {
            let (_directory, config) = fixture(
                "if IFS= read -r line; then printf 'consumed parent input\\n'; exit 65; fi\n\
                 printf 'fixture version 1.2\\n'",
                1,
            );
            let test_name = format!(
                "{}::child_probe_harness",
                module_path!().split_once("::").unwrap().1
            );
            for name in [
                "z3", "cvc5", "alt-ergo", "vampire", "eprover", "glpk", "minizinc", "opensmt",
            ] {
                let mut child = Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", &test_name, "--nocapture"])
                    .env(CHILD_BACKEND, name)
                    .env(CHILD_EXECUTABLE, &config.executable)
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .kill_on_drop(true)
                    .spawn()
                    .unwrap();
                let mut input = child.stdin.take().unwrap();
                input
                    .write_all(b"input reserved for the application\n")
                    .await
                    .unwrap();
                drop(input);
                let output = tokio::time::timeout(Duration::from_secs(5), child.wait_with_output())
                    .await
                    .expect("child harness must finish within its deadline")
                    .expect("child harness process");
                assert!(
                    output.status.success(),
                    "{name}: stdout={}; stderr={}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                let marker = format!("{CHILD_COMPLETE}:{name}");
                assert!(
                    String::from_utf8_lossy(&output.stdout).contains(&marker),
                    "{name}: the exact child test must actually run"
                );
            }
        }

        fn process_running(pid: &str) -> std::io::Result<bool> {
            let output = std::process::Command::new("/bin/ps")
                .args(["-o", "stat=", "-p", pid])
                .stdin(Stdio::null())
                .output()?;
            process_state(output.status.code(), &output.stdout, &output.stderr)
        }

        fn process_state(
            exit_code: Option<i32>,
            stdout: &[u8],
            stderr: &[u8],
        ) -> std::io::Result<bool> {
            let invalid = || {
                std::io::Error::other(format!(
                    "cannot inspect fixture process: ps exit={exit_code:?}, stdout={stdout:?}, stderr={stderr:?}"
                ))
            };
            if !stderr.is_empty() {
                return Err(invalid());
            }
            if exit_code == Some(1) && stdout.iter().all(u8::is_ascii_whitespace) {
                return Ok(false);
            }
            if exit_code != Some(0) {
                return Err(invalid());
            }
            let text = std::str::from_utf8(stdout).map_err(|_| invalid())?;
            let mut fields = text.split_whitespace();
            let state = fields.next().ok_or_else(invalid)?;
            if fields.next().is_some()
                || !state.as_bytes()[1..]
                    .iter()
                    .all(|flag| matches!(flag, b'<' | b'N' | b'L' | b's' | b'l' | b'+'))
            {
                return Err(invalid());
            }
            match state.as_bytes()[0] {
                b'Z' | b'X' => Ok(false),
                b'R' | b'S' | b'D' | b'T' | b't' | b'I' | b'W' => Ok(true),
                _ => Err(invalid()),
            }
        }

        #[test]
        fn process_inspection_distinguishes_termination_from_unknown() {
            for state in ["R\n", "S+\n", "D\n", "T\n", "t\n", "I\n", "W\n"] {
                assert!(process_state(Some(0), state.as_bytes(), b"").unwrap());
            }
            for state in ["Z\n", "Zs\n", "X\n"] {
                assert!(!process_state(Some(0), state.as_bytes(), b"").unwrap());
            }
            assert!(!process_state(Some(1), b"", b"").unwrap());
            for (exit_code, stdout, stderr) in [
                (Some(0), b"".as_slice(), b"".as_slice()),
                (Some(0), b"S\nZ\n".as_slice(), b"".as_slice()),
                (Some(0), b"Zgarbage\n".as_slice(), b"".as_slice()),
                (Some(0), b"?\n".as_slice(), b"".as_slice()),
                (Some(0), b"\xff".as_slice(), b"".as_slice()),
                (Some(1), b"".as_slice(), b"fatal library error".as_slice()),
                (Some(1), b"Z\n".as_slice(), b"".as_slice()),
                (Some(2), b"Z\n".as_slice(), b"".as_slice()),
                (None, b"Z\n".as_slice(), b"".as_slice()),
            ] {
                assert!(process_state(exit_code, stdout, stderr).is_err());
            }
        }

        async fn assert_terminated(pid: &str) {
            let mut state = process_running(pid);
            for _ in 0..50 {
                if !matches!(&state, Ok(true)) {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
                state = process_running(pid);
            }
            // Cleanup precedes assertions, including an unknown inspection.
            // A zombie is terminated; Tokio, not this test, owns its reaping.
            let cleanup = if matches!(&state, Ok(false)) {
                None
            } else {
                Some(
                    std::process::Command::new("/bin/kill")
                        .args(["-9", pid])
                        .status(),
                )
            };
            let running = state.unwrap_or_else(|error| {
                panic!("inspect the fixture process: {error}; cleanup attempt: {cleanup:?}")
            });
            assert!(
                !running,
                "version probe process survived; cleanup attempt: {cleanup:?}"
            );
        }

        fn fixture_pid(config: &ProverConfig) -> std::io::Result<String> {
            std::fs::read_to_string(config.executable.with_extension("pid"))?
                .parse::<u32>()
                .map(|pid| pid.to_string())
                .map_err(std::io::Error::other)
        }

        #[tokio::test]
        async fn runner_times_out_and_terminates_the_process() {
            let (_directory, config) =
                fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 30", 1);
            let result =
                tokio::time::timeout(Duration::from_secs(3), run(&config, &["--version"])).await;
            let pid = fixture_pid(&config).expect("fixture process started");
            assert_terminated(&pid).await;
            let error = result
                .expect("the runner must enforce its own shorter deadline")
                .unwrap_err();
            assert!(error.to_string().contains("timed out after 1s"));
        }

        #[tokio::test]
        async fn factory_backends_enforce_their_own_probe_deadline_and_cleanup() {
            for name in [
                "z3", "cvc5", "alt-ergo", "vampire", "eprover", "glpk", "minizinc", "opensmt",
            ] {
                // The finite sleep also bounds a regression to a blocking
                // subprocess: Tokio cannot interrupt a future that never yields.
                let (_directory, config) =
                    fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 4", 1);
                let backend = ProverFactory::create(kind(name), config.clone()).unwrap();
                let started = std::time::Instant::now();
                let result = tokio::time::timeout(Duration::from_secs(3), backend.version()).await;
                let elapsed = started.elapsed();
                let pid = fixture_pid(&config).expect("fixture process started");
                // Check termination and attempt cleanup before any deadline or
                // result assertion, including a caller that bypasses the helper.
                assert_terminated(&pid).await;
                let error = result
                    .unwrap_or_else(|_| panic!("{name}: only the outer test timeout fired"))
                    .expect_err("the backend must reject its timed-out probe");
                assert!(
                    elapsed < Duration::from_secs(3),
                    "{name}: the backend blocked through its own deadline: {elapsed:?}"
                );
                assert!(
                    format!("{error:#}").contains("timed out"),
                    "{name}: expected the backend's timeout error, got {error:#}"
                );
            }
        }

        #[tokio::test]
        async fn caller_cancellation_terminates_an_in_flight_probe() {
            let (_directory, config) =
                fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 30", 10);
            let task_config = config.clone();
            let task = tokio::spawn(async move { run(&task_config, &["--version"]).await });
            let mut pid = fixture_pid(&config);
            for _ in 0..100 {
                if pid.is_ok() {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
                pid = fixture_pid(&config);
            }
            task.abort();
            let result = task.await;
            // If startup failed, abort still precedes any assertion.
            let pid = pid.expect("fixture must start before cancellation");
            assert_terminated(&pid).await;
            assert!(result.unwrap_err().is_cancelled());
        }
    }
}
