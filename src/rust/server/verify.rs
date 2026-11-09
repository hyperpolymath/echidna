// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Verification routes: `/api/verify`, `/api/verify_parallel`, `/api/verify_raw` and the SMT passthrough helpers.

use super::{is_empty_state, AppError};
use anyhow::Result;
use axum::Json;
use echidna::dispatch::ProverDispatcher;
use echidna::{ProverConfig, ProverKind};
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// Verify proof endpoint
pub(super) async fn verify_handler(
    Json(req): Json<VerifyRequest>,
) -> Result<Json<VerifyResponse>, AppError> {
    info!("Verify request for prover: {:?}", req.prover);

    // SMT query mode: when users send raw SMT-LIB with (check-sat) to Z3/CVC5,
    // run passthrough evaluation instead of proof-obligation negation semantics.
    if should_passthrough_smt_eval(&req) {
        let Json(raw) = verify_raw_handler(Json(req.clone())).await?;
        let smt_status = extract_smt_status(&raw.stdout);

        // A completed SMT query is not necessarily a discharged obligation.
        // Only unsat closes a query interpreted as the negated obligation.
        let verified = raw.valid && discharged_smt_queries(&req.content, &raw.stdout);
        let goals_remaining = if verified { 0 } else { 1 };
        let outcome_str = if verified { "PROVED" } else { "NO_PROOF_FOUND" };
        return Ok(Json(VerifyResponse {
            valid: verified,
            outcome: outcome_str.to_string(),
            goals_remaining,
            tactics_used: 0,
            mode: Some("smt-query".to_string()),
            smt_status,
        }));
    }

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof — parse errors surface as INVALID_INPUT in the outcome.
    // We intentionally don't forward the raw error message to the response
    // body (it may leak internal paths or prover internals).
    let state = match prover.parse_string(&req.content).await {
        Ok(s) => s,
        Err(_) => {
            return Ok(Json(VerifyResponse {
                valid: false,
                outcome: "INVALID_INPUT".to_string(),
                goals_remaining: 0,
                tactics_used: 0,
                mode: None,
                smt_status: None,
            }));
        },
    };

    // Fail-fast on empty parse results (see prove_handler comment).
    if is_empty_state(&state) && !req.content.trim().is_empty() {
        return Ok(Json(VerifyResponse {
            valid: false,
            outcome: "INVALID_INPUT".to_string(),
            goals_remaining: 0,
            tactics_used: 0,
            mode: None,
            smt_status: None,
        }));
    }

    // NOTE: a richer `.check()` call returning a `ProverOutcome` taxonomy
    // lived here until 2026-04-17 but the typed-outcome module was never
    // committed (see z3.rs note). Reverted to `verify_proof()` so the HTTP
    // API is no worse than it was before the dropped refactor; the outcome
    // string is a two-valued approximation of the planned taxonomy.
    // Tracked in AI-WORK-todo.md phase-2 followups.
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(VerifyResponse {
        valid,
        outcome: if valid {
            "PROVED".to_string()
        } else {
            "NO_PROOF_FOUND".to_string()
        },
        goals_remaining: if valid { 0 } else { state.goals.len() },
        tactics_used: state.proof_script.len(),
        mode: None,
        smt_status: None,
    }))
}

/// `/api/verify_parallel` — L2 Chapel parallel dispatch.
///
/// Fans out to multiple prover backends simultaneously (when the `chapel`
/// Cargo feature is compiled in and the Chapel runtime is available).
/// Returns the first successful result through the standard trust pipeline.
/// Falls back to sequential `select_prover` heuristic when Chapel is
/// unavailable. Callers that want a specific prover should use `/api/verify`.
pub(super) async fn verify_parallel_handler(
    Json(req): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, AppError> {
    let content = req
        .get("content")
        .and_then(|v| v.as_str())
        .ok_or_else(|| AppError::BadRequest("Missing 'content' field".to_string()))?;

    info!("verify_parallel request ({} bytes)", content.len());

    let dispatcher = ProverDispatcher::new();
    let result = dispatcher
        .verify_proof_parallel(content)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(serde_json::json!({
        "valid": result.verified,
        "outcome": result.outcome.status_str(),
        "provers_used": result.provers_used,
        "trust_level": result.trust_level as u8,
        "proof_time_ms": result.proof_time_ms,
        "goals_remaining": result.goals_remaining,
        "cross_checked": result.cross_checked,
        "message": result.message,
    })))
}

/// `/api/verify_raw` — writes the original `content` to a temp file with
/// the right extension for the prover, then invokes the backend binary
/// directly. Bypasses `parse_string`/`export` round-trip entirely — the
/// content you send is the content the prover sees.
///
/// This is the real fix for the parse+export round-trip bug: no
/// information is lost between the wire and the prover binary.
/// Currently supports: z3, cvc5, coq, lean, agda, idris2, vampire,
/// eprover. Other provers fall through to the legacy verify_handler path.
#[instrument(skip(req))]
pub(super) async fn verify_raw_handler(
    Json(req): Json<VerifyRequest>,
) -> Result<Json<VerifyRawResponse>, AppError> {
    use tokio::process::Command;

    info!("Verify_raw request for prover: {:?}", req.prover);

    if req.content.trim().is_empty() {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: "empty content".to_string(),
        }));
    }

    type Interpret = fn(i32, &str, &str) -> (bool, String);
    let (ext, program, args, interpret): (&str, &str, Vec<String>, Interpret) = match req.prover {
        echidna::provers::ProverKind::Z3 => (
            "smt2",
            "z3",
            vec!["-smt2".to_string()],
            |rc, stdout, _stderr| {
                let produced = stdout.contains("sat")
                    || stdout.contains("unsat")
                    || stdout.contains("unknown");
                (rc == 0 && produced, format!("exit={} smt-output", rc))
            },
        ),
        echidna::provers::ProverKind::CVC5 => ("smt2", "cvc5", vec![], |rc, stdout, _stderr| {
            let produced =
                stdout.contains("sat") || stdout.contains("unsat") || stdout.contains("unknown");
            (rc == 0 && produced, format!("exit={} smt-output", rc))
        }),
        echidna::provers::ProverKind::Coq => (
            "v",
            "coqc",
            vec!["-q".to_string()],
            |rc, _stdout, _stderr| (rc == 0, format!("exit={}", rc)),
        ),
        echidna::provers::ProverKind::Lean => ("lean", "lean", vec![], |rc, _stdout, _stderr| {
            (rc == 0, format!("exit={}", rc))
        }),
        echidna::provers::ProverKind::Agda => ("agda", "agda", vec![], |rc, _stdout, _stderr| {
            (rc == 0, format!("exit={}", rc))
        }),
        echidna::provers::ProverKind::Idris2 => (
            "idr",
            "idris2",
            vec!["--check".to_string()],
            |rc, _stdout, _stderr| (rc == 0, format!("exit={}", rc)),
        ),
        echidna::provers::ProverKind::Vampire => (
            "p",
            "vampire",
            vec!["--mode".to_string(), "casc".to_string()],
            |rc, stdout, _stderr| {
                let theorem = stdout.contains("SZS status Theorem")
                    || stdout.contains("SZS status Unsatisfiable");
                (rc == 0 || theorem, "szs-status".to_string())
            },
        ),
        echidna::provers::ProverKind::EProver => (
            "p",
            "eprover",
            vec!["--auto-schedule".to_string()],
            |rc, stdout, _stderr| {
                let theorem = stdout.contains("SZS status Theorem")
                    || stdout.contains("SZS status Unsatisfiable")
                    || stdout.contains("SZS status ContradictoryAxioms");
                (rc == 0 && theorem, "szs-status".to_string())
            },
        ),
        _ => {
            return Ok(Json(VerifyRawResponse {
                valid: false,
                exit_code: -1,
                stdout: String::new(),
                stderr: String::new(),
                message: format!(
                    "verify_raw not yet implemented for {:?} — use /api/verify",
                    req.prover
                ),
            }));
        },
    };

    // Write content to a unique temp file with the right extension.
    let tmpdir = std::env::temp_dir().join(format!("echidna_verify_raw_{}", std::process::id()));
    if let Err(e) = tokio::fs::create_dir_all(&tmpdir).await {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("tmpdir create failed: {}", e),
        }));
    }
    let filename = format!("Input.{}", ext);
    let path = tmpdir.join(&filename);
    if let Err(e) = tokio::fs::write(&path, req.content.as_bytes()).await {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("write failed: {}", e),
        }));
    }

    // Run the prover. cd to tmpdir for provers that care about module
    // name = filename (agda, coq, idris2, lean).
    let mut cmd = Command::new(program);
    cmd.current_dir(&tmpdir);
    for arg in &args {
        cmd.arg(arg);
    }
    cmd.arg(&filename);

    let output_result = cmd.output().await;
    // Best-effort cleanup; ignore errors.
    let _ = tokio::fs::remove_dir_all(&tmpdir).await;

    match output_result {
        Ok(output) => {
            let exit_code = output.status.code().unwrap_or(-1);
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let (valid, message) = interpret(exit_code, &stdout, &stderr);
            Ok(Json(VerifyRawResponse {
                valid,
                exit_code,
                stdout: stdout.chars().take(1024).collect(),
                stderr: stderr.chars().take(1024).collect(),
                message,
            }))
        },
        Err(e) => Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("spawn failed: {} (is the '{}' binary on PATH?)", e, program),
        })),
    }
}

fn should_passthrough_smt_eval(req: &VerifyRequest) -> bool {
    matches!(req.prover, ProverKind::Z3 | ProverKind::CVC5)
        && req.content.to_ascii_lowercase().contains("(check-sat")
}

fn extract_smt_status(text: &str) -> Option<String> {
    // Result tokens are case-sensitive, standalone SMT-LIB responses.
    // A satisfiable or unknown query prevents an aggregate proof claim.
    let statuses: Vec<_> = text
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    ["sat", "unknown", "unsat"]
        .into_iter()
        .find(|status| statuses.contains(status))
        .map(str::to_owned)
}

fn discharged_smt_queries(source: &str, stdout: &str) -> bool {
    let Some(commands) = smt_commands(source) else {
        return false;
    };
    // Z3 emits echo strings without quotes. Never authenticate an echoed
    // "unsat" as a solver answer, including echo+exit before a query.
    if commands
        .iter()
        .any(|command| matches!(*command, "echo" | "exit"))
    {
        return false;
    }
    let queries = commands
        .iter()
        .filter(|command| matches!(**command, "check-sat" | "check-sat-assuming"))
        .count();
    let statuses: Vec<_> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    queries > 0 && statuses.len() == queries && statuses.iter().all(|status| *status == "unsat")
}

/// Read command names only; the real solver still validates SMT-LIB terms.
/// Strings, quoted symbols and line comments cannot introduce commands.
fn smt_commands(source: &str) -> Option<Vec<&str>> {
    let bytes = source.as_bytes();
    let mut commands = Vec::new();
    let (mut index, mut depth) = (0, 0usize);
    while index < bytes.len() {
        match bytes[index] {
            b';' => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            },
            b'"' | b'|' => {
                if depth == 0 {
                    return None;
                }
                let delimiter = bytes[index];
                index += 1;
                loop {
                    if index == bytes.len() {
                        return None;
                    }
                    if bytes[index] == delimiter {
                        index += 1;
                        if delimiter == b'"' && bytes.get(index) == Some(&b'"') {
                            index += 1;
                        } else {
                            break;
                        }
                    } else {
                        index += 1;
                    }
                }
            },
            b'(' => {
                if depth == 0 {
                    index += 1;
                    // Whitespace and comments are legal before the command.
                    loop {
                        while bytes.get(index).is_some_and(u8::is_ascii_whitespace) {
                            index += 1;
                        }
                        if bytes.get(index) != Some(&b';') {
                            break;
                        }
                        while index < bytes.len() && bytes[index] != b'\n' {
                            index += 1;
                        }
                    }
                    let start = index;
                    while bytes
                        .get(index)
                        .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'-')
                    {
                        index += 1;
                    }
                    if index == start
                        || !bytes
                            .get(index)
                            .is_some_and(|b| b.is_ascii_whitespace() || matches!(b, b')' | b';'))
                    {
                        return None;
                    }
                    commands.push(&source[start..index]);
                } else {
                    index += 1;
                }
                depth += 1;
            },
            b')' => {
                depth = depth.checked_sub(1)?;
                index += 1;
            },
            byte if byte.is_ascii_whitespace() => {
                index += 1;
            },
            _ => {
                if depth == 0 {
                    return None;
                }
                index += 1;
            },
        }
    }
    (depth == 0).then_some(commands)
}

// ========== Request/Response Types ==========

#[derive(Clone, Deserialize)]
pub(super) struct VerifyRequest {
    prover: ProverKind,
    content: String,
}

#[derive(Serialize)]
pub(super) struct VerifyResponse {
    valid: bool,
    /// Typed outcome from the prover — one of PROVED, NO_PROOF_FOUND,
    /// INVALID_INPUT, UNSUPPORTED_FEATURE, TIMEOUT, INCONSISTENT_PREMISES,
    /// PROVER_ERROR, SYSTEM_ERROR.
    ///
    /// This is the primary result field; `valid` is a backward-compatible bool
    /// summary derived from it (true iff outcome == PROVED).
    outcome: String,
    goals_remaining: usize,
    tactics_used: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    smt_status: Option<String>,
}

/// Raw-content verification response. Skips `parse_string`/`export` round
/// trip and invokes the prover binary directly on the supplied content.
#[derive(Serialize)]
pub(super) struct VerifyRawResponse {
    valid: bool,
    exit_code: i32,
    stdout: String,
    stderr: String,
    message: String,
}
