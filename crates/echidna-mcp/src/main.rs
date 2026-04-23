// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA MCP Server — exposes the `echidna` CLI as Model Context Protocol
//! tools so Claude Code / Claude API agents can call on the 105-prover
//! portfolio as first-class tool-use actions.
//!
//! # Running
//!
//! ```sh
//! echidna-mcp                          # serves on stdio (default MCP transport)
//! ECHIDNA_BIN=/abs/path/echidna echidna-mcp
//! ```
//!
//! # Claude Code integration
//!
//! Add to `.claude/settings.json`:
//!
//! ```json
//! { "mcpServers": { "echidna": { "command": "echidna-mcp" } } }
//! ```

use rmcp::{
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    model::{ServerCapabilities, ServerInfo},
    schemars::JsonSchema,
    tool, tool_handler, tool_router,
    transport::stdio,
    ServerHandler, ServiceExt,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::process::Command;

fn echidna_bin() -> String {
    std::env::var("ECHIDNA_BIN").unwrap_or_else(|_| "echidna".to_string())
}

#[derive(Debug, Deserialize, Serialize, JsonSchema)]
struct ProveParams {
    /// Absolute path to the proof file. Accepted formats depend on the
    /// chosen prover: SMT-LIB `.smt2` for Z3/CVC5/etc., Lean `.lean` for
    /// Lean 4, Coq `.v` for Coq/Rocq, Agda `.agda`, Isabelle `.thy`,
    /// Mizar `.miz`, F* `.fst`, SPASS DFG `.dfg`, Metamath `.mm`, etc.
    pub file: String,

    /// Prover backend name (case-sensitive). Common values: `Z3`, `Lean`,
    /// `Coq`, `Agda`, `Isabelle`, `Mizar`, `FStar`, `SPASS`, `Vampire`,
    /// `CVC5`, `Metamath`. If omitted, ECHIDNA auto-detects from the file
    /// extension.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prover: Option<String>,

    /// Timeout in seconds for the prover invocation. Default 300.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_secs: Option<u32>,
}

#[derive(Debug, Serialize)]
struct ProveResult {
    verified: bool,
    message: String,
    prover: Option<String>,
    raw_output: String,
    stderr: String,
}

#[derive(Debug, Deserialize, Serialize, JsonSchema)]
struct CheckProverParams {
    /// Prover backend name to check (case-sensitive). Examples: `Z3`, `Lean`,
    /// `Coq`, `Agda`, `Isabelle`, `Vampire`, `CVC5`, `Metamath`.
    pub prover: String,
}

#[derive(Debug, Serialize)]
struct CheckProverResult {
    /// Whether the prover binary was found and is executable.
    available: bool,
    /// Human-readable status message.
    message: String,
}

#[derive(Debug, Serialize)]
struct ListProversResult {
    /// Total number of supported prover backends.
    total: usize,
    /// Map from prover name to a brief description.
    provers: HashMap<String, String>,
}

#[derive(Clone)]
struct EchidnaMcp {
    tool_router: ToolRouter<Self>,
}

impl EchidnaMcp {
    pub fn new() -> Self {
        Self {
            tool_router: Self::tool_router(),
        }
    }
}

#[tool_router(router = tool_router)]
impl EchidnaMcp {
    /// Prove a theorem using one of ECHIDNA's 105 prover backends.
    #[tool(
        name = "prove",
        description = "Prove a theorem from a file using ECHIDNA's 105-prover \
                       portfolio. Returns a JSON object with {verified, message, \
                       prover, raw_output, stderr}. Common provers: Z3, Lean, Coq, \
                       Agda, Isabelle, Mizar, FStar, SPASS, Metamath."
    )]
    pub async fn prove(&self, params: Parameters<ProveParams>) -> String {
        let ProveParams {
            file,
            prover,
            timeout_secs,
        } = params.0;

        let mut cmd = Command::new(echidna_bin());
        cmd.arg("prove").arg(&file).arg("--format").arg("json");
        if let Some(p) = prover.as_deref() {
            cmd.arg("-p").arg(p);
        }
        let timeout = timeout_secs.unwrap_or(300);
        cmd.arg("-t").arg(timeout.to_string());

        let output = match cmd.output().await {
            Ok(o) => o,
            Err(e) => {
                let result = ProveResult {
                    verified: false,
                    message: format!("Failed to invoke echidna: {e}"),
                    prover,
                    raw_output: String::new(),
                    stderr: String::new(),
                };
                return serde_json::to_string_pretty(&result).unwrap_or_default();
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

        let verified = stdout.contains("\"level\": \"success\"")
            || stdout.contains("\"level\":\"success\"");
        let message = extract_first_message(&stdout).unwrap_or_else(|| {
            if stderr.is_empty() {
                "(no output)".to_string()
            } else {
                stderr.lines().take(5).collect::<Vec<_>>().join("\n")
            }
        });

        let result = ProveResult {
            verified,
            message,
            prover,
            raw_output: stdout,
            stderr,
        };
        serde_json::to_string_pretty(&result).unwrap_or_default()
    }

    /// Check whether a named prover backend is available on this system.
    #[tool(
        name = "check_prover",
        description = "Check whether a named prover backend is installed and \
                       reachable. Returns {available: bool, message: string}. \
                       Example: check_prover({\"prover\": \"Z3\"})."
    )]
    pub async fn check_prover(&self, params: Parameters<CheckProverParams>) -> String {
        let prover = params.0.prover;

        let mut cmd = Command::new(echidna_bin());
        cmd.arg("check-prover").arg(&prover);

        let result = match cmd.output().await {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
                let available = output.status.success()
                    || stdout.contains("available")
                    || stdout.contains("found");
                let message = if stdout.trim().is_empty() {
                    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                    if stderr.trim().is_empty() {
                        if available {
                            format!("{prover} is available")
                        } else {
                            format!("{prover} is not available")
                        }
                    } else {
                        stderr.lines().take(3).collect::<Vec<_>>().join("\n")
                    }
                } else {
                    stdout.trim().to_string()
                };
                CheckProverResult { available, message }
            }
            Err(e) => CheckProverResult {
                available: false,
                message: format!("Failed to invoke echidna: {e}"),
            },
        };

        serde_json::to_string_pretty(&result).unwrap_or_default()
    }

    /// List all 105 prover backends supported by ECHIDNA.
    #[tool(
        name = "list_provers",
        description = "List all 105 prover backends supported by ECHIDNA, \
                       grouped by category. Returns {total: int, provers: {name: description}}."
    )]
    pub async fn list_provers(&self, _params: Parameters<()>) -> String {
        let mut cmd = Command::new(echidna_bin());
        cmd.arg("list-provers").arg("--format").arg("json");

        match cmd.output().await {
            Ok(output) if output.status.success() => {
                let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
                // Return the raw JSON from the CLI if it looks like JSON, else wrap it.
                if stdout.trim_start().starts_with('{') || stdout.trim_start().starts_with('[') {
                    stdout
                } else {
                    // Wrap plain-text listing as a simple result object.
                    let lines: Vec<&str> = stdout.lines().filter(|l| !l.trim().is_empty()).collect();
                    let provers: HashMap<String, String> = lines
                        .iter()
                        .map(|l| (l.trim().to_string(), String::new()))
                        .collect();
                    let result = ListProversResult {
                        total: provers.len(),
                        provers,
                    };
                    serde_json::to_string_pretty(&result).unwrap_or_default()
                }
            }
            Ok(output) => {
                let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                let result = serde_json::json!({
                    "error": format!("echidna list-provers failed: {}", stderr.trim())
                });
                serde_json::to_string_pretty(&result).unwrap_or_default()
            }
            Err(e) => {
                let result = serde_json::json!({
                    "error": format!("Failed to invoke echidna: {e}")
                });
                serde_json::to_string_pretty(&result).unwrap_or_default()
            }
        }
    }
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for EchidnaMcp {
    fn get_info(&self) -> ServerInfo {
        let mut info = ServerInfo::default();
        info.capabilities = ServerCapabilities::builder().enable_tools().build();
        info.instructions = Some(
            "ECHIDNA MCP server. Call `prove` with a proof-file path and \
             (optionally) a prover name to run a theorem prover from \
             ECHIDNA's 105-backend portfolio."
                .into(),
        );
        info
    }
}

/// Parse the first `"message": "..."` value out of ECHIDNA's stdout.
fn extract_first_message(stdout: &str) -> Option<String> {
    let needle = "\"message\"";
    let start = stdout.find(needle)?;
    let rest = &stdout[start + needle.len()..];
    let colon = rest.find(':')?;
    let after_colon = &rest[colon + 1..];
    let q1 = after_colon.find('"')?;
    let after_q1 = &after_colon[q1 + 1..];
    let bytes = after_q1.as_bytes();
    let mut end = 0;
    while end < bytes.len() {
        if bytes[end] == b'\\' && end + 1 < bytes.len() {
            end += 2;
            continue;
        }
        if bytes[end] == b'"' {
            break;
        }
        end += 1;
    }
    Some(after_q1[..end].to_string())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("echidna_mcp=info")),
        )
        .with_writer(std::io::stderr)
        .init();

    let service = EchidnaMcp::new().serve(stdio()).await?;
    service.waiting().await?;
    Ok(())
}
