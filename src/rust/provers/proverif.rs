// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! ProVerif Security Protocol Verifier Backend
//!
//! ProVerif is an automatic cryptographic protocol verifier based on the
//! applied pi-calculus. It takes .pv files as input and can verify:
//!
//! - **Reachability properties**: Can certain states be reached?
//! - **Correspondence assertions**: If event A occurs, then event B must have occurred
//! - **Observational equivalence**: Two processes are indistinguishable to an attacker
//!
//! ProVerif models protocols as processes in the applied pi-calculus with
//! user-defined reduction rules for cryptographic primitives (e.g. symmetric/
//! asymmetric encryption, hashing, signatures, Diffie-Hellman).
//!
//! Unlike Tamarin, ProVerif is fully automated — there is no interactive
//! proof mode. It either proves the property, finds an attack trace, or
//! reports that the property cannot be proved (potential false positive).
//!
//! Output parsing keys:
//! - `RESULT ... is true.` — property verified
//! - `RESULT ... is false.` — attack found (counterexample)
//! - `RESULT ... cannot be proved.` — inconclusive (overapproximation)

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// ProVerif cryptographic protocol verifier backend
///
/// Integrates the ProVerif tool for automatic verification of security
/// protocols modelled in the applied pi-calculus. ProVerif reasons about
/// an unbounded number of sessions and uses Horn clause resolution with
/// careful abstraction to achieve termination in most practical cases.
///
/// Input files use the .pv format with process declarations, equational
/// theories for cryptographic primitives, and query declarations for
/// the properties to verify.
///
/// ProVerif is fully automated — it does not support interactive tactics.
/// The `apply_tactic` method will return an error for any tactic that
/// requires interactive guidance.
pub struct ProVerifBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl ProVerifBackend {
    /// Create a new ProVerif backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        ProVerifBackend { config }
    }

    /// Convert proof state to ProVerif .pv format
    ///
    /// Generates a valid ProVerif input script from the ECHIDNA proof state.
    /// Axioms become declarations (types, functions, equations, reductions),
    /// definitions become free names/constants, and goals become queries.
    fn to_pv(&self, state: &ProofState) -> Result<String> {
        let mut pv = String::new();

        // Header comment
        pv.push_str("(* ECHIDNA ProVerif Export *)\n\n");

        // Default channel declaration — ProVerif needs at least one channel
        pv.push_str("free c: channel.\n\n");

        // Add definitions as type/function/free declarations
        //
        // Definition.name holds the declaration keyword + name (e.g. "type key")
        // Definition.body holds the full ProVerif syntax line when available
        for def in &state.context.definitions {
            let body_str = format!("{}", def.body);
            let name_str = &def.name;

            // If the body contains ProVerif syntax, emit it directly
            if body_str.starts_with("type ")
                || body_str.starts_with("free ")
                || body_str.starts_with("fun ")
                || body_str.starts_with("reduc ")
                || body_str.starts_with("equation ")
                || body_str.starts_with("const ")
                || body_str.starts_with("table ")
                || body_str.starts_with("letfun ")
            {
                pv.push_str(&body_str);
                if !body_str.ends_with('.') {
                    pv.push('.');
                }
                pv.push('\n');
            } else if name_str.starts_with("type ")
                || name_str.starts_with("free ")
                || name_str.starts_with("fun ")
                || name_str.starts_with("reduc ")
                || name_str.starts_with("equation ")
                || name_str.starts_with("const ")
                || name_str.starts_with("table ")
                || name_str.starts_with("letfun ")
            {
                // Name field carries the full declaration
                pv.push_str(name_str);
                if !name_str.ends_with('.') {
                    pv.push('.');
                }
                pv.push('\n');
            } else {
                // Wrap as a comment placeholder
                pv.push_str(&format!("(* definition: {} *)\n", def));
            }
        }

        pv.push('\n');

        // Add axioms as process declarations, events, or raw ProVerif constructs
        for (i, axiom) in state.context.axioms.iter().enumerate() {
            if axiom.starts_with("event ")
                || axiom.starts_with("let ")
                || axiom.starts_with("process ")
                || axiom.starts_with("fun ")
                || axiom.starts_with("reduc ")
                || axiom.starts_with("equation ")
                || axiom.starts_with("type ")
                || axiom.starts_with("free ")
                || axiom.starts_with("table ")
                || axiom.starts_with("not ")
            {
                pv.push_str(axiom);
                if !axiom.ends_with('.') {
                    pv.push('.');
                }
                pv.push('\n');
            } else {
                // Wrap as a commented axiom placeholder
                pv.push_str(&format!("(* axiom_{}: {} *)\n", i, axiom));
            }
        }

        pv.push('\n');

        // Add goals as queries to verify
        for goal in &state.goals {
            let target_str = format!("{}", goal.target);

            // If the target already contains a query declaration, use it directly
            if target_str.starts_with("query ") {
                pv.push_str(&target_str);
                if !target_str.ends_with('.') {
                    pv.push('.');
                }
                pv.push('\n');
            } else if target_str.starts_with("attacker(") {
                // Secrecy query shorthand
                pv.push_str(&format!("query {}.", target_str));
                pv.push('\n');
            } else {
                // Wrap as a generic reachability/correspondence query
                pv.push_str(&format!(
                    "(* goal {}: {} *)\nquery {}.\n",
                    goal.id, target_str, target_str
                ));
            }
        }

        pv.push('\n');

        // Add a minimal process if none was declared via axioms
        let has_process = state
            .context
            .axioms
            .iter()
            .any(|a| a.starts_with("process "));
        if !has_process {
            pv.push_str("process\n  0\n");
        }

        Ok(pv)
    }

    /// Parse ProVerif verification output to determine success or failure
    ///
    /// ProVerif reports one RESULT line per query:
    /// - `RESULT ... is true.` — the property holds
    /// - `RESULT ... is false.` — an attack was found
    /// - `RESULT ... cannot be proved.` — inconclusive (sound overapproximation)
    ///
    /// Returns `Ok(true)` only if all results are `true`.
    /// Returns `Ok(false)` if any result is `false`.
    /// Returns `Err` if any result is inconclusive or parsing fails.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let mut found_any_result = false;
        let all_true = true;

        for line in output.lines() {
            let trimmed = line.trim();

            if !trimmed.starts_with("RESULT ") {
                continue;
            }

            found_any_result = true;

            if trimmed.contains("is false") {
                // Attack found — property violated
                return Ok(false);
            } else if trimmed.contains("cannot be proved") {
                // Inconclusive — ProVerif's abstraction could not decide
                return Err(anyhow!(
                    "ProVerif inconclusive: property cannot be proved (possible false positive). \
                     Line: {}",
                    trimmed
                ));
            } else if trimmed.contains("is true") {
                // This query verified successfully
                // (all_true remains true)
            } else {
                // Unexpected RESULT format
                return Err(anyhow!("ProVerif unexpected RESULT format: {}", trimmed));
            }
        }

        // Check for parse errors in ProVerif output
        if output.contains("Syntax error") || output.contains("Error:") {
            return Err(anyhow!(
                "ProVerif error: {}",
                output
                    .lines()
                    .filter(|l| {
                        l.contains("Syntax error") || l.contains("Error:") || l.contains("error")
                    })
                    .take(5)
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }

        if !found_any_result {
            return Err(anyhow!(
                "ProVerif produced no RESULT lines: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        Ok(all_true)
    }

    /// Parse a .pv file to extract declarations, processes, events,
    /// and queries into the proof state
    fn parse_pv(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();

        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty()
                || trimmed.starts_with("(*")
                || trimmed.starts_with("*)")
                || trimmed.starts_with("*")
            {
                continue;
            }

            // Type declarations → definitions
            if trimmed.starts_with("type ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Free name/channel declarations → definitions
            if trimmed.starts_with("free ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Function symbol declarations → definitions
            if trimmed.starts_with("fun ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Reduction rules (destructor definitions) → definitions
            if trimmed.starts_with("reduc ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Equations (equational theories) → definitions
            if trimmed.starts_with("equation ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Constant declarations → definitions
            if trimmed.starts_with("const ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Table declarations → definitions
            if trimmed.starts_with("table ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Let function bindings → definitions
            if trimmed.starts_with("letfun ") {
                state.context.definitions.push(pv_definition(trimmed));
                continue;
            }

            // Event declarations → axioms
            if trimmed.starts_with("event ") {
                state.context.axioms.push(trimmed.to_string());
                continue;
            }

            // Process declarations → axioms
            if trimmed.starts_with("let ") && !trimmed.starts_with("letfun ") {
                state.context.axioms.push(trimmed.to_string());
                continue;
            }

            // Not declarations (for secrecy assumptions) → axioms
            if trimmed.starts_with("not ") {
                state.context.axioms.push(trimmed.to_string());
                continue;
            }

            // Queries → goals
            if trimmed.starts_with("query ") {
                // Extract the query body (strip "query " prefix and trailing ".")
                let query_body = trimmed
                    .trim_start_matches("query ")
                    .trim_end_matches('.')
                    .trim()
                    .to_string();

                // Derive a goal ID from the query content
                let goal_id = if query_body.contains("attacker(") {
                    // Secrecy query — name after the secret
                    let inner = query_body
                        .trim_start_matches("attacker(")
                        .trim_end_matches(')')
                        .to_string();
                    format!("secrecy_{}", sanitise_id(&inner))
                } else if query_body.contains("event(") || query_body.contains("inj-event(") {
                    format!("correspondence_{}", state.goals.len())
                } else {
                    format!("query_{}", state.goals.len())
                };

                state.goals.push(Goal {
                    id: goal_id,
                    target: Term::Const(format!("query {}", query_body)),
                    hypotheses: vec![],
                });
                continue;
            }
        }

        Ok(state)
    }
}

/// Sanitise a string into a valid identifier (alphanumeric + underscore)
fn sanitise_id(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Create a Definition from a ProVerif declaration line
///
/// Stores the full declaration text in both name and body fields so
/// round-tripping through to_pv() preserves the original syntax.
fn pv_definition(line: &str) -> Definition {
    // Extract keyword + identifier from the line for the name field
    // e.g. "type key." → "type key", "fun senc(bitstring, key): bitstring." → "fun senc"
    let clean = line.trim_end_matches('.');
    let name = clean
        .split(['(', ':'])
        .next()
        .unwrap_or(clean)
        .trim()
        .to_string();

    Definition {
        name,
        ty: Term::Const("proverif_decl".to_string()),
        body: Term::Const(clean.to_string()),
        type_info: None,
    }
}

#[async_trait]
impl ProverBackend for ProVerifBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::ProVerif
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--help")
            .output()
            .await
            .context("Failed to run proverif --help (ProVerif has no --version flag)")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // ProVerif typically prints version info in the first line of --help or banner
        let combined = format!("{}\n{}", stdout, stderr);
        let version = combined
            .lines()
            .find(|l| l.contains("ProVerif") || l.contains("proverif") || l.contains("version"))
            .unwrap_or("ProVerif (unknown version)")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read .pv file")?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = self.parse_pv(content)?;
        state.metadata.insert(
            "proverif_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, _state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // ProVerif is fully automated — no interactive tactic support.
        // Users should modify the protocol model or queries instead.
        Ok(TacticResult::Error(format!(
            "ProVerif is fully automated and does not support interactive tactics. \
             Tactic {:?} cannot be applied. Modify the .pv model or queries instead.",
            tactic
        )))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 10),
                Command::new(&self.config.executable)
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| {
                anyhow!(
                    "ProVerif verification timed out after {} seconds",
                    self.config.timeout
                )
            })?
            .context("Failed to execute proverif")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return self.parse_result(&combined);
        }
        let pv_code = if let Some(src) = state
            .metadata
            .get("proverif_source")
            .and_then(|v| v.as_str())
        {
            src.to_string()
        } else {
            self.to_pv(state)?
        };

        // Write .pv to a temporary file (proverif requires a file path)
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for ProVerif")?;
        let tmp_file = tmp_dir.path().join("protocol.pv");
        tokio::fs::write(&tmp_file, &pv_code)
            .await
            .context("Failed to write temporary .pv file")?;

        // Run proverif on the .pv file
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 10),
            Command::new(&self.config.executable)
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| {
            anyhow!(
                "ProVerif verification timed out after {} seconds",
                self.config.timeout
            )
        })?
        .context("Failed to execute proverif")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Combine stdout and stderr for parsing (ProVerif outputs results to stdout)
        let combined = format!("{}\n{}", stdout, stderr);

        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_pv(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        // ProVerif is fully automated — no tactics to suggest.
        // Return empty list rather than error, since this is an advisory call.
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a test backend instance
    fn test_backend() -> ProVerifBackend {
        let config = ProverConfig {
            executable: PathBuf::from("proverif"),
            timeout: 60,
            ..Default::default()
        };
        ProVerifBackend::new(config)
    }

    #[tokio::test]
    async fn test_proverif_pv_export() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: "secrecy_s".to_string(),
            target: Term::Const("query attacker(s).".to_string()),
            hypotheses: vec![],
        });

        let pv = backend.to_pv(&state).unwrap();

        assert!(pv.contains("ECHIDNA ProVerif Export"));
        assert!(pv.contains("free c: channel."));
        assert!(pv.contains("attacker(s)"));
    }

    #[tokio::test]
    async fn test_proverif_pv_export_with_definitions() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state.context.definitions.push(pv_definition("type key."));
        state
            .context
            .definitions
            .push(pv_definition("fun senc(bitstring, key): bitstring."));
        state.context.definitions.push(pv_definition(
            "reduc forall m: bitstring, k: key; sdec(senc(m, k), k) = m.",
        ));

        state.goals.push(Goal {
            id: "secrecy_s".to_string(),
            target: Term::Const("query attacker(s)".to_string()),
            hypotheses: vec![],
        });

        let pv = backend.to_pv(&state).unwrap();

        assert!(pv.contains("type key."));
        assert!(pv.contains("fun senc(bitstring, key): bitstring."));
        assert!(pv.contains("reduc forall m: bitstring, k: key; sdec(senc(m, k), k) = m."));
        assert!(pv.contains("query attacker(s)."));
    }

    #[tokio::test]
    async fn test_proverif_parse_pv() {
        let backend = test_backend();

        let pv_source = r#"
(* Simple Needham-Schroeder example *)

free c: channel.

type key.
type nonce.

fun senc(bitstring, key): bitstring.
reduc forall m: bitstring, k: key; sdec(senc(m, k), k) = m.

free s: bitstring [private].

event beginA(nonce).
event endB(nonce).

query attacker(s).
query event(endB(x)) ==> event(beginA(x)).

let processA =
    new na: nonce;
    event beginA(na);
    out(c, na).

let processB =
    in(c, x: nonce);
    event endB(x);
    out(c, senc(s, new key)).

process
    (!processA | !processB)
"#;

        let state = backend.parse_string(pv_source).await.unwrap();

        // Should have found type, free, fun, reduc as definitions
        assert!(
            state
                .context
                .definitions
                .iter()
                .any(|d| d.name.contains("type key")),
            "Should have parsed type declaration"
        );
        assert!(
            state
                .context
                .definitions
                .iter()
                .any(|d| d.name.contains("free c")),
            "Should have parsed free channel declaration"
        );
        assert!(
            state
                .context
                .definitions
                .iter()
                .any(|d| d.name.contains("fun senc")),
            "Should have parsed function declaration"
        );
        assert!(
            state
                .context
                .definitions
                .iter()
                .any(|d| d.name.starts_with("reduc")),
            "Should have parsed reduction rule"
        );

        // Should have found event declarations as axioms
        assert!(
            state
                .context
                .axioms
                .iter()
                .any(|a| a.contains("event beginA")),
            "Should have parsed event declaration"
        );

        // Should have found both queries as goals
        assert_eq!(state.goals.len(), 2, "Should have parsed two queries");
        assert!(
            state.goals[0].id.contains("secrecy"),
            "First goal should be secrecy query"
        );
        assert!(
            state.goals[1].id.contains("correspondence"),
            "Second goal should be correspondence query"
        );
    }

    #[test]
    fn test_proverif_parse_result_true() {
        let backend = test_backend();

        let output = "\
Verification summary:\n\
\n\
Query not attacker(s[]) is true.\n\
\n\
RESULT not attacker(s[]) is true.\n";

        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_proverif_parse_result_false() {
        let backend = test_backend();

        let output = "\
RESULT not attacker(s[]) is false.\n";

        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_proverif_parse_result_cannot_be_proved() {
        let backend = test_backend();

        let output = "\
RESULT event(endB(x)) ==> event(beginA(x)) cannot be proved.\n";

        assert!(
            backend.parse_result(output).is_err(),
            "Inconclusive result should return error"
        );
    }

    #[test]
    fn test_proverif_parse_result_multiple_true() {
        let backend = test_backend();

        let output = "\
RESULT not attacker(s[]) is true.\n\
RESULT event(endB(x)) ==> event(beginA(x)) is true.\n";

        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_proverif_parse_result_mixed() {
        let backend = test_backend();

        let output = "\
RESULT not attacker(s[]) is true.\n\
RESULT event(endB(x)) ==> event(beginA(x)) is false.\n";

        // Any false result means overall false
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_proverif_parse_result_syntax_error() {
        let backend = test_backend();

        let output = "Error: Syntax error at line 5.\n";

        assert!(
            backend.parse_result(output).is_err(),
            "Syntax error should return error"
        );
    }

    #[test]
    fn test_proverif_parse_result_no_results() {
        let backend = test_backend();

        let output = "ProVerif 2.05\nSome other output\n";

        assert!(
            backend.parse_result(output).is_err(),
            "No RESULT lines should return error"
        );
    }

    #[tokio::test]
    async fn test_proverif_apply_tactic_returns_error() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "proverif".to_string(),
            command: "some_tactic".to_string(),
            args: vec![],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();

        match result {
            TacticResult::Error(msg) => {
                assert!(
                    msg.contains("fully automated"),
                    "Error message should explain ProVerif is automated"
                );
            },
            _ => panic!("apply_tactic should return TacticResult::Error for ProVerif"),
        }
    }

    #[tokio::test]
    async fn test_proverif_suggest_tactics_empty() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 10).await.unwrap();
        assert!(
            tactics.is_empty(),
            "ProVerif should suggest no tactics (fully automated)"
        );
    }

    #[test]
    fn test_sanitise_id() {
        assert_eq!(sanitise_id("hello_world"), "hello_world");
        assert_eq!(sanitise_id("foo.bar"), "foo_bar");
        assert_eq!(sanitise_id("s[]"), "s__");
        assert_eq!(sanitise_id("key-pair"), "key_pair");
    }
}
