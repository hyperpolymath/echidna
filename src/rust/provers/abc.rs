// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! ABC Logic Synthesis and Formal Verification Backend
//!
//! ABC is a system for sequential synthesis and verification of hardware
//! designs developed at UC Berkeley. It uses And-Inverter Graphs (AIGs)
//! as its core data structure and provides multiple verification engines.
//!
//! Input formats:
//! - AIGER (.aig) — binary AIG format for safety properties
//! - BLIF (.blif) — Berkeley Logic Interchange Format
//! - Verilog (.v) — structural/RTL Verilog (gate-level and limited behavioral)
//! - ABC script commands — inline verification scripts
//!
//! Verification engines:
//! - `pdr` — Property Directed Reachability (IC3 algorithm)
//! - `bmc` / `bmc3` — Bounded Model Checking
//! - `int` — Interpolation-based model checking
//! - `dprove` — Complete multi-engine verification
//! - `dsec` — Sequential equivalence checking
//! - `cec` — Combinational equivalence checking
//!
//! Output parsing:
//! - "Property proved" — property holds on all reachable states
//! - "Output N is SAT" — counterexample found (property violation)
//! - "UNDECIDED" — verification inconclusive within resource limits

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Definition, Goal, ProofState, Tactic, TacticResult, Term};

/// ABC logic synthesis and formal verification backend
///
/// Integrates the Berkeley ABC system for hardware verification using
/// And-Inverter Graphs (AIGs). Supports property directed reachability
/// (PDR/IC3), bounded model checking (BMC), interpolation, and
/// sequential/combinational equivalence checking.
pub struct AbcBackend {
    /// Backend configuration (executable path, timeout, etc.)
    config: ProverConfig,
}

impl AbcBackend {
    /// Create a new ABC backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        AbcBackend { config }
    }

    /// Convert proof state to an ABC verification script
    ///
    /// Generates a sequence of ABC commands that:
    /// 1. Reads the design from axioms (AIGER, BLIF, or Verilog)
    /// 2. Applies any specified verification engine
    /// 3. Reports property status
    ///
    /// If axioms contain raw ABC commands (detected by `read` keyword),
    /// they are emitted directly. Otherwise, the state is converted to
    /// an inline AIGER-like description with property goals.
    fn to_abc_script(&self, state: &ProofState) -> Result<String> {
        let mut script = String::new();

        // Header comment
        script.push_str("# ECHIDNA ABC Export\n\n");

        // Check if any axiom contains raw ABC commands
        let has_raw_commands = state.context.axioms.iter().any(|a| {
            a.starts_with("read")
                || a.starts_with("read_aiger")
                || a.starts_with("read_blif")
                || a.starts_with("read_verilog")
        });

        if has_raw_commands {
            // Emit raw ABC commands from axioms directly
            for axiom in &state.context.axioms {
                script.push_str(axiom);
                script.push('\n');
            }
        } else {
            // If axioms contain a file path reference, generate a read command
            for axiom in &state.context.axioms {
                if axiom.ends_with(".aig") {
                    script.push_str(&format!("read_aiger {}\n", axiom));
                } else if axiom.ends_with(".blif") {
                    script.push_str(&format!("read_blif {}\n", axiom));
                } else if axiom.ends_with(".v") {
                    script.push_str(&format!("read_verilog {}\n", axiom));
                } else {
                    // Treat as an inline ABC command
                    script.push_str(axiom);
                    script.push('\n');
                }
            }
        }

        // Determine verification method from metadata or default to pdr
        let method = state
            .metadata
            .get("abc_method")
            .and_then(|v| v.as_str())
            .unwrap_or("pdr");

        // Apply verification method for each goal
        if !state.goals.is_empty() {
            match method {
                "bmc" | "bmc3" => {
                    let bound = state
                        .metadata
                        .get("bmc_bound")
                        .and_then(|v| v.as_str())
                        .unwrap_or("100");
                    script.push_str(&format!("bmc3 -F {}\n", bound));
                },
                "int" => {
                    script.push_str("int\n");
                },
                "dprove" => {
                    script.push_str("dprove\n");
                },
                "dsec" => {
                    script.push_str("dsec\n");
                },
                "cec" => {
                    script.push_str("cec\n");
                },
                // Default: PDR (IC3) — most commonly used complete engine
                _ => {
                    script.push_str("pdr\n");
                },
            }
        }

        // Print status and quit
        script.push_str("print_status\n");
        script.push_str("quit\n");

        Ok(script)
    }

    /// Parse ABC verification output to determine success or failure
    ///
    /// ABC reports results in several forms:
    /// - "Property proved" — all outputs are UNSAT (property holds)
    /// - "Output N is SAT" — counterexample found at output N
    /// - "UNDECIDED" — verification could not conclude
    /// - "Networks are equivalent" — equivalence checking success (cec/dsec)
    /// - "Networks are NOT equivalent" — equivalence checking failure
    fn parse_result(&self, output: &str) -> Result<bool> {
        let mut found_proved = false;
        let mut found_sat = false;
        let mut found_equiv = false;
        let mut found_error = false;

        for line in output.lines() {
            let trimmed = line.trim();

            // Property proved (PDR/BMC/INT success)
            if trimmed.contains("Property proved")
                || trimmed.contains("property proved")
                || trimmed.contains("UNSAT")
            {
                found_proved = true;
            }

            // Counterexample found (property violation)
            if trimmed.contains("is SAT")
                || trimmed.contains("is sat")
                || trimmed.contains("Output") && trimmed.contains("asserted")
            {
                found_sat = true;
            }

            // Equivalence checking results
            if trimmed.contains("Networks are equivalent") {
                found_equiv = true;
            }
            if trimmed.contains("Networks are NOT equivalent") {
                found_sat = true;
            }

            // Undecided — inconclusive result
            if trimmed.contains("UNDECIDED") || trimmed.contains("undecided") {
                return Err(anyhow!(
                    "ABC verification undecided (resource limit reached)"
                ));
            }

            // Error conditions
            if trimmed.starts_with("Error:")
                || trimmed.starts_with("Cannot")
                || trimmed.contains("abc: command not found")
            {
                found_error = true;
            }
        }

        if found_error && !found_proved && !found_equiv {
            return Err(anyhow!(
                "ABC error: {}",
                output.lines().take(10).collect::<Vec<_>>().join("\n")
            ));
        }

        // SAT (counterexample) overrides any partial "proved" messages
        if found_sat {
            return Ok(false);
        }

        if found_proved || found_equiv {
            return Ok(true);
        }

        Err(anyhow!(
            "ABC inconclusive: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ))
    }

    /// Parse an AIGER/BLIF/Verilog file to extract design structure
    /// into the proof state
    ///
    /// For AIGER (.aig): extracts input/latch/output counts and property info
    /// For BLIF (.blif): extracts model name, inputs, outputs, gate definitions
    /// For Verilog (.v): extracts module declarations and port definitions
    /// For ABC scripts: extracts commands as axioms and property queries as goals
    fn parse_design(&self, content: &str, extension: Option<&str>) -> Result<ProofState> {
        let mut state = ProofState::default();

        match extension {
            Some("blif") => self.parse_blif(content, &mut state)?,
            Some("aig") => self.parse_aiger_ascii(content, &mut state)?,
            _ => self.parse_abc_commands(content, &mut state)?,
        }

        Ok(state)
    }

    /// Parse BLIF (Berkeley Logic Interchange Format) content
    ///
    /// Extracts model name, input/output ports, and gate definitions
    /// from BLIF format into the proof state.
    fn parse_blif(&self, content: &str, state: &mut ProofState) -> Result<()> {
        for line in content.lines() {
            let trimmed = line.trim();

            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            // Model declaration
            if trimmed.starts_with(".model") {
                let name = trimmed.trim_start_matches(".model").trim();
                state.context.axioms.push(format!(".model {}", name));
            }

            // Input declarations
            if trimmed.starts_with(".inputs") {
                let inputs = trimmed.trim_start_matches(".inputs").trim();
                for input_name in inputs.split_whitespace() {
                    state.context.definitions.push(Definition {
                        name: input_name.to_string(),
                        ty: Term::Const("BLIF_INPUT".to_string()),
                        body: Term::Const(input_name.to_string()),
                        type_info: None,
                    });
                }
            }

            // Output declarations — these become verification targets
            if trimmed.starts_with(".outputs") {
                let outputs = trimmed.trim_start_matches(".outputs").trim();
                for output_name in outputs.split_whitespace() {
                    state.goals.push(Goal {
                        id: format!("out_{}", output_name),
                        target: Term::Const(output_name.to_string()),
                        hypotheses: vec![],
                    });
                }
            }

            // Gate definitions (.names)
            if trimmed.starts_with(".names") {
                state.context.axioms.push(trimmed.to_string());
            }

            // Latch definitions
            if trimmed.starts_with(".latch") {
                state.context.axioms.push(trimmed.to_string());
            }
        }

        Ok(())
    }

    /// Parse ASCII AIGER content
    ///
    /// AIGER header format: aag M I L O A [B C J F]
    /// where M=max var, I=inputs, L=latches, O=outputs, A=AND gates
    /// Optional: B=bad state props, C=constraints, J=justice, F=fairness
    fn parse_aiger_ascii(&self, content: &str, state: &mut ProofState) -> Result<()> {
        let mut lines = content.lines();

        // Parse header
        if let Some(header) = lines.next() {
            let parts: Vec<&str> = header.split_whitespace().collect();
            if parts.first() == Some(&"aag") || parts.first() == Some(&"aig") {
                state.context.axioms.push(header.to_string());

                // Extract output count to create goals
                if let Some(output_count_str) = parts.get(4) {
                    if let Ok(output_count) = output_count_str.parse::<usize>() {
                        for i in 0..output_count {
                            state.goals.push(Goal {
                                id: format!("output_{}", i),
                                target: Term::Const(format!("output_{}", i)),
                                hypotheses: vec![],
                            });
                        }
                    }
                }
            }
        }

        // Remaining lines are literal indices
        for line in lines {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                state.context.axioms.push(trimmed.to_string());
            }
        }

        Ok(())
    }

    /// Parse ABC command script content
    ///
    /// Extracts `read` commands and verification commands, treating
    /// verification queries (pdr, bmc, int, dprove, dsec, cec) as goals.
    fn parse_abc_commands(&self, content: &str, state: &mut ProofState) -> Result<()> {
        for line in content.lines() {
            let trimmed = line.trim();

            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            // Verification commands become goals
            let cmd = trimmed.split_whitespace().next().unwrap_or("");
            match cmd {
                "pdr" | "bmc" | "bmc3" | "int" | "dprove" | "dsec" | "cec" => {
                    state.goals.push(Goal {
                        id: format!("verify_{}", state.goals.len()),
                        target: Term::Const(trimmed.to_string()),
                        hypotheses: vec![],
                    });
                },
                _ => {
                    // Everything else is context (read commands, transforms, etc.)
                    state.context.axioms.push(trimmed.to_string());
                },
            }
        }

        Ok(())
    }
}

#[async_trait]
impl ProverBackend for AbcBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::ABC
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("-c")
            .arg("version; quit")
            .output()
            .await
            .context("Failed to run ABC")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);

        // ABC prints version info like "UC Berkeley, ABC 1.01" in banner
        let version = combined
            .lines()
            .find(|l| {
                l.contains("ABC")
                    || l.contains("abc")
                    || l.contains("version")
                    || l.contains("UC Berkeley")
            })
            .unwrap_or("unknown")
            .to_string();

        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path)
            .await
            .context("Failed to read ABC input file")?;

        let extension = path.extension().and_then(|e| e.to_str());
        let mut state = self.parse_design(&content, extension)?;
        state.metadata.insert(
            "abc_source".to_string(),
            serde_json::Value::String(content.clone()),
        );
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        // Without file extension context, try ABC command script first,
        // then fall back to AIGER ASCII if header starts with "aag"/"aig"
        let trimmed = content.trim();
        let mut state = if trimmed.starts_with("aag") || trimmed.starts_with("aig") {
            self.parse_design(content, Some("aig"))?
        } else if trimmed.starts_with(".model") || trimmed.starts_with(".inputs") {
            self.parse_design(content, Some("blif"))?
        } else {
            self.parse_design(content, None)?
        };
        state.metadata.insert(
            "abc_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            // PDR: Property Directed Reachability (IC3 algorithm)
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "abc" && command == "pdr" => {
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("pdr".to_string()),
                );
                if let Some(depth) = args.first() {
                    new_state.metadata.insert(
                        "pdr_depth".to_string(),
                        serde_json::Value::String(depth.clone()),
                    );
                }
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // BMC: Bounded Model Checking
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "abc" && command == "bmc" => {
                let mut new_state = state.clone();
                let bound = args.first().cloned().unwrap_or_else(|| "100".to_string());
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("bmc".to_string()),
                );
                new_state
                    .metadata
                    .insert("bmc_bound".to_string(), serde_json::Value::String(bound));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // INT: Interpolation-based model checking
            Tactic::Custom {
                prover, command, ..
            } if prover == "abc" && command == "int" => {
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("int".to_string()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // DPROVE: Complete multi-engine verification
            Tactic::Custom {
                prover, command, ..
            } if prover == "abc" && command == "dprove" => {
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("dprove".to_string()),
                );
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // DSEC: Sequential equivalence checking
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "abc" && command == "dsec" => {
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("dsec".to_string()),
                );
                // dsec requires a second design file for comparison
                if let Some(ref_design) = args.first() {
                    new_state.metadata.insert(
                        "dsec_reference".to_string(),
                        serde_json::Value::String(ref_design.clone()),
                    );
                }
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // CEC: Combinational equivalence checking
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "abc" && command == "cec" => {
                let mut new_state = state.clone();
                new_state.metadata.insert(
                    "abc_method".to_string(),
                    serde_json::Value::String("cec".to_string()),
                );
                if let Some(ref_design) = args.first() {
                    new_state.metadata.insert(
                        "cec_reference".to_string(),
                        serde_json::Value::String(ref_design.clone()),
                    );
                }
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            // READ: Load a design file into the ABC framework
            Tactic::Custom {
                prover,
                command,
                args,
            } if prover == "abc" && command == "read" => {
                if args.is_empty() {
                    return Ok(TacticResult::Error(
                        "abc read tactic requires a file path argument".to_string(),
                    ));
                }
                let mut new_state = state.clone();
                let file_path = &args[0];
                new_state.context.axioms.push(format!("read {}", file_path));
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            },

            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not supported for ABC logic synthesis/verification system",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Prefer the original source — parsing ABC/BLIF/AIGER into the
        // generic Term IR and reconstructing via `to_abc_script` loses
        // structure for anything beyond a one-command script.
        let method = state
            .metadata
            .get("abc_method")
            .and_then(|v| v.as_str())
            .unwrap_or("pdr");
        let bmc_bound = state
            .metadata
            .get("bmc_bound")
            .and_then(|v| v.as_str())
            .unwrap_or("100");
        let verify_cmd = match method {
            "bmc" | "bmc3" => format!("bmc3 -F {}", bmc_bound),
            "int" => "int".to_string(),
            "dprove" => "dprove".to_string(),
            "dsec" => "dsec".to_string(),
            "cec" => "cec".to_string(),
            _ => "pdr".to_string(),
        };

        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let p = std::path::Path::new(path);
            let read_cmd = match p.extension().and_then(|e| e.to_str()) {
                Some("aig") => format!("read_aiger {}", path),
                Some("blif") => format!("read_blif {}", path),
                Some("v") => format!("read_verilog {}", path),
                _ => format!("read {}", path),
            };
            let script = format!("{}\n{}\nprint_status\nquit\n", read_cmd, verify_cmd);
            let tmp_dir =
                tempfile::tempdir().context("Failed to create temporary directory for ABC")?;
            let tmp_file = tmp_dir.path().join("verify.abc");
            tokio::fs::write(&tmp_file, &script)
                .await
                .context("Failed to write temporary ABC script file")?;
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout),
                Command::new(&self.config.executable)
                    .arg("-f")
                    .arg(&tmp_file)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .map_err(|_| anyhow!("ABC timed out after {} seconds", self.config.timeout))?
            .context("Failed to execute ABC")?;
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            return self.parse_result(&combined);
        }

        if let Some(source) = state.metadata.get("abc_source").and_then(|v| v.as_str()) {
            let trimmed = source.trim();
            let (ext, read_cmd_base) =
                if trimmed.starts_with("aag") || trimmed.starts_with("aig") {
                    (".aig", "read_aiger")
                } else if trimmed.starts_with(".model") || trimmed.starts_with(".inputs") {
                    (".blif", "read_blif")
                } else {
                    // Inline script — just execute it directly.
                    ("", "")
                };
            let tmp_dir =
                tempfile::tempdir().context("Failed to create temporary directory for ABC")?;
            if ext.is_empty() {
                let tmp_file = tmp_dir.path().join("verify.abc");
                let script = format!("{}\n{}\nprint_status\nquit\n", source, verify_cmd);
                tokio::fs::write(&tmp_file, &script)
                    .await
                    .context("Failed to write temporary ABC script file")?;
                let output = tokio::time::timeout(
                    tokio::time::Duration::from_secs(self.config.timeout),
                    Command::new(&self.config.executable)
                        .arg("-f")
                        .arg(&tmp_file)
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .output(),
                )
                .await
                .map_err(|_| anyhow!("ABC timed out after {} seconds", self.config.timeout))?
                .context("Failed to execute ABC")?;
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                let combined = format!("{}\n{}", stdout, stderr);
                return self.parse_result(&combined);
            } else {
                let design_file = tmp_dir.path().join(format!("design{}", ext));
                tokio::fs::write(&design_file, source)
                    .await
                    .context("Failed to write temporary ABC design file")?;
                let script_file = tmp_dir.path().join("verify.abc");
                let script = format!(
                    "{} {}\n{}\nprint_status\nquit\n",
                    read_cmd_base,
                    design_file.display(),
                    verify_cmd
                );
                tokio::fs::write(&script_file, &script)
                    .await
                    .context("Failed to write temporary ABC script file")?;
                let output = tokio::time::timeout(
                    tokio::time::Duration::from_secs(self.config.timeout),
                    Command::new(&self.config.executable)
                        .arg("-f")
                        .arg(&script_file)
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .output(),
                )
                .await
                .map_err(|_| anyhow!("ABC timed out after {} seconds", self.config.timeout))?
                .context("Failed to execute ABC")?;
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                let combined = format!("{}\n{}", stdout, stderr);
                return self.parse_result(&combined);
            }
        }

        // Fallback: reconstruct an ABC script from the parsed IR.
        let abc_script = self.to_abc_script(state)?;

        // ABC can execute commands via -c flag or from a script file.
        // For multi-line scripts, write to a temp file and use -f.
        let tmp_dir =
            tempfile::tempdir().context("Failed to create temporary directory for ABC")?;
        let tmp_file = tmp_dir.path().join("verify.abc");
        tokio::fs::write(&tmp_file, &abc_script)
            .await
            .context("Failed to write temporary ABC script file")?;

        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout),
            Command::new(&self.config.executable)
                .arg("-f")
                .arg(&tmp_file)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .map_err(|_| anyhow!("ABC timed out after {} seconds", self.config.timeout))?
        .context("Failed to execute ABC")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let combined = format!("{}\n{}", stdout, stderr);
        self.parse_result(&combined)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_abc_script(state)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            // PDR (IC3) — most commonly used complete verification engine
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "pdr".to_string(),
                args: vec![],
            },
            // BMC — fast bug-finding with bounded depth
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "bmc".to_string(),
                args: vec!["200".to_string()],
            },
            // Interpolation — complete verification via Craig interpolation
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "int".to_string(),
                args: vec![],
            },
            // dprove — runs multiple engines in parallel for best coverage
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "dprove".to_string(),
                args: vec![],
            },
            // CEC — combinational equivalence checking
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "cec".to_string(),
                args: vec![],
            },
            // DSEC — sequential equivalence checking
            Tactic::Custom {
                prover: "abc".to_string(),
                command: "dsec".to_string(),
                args: vec![],
            },
        ];

        tactics.truncate(limit);
        Ok(tactics)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // ABC does not have a theorem library; it verifies hardware properties
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

    /// Helper to create a test ABC backend with default config
    fn test_backend() -> AbcBackend {
        let config = ProverConfig {
            executable: PathBuf::from("abc"),
            timeout: 60,
            ..Default::default()
        };
        AbcBackend::new(config)
    }

    #[tokio::test]
    async fn test_abc_script_export_with_pdr() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state
            .context
            .axioms
            .push("read_aiger design.aig".to_string());
        state.goals.push(Goal {
            id: "output_0".to_string(),
            target: Term::Const("safety_property".to_string()),
            hypotheses: vec![],
        });

        let script = backend.to_abc_script(&state).unwrap();

        assert!(script.contains("ECHIDNA ABC Export"));
        assert!(script.contains("read_aiger design.aig"));
        assert!(script.contains("pdr"));
        assert!(script.contains("print_status"));
        assert!(script.contains("quit"));
    }

    #[tokio::test]
    async fn test_abc_script_export_bmc_method() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state
            .context
            .axioms
            .push("read_aiger design.aig".to_string());
        state.metadata.insert(
            "abc_method".to_string(),
            serde_json::Value::String("bmc".to_string()),
        );
        state.metadata.insert(
            "bmc_bound".to_string(),
            serde_json::Value::String("50".to_string()),
        );
        state.goals.push(Goal {
            id: "output_0".to_string(),
            target: Term::Const("property_0".to_string()),
            hypotheses: vec![],
        });

        let script = backend.to_abc_script(&state).unwrap();

        assert!(script.contains("bmc3 -F 50"));
    }

    #[test]
    fn test_abc_parse_result_proved() {
        let backend = test_backend();

        let output = "ABC command line execution.\nProperty proved.\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_abc_parse_result_sat_counterexample() {
        let backend = test_backend();

        let output = "Output 0 is SAT at frame 15\nCounterexample trace:\n  ...\n";
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_abc_parse_result_equivalent() {
        let backend = test_backend();

        let output = "Networks are equivalent.\n";
        assert!(backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_abc_parse_result_not_equivalent() {
        let backend = test_backend();

        let output = "Networks are NOT equivalent.\n";
        assert!(!backend.parse_result(output).unwrap());
    }

    #[test]
    fn test_abc_parse_result_undecided() {
        let backend = test_backend();

        let output = "UNDECIDED after 1000 frames\n";
        assert!(backend.parse_result(output).is_err());
    }

    #[tokio::test]
    async fn test_abc_parse_blif() {
        let backend = test_backend();

        let blif = r#"
.model counter
.inputs clk reset
.outputs count_0 count_1
.names reset count_0_next count_0
01 1
.latch count_0_next count_0 re clk 0
.end
"#;

        let state = backend.parse_string(blif).await.unwrap();

        // Should have parsed inputs as definitions
        assert!(
            state.context.definitions.iter().any(|d| d.name == "clk"),
            "Should have parsed clk input"
        );
        assert!(
            state.context.definitions.iter().any(|d| d.name == "reset"),
            "Should have parsed reset input"
        );

        // Outputs become goals (verification targets)
        assert_eq!(state.goals.len(), 2, "Should have 2 output goals");
    }

    #[tokio::test]
    async fn test_abc_parse_aiger_ascii() {
        let backend = test_backend();

        let aiger = "aag 5 2 1 1 2\n2\n4\n6 8\n10\n8 2 4\n10 3 5\n";

        let state = backend.parse_string(aiger).await.unwrap();

        assert!(
            !state.context.axioms.is_empty(),
            "Should have parsed AIGER header and gates"
        );
        assert_eq!(
            state.goals.len(),
            1,
            "Should have 1 output goal from header"
        );
    }

    #[tokio::test]
    async fn test_abc_parse_commands() {
        let backend = test_backend();

        let commands = r#"
# Verify safety property
read_aiger design.aig
strash
pdr
"#;

        let state = backend.parse_string(commands).await.unwrap();

        assert!(
            state
                .context
                .axioms
                .iter()
                .any(|a| a.contains("read_aiger")),
            "Should have parsed read command as axiom"
        );
        assert!(
            state
                .goals
                .iter()
                .any(|g| g.target.to_string().contains("pdr")),
            "Should have parsed pdr as a verification goal"
        );
    }

    #[tokio::test]
    async fn test_abc_apply_tactic_pdr() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "abc".to_string(),
            command: "pdr".to_string(),
            args: vec![],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();

        match result {
            TacticResult::Success(new_state) => {
                assert_eq!(
                    new_state
                        .metadata
                        .get("abc_method")
                        .and_then(|v| v.as_str()),
                    Some("pdr")
                );
            },
            other => panic!("Expected Success, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_abc_apply_tactic_bmc_with_bound() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "abc".to_string(),
            command: "bmc".to_string(),
            args: vec!["500".to_string()],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();

        match result {
            TacticResult::Success(new_state) => {
                assert_eq!(
                    new_state
                        .metadata
                        .get("abc_method")
                        .and_then(|v| v.as_str()),
                    Some("bmc")
                );
                assert_eq!(
                    new_state.metadata.get("bmc_bound").and_then(|v| v.as_str()),
                    Some("500")
                );
            },
            other => panic!("Expected Success, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_abc_suggest_tactics() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactics = backend.suggest_tactics(&state, 3).await.unwrap();
        assert_eq!(tactics.len(), 3);

        // First suggestion should be PDR (most commonly used)
        match &tactics[0] {
            Tactic::Custom {
                prover, command, ..
            } => {
                assert_eq!(prover, "abc");
                assert_eq!(command, "pdr");
            },
            other => panic!("Expected Custom tactic, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_abc_apply_unsupported_tactic() {
        let backend = test_backend();
        let state = ProofState::default();

        let tactic = Tactic::Custom {
            prover: "coq".to_string(),
            command: "intros".to_string(),
            args: vec![],
        };

        let result = backend.apply_tactic(&state, &tactic).await.unwrap();

        match result {
            TacticResult::Error(_) => {}, // Expected
            other => panic!("Expected Error for unsupported tactic, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_abc_file_path_detection() {
        let backend = test_backend();

        let mut state = ProofState::default();
        state.context.axioms.push("design.aig".to_string());
        state.goals.push(Goal {
            id: "output_0".to_string(),
            target: Term::Const("prop".to_string()),
            hypotheses: vec![],
        });

        let script = backend.to_abc_script(&state).unwrap();

        assert!(
            script.contains("read_aiger design.aig"),
            "Should auto-detect .aig extension and use read_aiger"
        );
    }
}
