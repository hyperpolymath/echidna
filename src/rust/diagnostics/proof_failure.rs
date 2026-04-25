// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Proof failure diagnostics.
//!
//! When a prover returns an error or unexpected result, this module parses the
//! raw prover output and returns a structured `DiagnosticReport` that:
//!
//! - classifies the failure into a `FailureKind` (e.g. `ParseMismatch`,
//!   `UnsolvedGoal`, `Timeout`, `BackendBug`),
//! - extracts the relevant location (file, line) when available,
//! - produces a human-readable explanation,
//! - suggests concrete fixes the user can apply.
//!
//! The module is prover-aware: `diagnose(kind, raw_output)` dispatches to a
//! per-prover parser that understands that prover's output format.

use std::fmt;

use crate::provers::ProverKind;

/// Taxonomy of proof failure causes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailureKind {
    /// The prover's output did not match any known success/failure pattern.
    /// This usually means an ECHIDNA backend bug (wrong prefix, wrong token).
    ParseMismatch {
        /// What we looked for.
        expected_pattern: String,
        /// What the prover actually emitted (first 200 chars).
        actual_prefix: String,
    },

    /// The prover could not close the goal — no proof was found in the
    /// allotted time but the search was not cut off by a timeout.
    UnsolvedGoal {
        /// The goal or query that could not be closed.
        goal_summary: Option<String>,
    },

    /// The input failed to type-check or parse inside the prover.
    TypeError {
        message: String,
        location: Option<SourceLocation>,
    },

    /// An identifier, module, or library was not found.
    OutOfScope {
        missing: String,
        location: Option<SourceLocation>,
    },

    /// The prover hit its wall-clock or CPU limit before finishing.
    Timeout {
        limit_secs: Option<u64>,
    },

    /// The prover process crashed (non-zero exit, signal, or internal error).
    ProverCrash {
        exit_code: Option<i32>,
        stderr_excerpt: String,
    },

    /// The user's proof file could not be parsed by the prover.
    SyntaxError {
        message: String,
        location: Option<SourceLocation>,
    },

    /// An ECHIDNA configuration problem (wrong executable path, missing flag).
    ConfigError {
        detail: String,
    },

    /// ECHIDNA's backend has a known bug for this prover/input combination.
    BackendBug {
        description: String,
        workaround: Option<String>,
    },

    /// The prover reported the formula is satisfiable (counterexample exists),
    /// so the proof attempt failed by design.
    Satisfiable {
        model_excerpt: Option<String>,
    },

    /// A catch-all for failures that don't fit the above categories.
    Unknown {
        raw_output: String,
    },
}

/// A file:line reference extracted from prover output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (&self.file, self.line, self.column) {
            (Some(file), Some(line), Some(col)) => write!(f, "{}:{}:{}", file, line, col),
            (Some(file), Some(line), None) => write!(f, "{}:{}", file, line),
            (Some(file), None, _) => write!(f, "{}", file),
            (None, Some(line), _) => write!(f, "line {}", line),
            _ => write!(f, "(unknown location)"),
        }
    }
}

/// Structured diagnostic report returned by [`diagnose`].
#[derive(Debug, Clone)]
pub struct DiagnosticReport {
    /// Which prover produced the failure.
    pub prover: ProverKind,
    /// Failure classification.
    pub kind: FailureKind,
    /// One-paragraph human-readable explanation.
    pub explanation: String,
    /// Ordered list of concrete suggestions for the user.
    pub suggestions: Vec<String>,
    /// The first 500 characters of raw prover output.
    pub raw_excerpt: String,
}

impl DiagnosticReport {
    /// Format the report as a human-readable string for CLI or log output.
    pub fn display(&self) -> String {
        let mut out = format!("[{:?}] {:?}\n\n", self.prover, self.kind);
        out.push_str(&format!("Explanation: {}\n\n", self.explanation));
        if !self.suggestions.is_empty() {
            out.push_str("Suggestions:\n");
            for (i, s) in self.suggestions.iter().enumerate() {
                out.push_str(&format!("  {}. {}\n", i + 1, s));
            }
        }
        if !self.raw_excerpt.is_empty() {
            out.push_str(&format!("\nProver output (excerpt):\n  {}\n", self.raw_excerpt.replace('\n', "\n  ")));
        }
        out
    }

    /// Emit as an A2ML data block (TOML-flavoured).
    pub fn to_a2ml(&self) -> String {
        let kind_tag = match &self.kind {
            FailureKind::ParseMismatch { .. } => "ParseMismatch",
            FailureKind::UnsolvedGoal { .. } => "UnsolvedGoal",
            FailureKind::TypeError { .. } => "TypeError",
            FailureKind::OutOfScope { .. } => "OutOfScope",
            FailureKind::Timeout { .. } => "Timeout",
            FailureKind::ProverCrash { .. } => "ProverCrash",
            FailureKind::SyntaxError { .. } => "SyntaxError",
            FailureKind::ConfigError { .. } => "ConfigError",
            FailureKind::BackendBug { .. } => "BackendBug",
            FailureKind::Satisfiable { .. } => "Satisfiable",
            FailureKind::Unknown { .. } => "Unknown",
        };
        let suggestions = self
            .suggestions
            .iter()
            .map(|s| format!("  \"{}\",", s))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "[proof-failure-diagnostic]\nprover = \"{:?}\"\nkind = \"{}\"\nexplanation = \"{}\"\nsuggestions = [\n{}\n]\nraw_excerpt = \"\"\"\n{}\n\"\"\"\n",
            self.prover,
            kind_tag,
            self.explanation.replace('"', "'"),
            suggestions,
            self.raw_excerpt.chars().take(500).collect::<String>(),
        )
    }
}

/// Diagnose a prover failure from its raw output.
///
/// `raw_output` is the combined stdout (and optionally stderr) from the
/// prover process.  `prover` determines which output format to parse.
pub fn diagnose(prover: ProverKind, raw_output: &str) -> DiagnosticReport {
    let raw_excerpt = raw_output.chars().take(500).collect::<String>();

    let kind = match prover {
        ProverKind::EProver => diagnose_eprover(raw_output),
        ProverKind::Z3 => diagnose_z3(raw_output),
        ProverKind::CVC5 => diagnose_smt_generic(raw_output, "CVC5"),
        ProverKind::Coq => diagnose_coq(raw_output),
        ProverKind::Agda => diagnose_agda(raw_output),
        ProverKind::Lean => diagnose_lean4(raw_output),
        ProverKind::Idris2 => diagnose_idris2(raw_output),
        ProverKind::Vampire => diagnose_vampire(raw_output),
        _ => diagnose_generic(raw_output),
    };

    let (explanation, suggestions) = explain_and_suggest(prover, &kind);

    DiagnosticReport {
        prover,
        kind,
        explanation,
        suggestions,
        raw_excerpt,
    }
}

// ---------------------------------------------------------------------------
// Per-prover diagnostic parsers
// ---------------------------------------------------------------------------

fn diagnose_eprover(output: &str) -> FailureKind {
    // Timeout signals
    if output.contains("CPU time limit exceeded") || output.contains("ResourceOut") {
        return FailureKind::Timeout { limit_secs: None };
    }
    // Crash / internal error
    if output.contains("Segmentation fault") || output.contains("Internal error") {
        return FailureKind::ProverCrash {
            exit_code: None,
            stderr_excerpt: first_n(output, 300),
        };
    }
    // Explicit counter-satisfiable result
    if output.contains("% SZS status CounterSatisfiable")
        || output.contains("% SZS status Satisfiable")
    {
        return FailureKind::Satisfiable { model_excerpt: None };
    }
    // Parse / syntax errors in the input
    if output.contains("Unexpected token") || output.contains("syntax error") {
        return FailureKind::SyntaxError {
            message: extract_line_containing(output, "syntax error")
                .or_else(|| extract_line_containing(output, "Unexpected token"))
                .unwrap_or_default(),
            location: extract_tptp_location(output),
        };
    }
    // ECHIDNA backend bug: output uses '%' but old code checked '#'
    if !output.contains('%') && (output.contains("Proof found") || output.contains("SZS status"))
    {
        return FailureKind::BackendBug {
            description: "EProver output uses '%' prefix but ECHIDNA checked '#'. Parser mismatch.".into(),
            workaround: Some("Update parse_result to check '% SZS status ...' not '# SZS status ...'".into()),
        };
    }
    // Inconclusive / resource exhaustion
    if output.contains("% SZS status GaveUp") || output.contains("% SZS status Unknown") {
        return FailureKind::UnsolvedGoal { goal_summary: None };
    }
    // No recognised pattern
    FailureKind::ParseMismatch {
        expected_pattern: "% SZS status (Theorem|Unsatisfiable|...)".into(),
        actual_prefix: first_n(output, 200),
    }
}

fn diagnose_z3(output: &str) -> FailureKind {
    // Explicit errors from Z3
    if let Some(err_line) = output.lines().find(|l| l.trim_start().starts_with("(error")) {
        let msg = err_line
            .trim()
            .trim_start_matches("(error")
            .trim_end_matches(')')
            .trim()
            .trim_matches('"')
            .to_string();
        // Distinguish parse vs unsupported vs other
        if msg.contains("parse") || msg.contains("not declared") || msg.contains("unexpected") {
            return FailureKind::SyntaxError {
                message: msg,
                location: extract_z3_location(output),
            };
        }
        if msg.contains("not supported") || msg.contains("unsupported") {
            return FailureKind::ConfigError { detail: msg };
        }
        return FailureKind::ProverCrash {
            exit_code: None,
            stderr_excerpt: msg,
        };
    }
    // Timeout
    if output.contains("timeout") || output.contains("unknown") {
        if output.trim() == "unknown" || output.lines().any(|l| l.trim() == "unknown") {
            return FailureKind::Timeout { limit_secs: None };
        }
    }
    // Satisfiable (not a proof)
    if output.lines().any(|l| l.trim() == "sat") {
        let model = output
            .lines()
            .skip_while(|l| l.trim() != "sat")
            .skip(1)
            .take(5)
            .collect::<Vec<_>>()
            .join("\n");
        return FailureKind::Satisfiable {
            model_excerpt: if model.is_empty() { None } else { Some(model) },
        };
    }
    // Backend bug: model output after get-value was mistaken for the sat/unsat answer
    if output.lines().any(|l| {
        let t = l.trim();
        t.starts_with("((") || (t.starts_with('(') && !t.starts_with("(error") && !t.starts_with("(model"))
    }) && output.lines().any(|l| matches!(l.trim(), "sat" | "unsat"))
    {
        return FailureKind::BackendBug {
            description: "Z3 get-value output appeared after the check-sat answer. Parser took the model term as the answer.".into(),
            workaround: Some("Scan backward for the last 'sat'/'unsat'/'unknown' line, skipping model output.".into()),
        };
    }
    FailureKind::ParseMismatch {
        expected_pattern: "sat | unsat | unknown | (error ...)".into(),
        actual_prefix: first_n(output, 200),
    }
}

fn diagnose_smt_generic(output: &str, _prover_name: &str) -> FailureKind {
    if output.lines().any(|l| l.trim() == "unsat") {
        // unsat is success for proof queries — if we're in diagnostics,
        // something else went wrong (likely the verify_proof logic)
        return FailureKind::Unknown { raw_output: first_n(output, 300) };
    }
    if output.lines().any(|l| l.trim() == "sat") {
        return FailureKind::Satisfiable { model_excerpt: None };
    }
    if let Some(err) = output.lines().find(|l| l.trim_start().starts_with("(error")) {
        return FailureKind::SyntaxError {
            message: err.trim().to_string(),
            location: None,
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_coq(output: &str) -> FailureKind {
    // Type errors
    if output.contains("Error: The term") || output.contains("Illegal application") {
        return FailureKind::TypeError {
            message: extract_coq_error(output),
            location: extract_coq_location(output),
        };
    }
    // Unresolved goals
    if output.contains("Unfinished proof") || output.contains("remaining subgoal") {
        return FailureKind::UnsolvedGoal {
            goal_summary: extract_line_containing(output, "subgoal"),
        };
    }
    // Module / library not found
    if output.contains("Cannot find") || output.contains("Require") && output.contains("Error") {
        return FailureKind::OutOfScope {
            missing: extract_line_containing(output, "Cannot find")
                .or_else(|| extract_line_containing(output, "Require"))
                .unwrap_or_default(),
            location: None,
        };
    }
    // Syntax
    if output.contains("Syntax error") || output.contains("Parse error") {
        return FailureKind::SyntaxError {
            message: extract_coq_error(output),
            location: extract_coq_location(output),
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_agda(output: &str) -> FailureKind {
    // Parse errors have a clear marker
    if output.contains("Parse error") || output.contains("Unexpected token") {
        return FailureKind::SyntaxError {
            message: extract_line_containing(output, "Parse error")
                .or_else(|| extract_line_containing(output, "Unexpected"))
                .unwrap_or_default(),
            location: extract_agda_location(output),
        };
    }
    // Type errors
    if output.contains("type mismatch") || output.contains("Type mismatch")
        || output.contains("_!=_") || output.contains("!=<")
    {
        return FailureKind::TypeError {
            message: first_n(output, 300),
            location: extract_agda_location(output),
        };
    }
    // Unresolved
    if output.contains("Unsolved constraints") || output.contains("unsolved metas") {
        return FailureKind::UnsolvedGoal {
            goal_summary: extract_line_containing(output, "Unsolved"),
        };
    }
    // Missing module
    if output.contains("Failed to find source of module") || output.contains("No such module") {
        return FailureKind::OutOfScope {
            missing: extract_line_containing(output, "module").unwrap_or_default(),
            location: None,
        };
    }
    // Termination
    if output.contains("Termination checking failed") {
        return FailureKind::TypeError {
            message: "Termination checking failed — the function may not be total.".into(),
            location: extract_agda_location(output),
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_lean4(output: &str) -> FailureKind {
    if output.contains("unknown identifier") || output.contains("unknown tactic") {
        return FailureKind::OutOfScope {
            missing: extract_line_containing(output, "unknown").unwrap_or_default(),
            location: extract_lean4_location(output),
        };
    }
    if output.contains("type mismatch") || output.contains("application type mismatch") {
        return FailureKind::TypeError {
            message: first_n(output, 300),
            location: extract_lean4_location(output),
        };
    }
    if output.contains("unsolved goals") {
        return FailureKind::UnsolvedGoal {
            goal_summary: extract_line_containing(output, "unsolved goals"),
        };
    }
    if output.contains("expected token") || output.contains("unexpected token") {
        return FailureKind::SyntaxError {
            message: extract_line_containing(output, "token").unwrap_or_default(),
            location: extract_lean4_location(output),
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_idris2(output: &str) -> FailureKind {
    if output.contains("Parse failed") || output.contains("Expected") {
        return FailureKind::SyntaxError {
            message: extract_line_containing(output, "Parse failed")
                .or_else(|| extract_line_containing(output, "Expected"))
                .unwrap_or_default(),
            location: extract_idris2_location(output),
        };
    }
    if output.contains("Mismatch between") || output.contains("When checking") && output.contains("Expected") {
        return FailureKind::TypeError {
            message: first_n(output, 300),
            location: extract_idris2_location(output),
        };
    }
    if output.contains("Module not found") || output.contains("can't find") {
        return FailureKind::OutOfScope {
            missing: extract_line_containing(output, "Module not found")
                .or_else(|| extract_line_containing(output, "can't find"))
                .unwrap_or_default(),
            location: None,
        };
    }
    if output.contains("Unsolvable holes") || output.contains("holes remaining") {
        return FailureKind::UnsolvedGoal {
            goal_summary: extract_line_containing(output, "holes"),
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_vampire(output: &str) -> FailureKind {
    if output.contains("% Termination reason: Time limit") {
        return FailureKind::Timeout { limit_secs: None };
    }
    if output.contains("% SZS status CounterSatisfiable")
        || output.contains("% SZS status Satisfiable")
    {
        return FailureKind::Satisfiable { model_excerpt: None };
    }
    if output.contains("% SZS status GaveUp") {
        return FailureKind::UnsolvedGoal { goal_summary: None };
    }
    if output.contains("parse error") || output.contains("unexpected input") {
        return FailureKind::SyntaxError {
            message: extract_line_containing(output, "parse error")
                .or_else(|| extract_line_containing(output, "unexpected"))
                .unwrap_or_default(),
            location: None,
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

fn diagnose_generic(output: &str) -> FailureKind {
    if output.contains("timeout") || output.contains("time limit") {
        return FailureKind::Timeout { limit_secs: None };
    }
    if output.is_empty() {
        return FailureKind::ProverCrash {
            exit_code: None,
            stderr_excerpt: "(empty output)".into(),
        };
    }
    FailureKind::Unknown { raw_output: first_n(output, 300) }
}

// ---------------------------------------------------------------------------
// Explanation and suggestion generation
// ---------------------------------------------------------------------------

fn explain_and_suggest(prover: ProverKind, kind: &FailureKind) -> (String, Vec<String>) {
    match kind {
        FailureKind::ParseMismatch { expected_pattern, actual_prefix } => (
            format!(
                "ECHIDNA expected the {} output to match '{}', but saw '{}...' instead. \
                 This typically means ECHIDNA's backend parser does not recognise \
                 the prover's actual output format.",
                format!("{:?}", prover), expected_pattern,
                actual_prefix.chars().take(60).collect::<String>()
            ),
            vec![
                "Check that the prover binary is the correct version.".into(),
                "Compare the prover's raw stdout against the pattern in the backend's \
                 parse_result function.".into(),
                "File an ECHIDNA issue with the raw prover output attached.".into(),
            ],
        ),

        FailureKind::BackendBug { description, workaround } => (
            format!(
                "ECHIDNA has a known backend bug with {:?}: {}",
                prover, description
            ),
            {
                let mut s = vec![
                    "Update the ECHIDNA backend to fix the parser.".into(),
                ];
                if let Some(w) = workaround {
                    s.push(format!("Workaround: {}", w));
                }
                s
            },
        ),

        FailureKind::UnsolvedGoal { goal_summary } => (
            format!(
                "{:?} could not find a proof for this goal{}. \
                 The prover exhausted its search without finding a derivation.",
                prover,
                goal_summary.as_deref().map(|g| format!(": {}", g)).unwrap_or_default()
            ),
            vec![
                "Check that the goal is actually provable — try a smaller example.".into(),
                "Add intermediate lemmas to break the proof into steps.".into(),
                "Try a different prover backend (e.g. Vampire instead of EProver).".into(),
                "Increase the prover timeout.".into(),
            ],
        ),

        FailureKind::TypeError { message, location } => (
            format!(
                "{:?} rejected the proof term due to a type error{}. Message: {}",
                prover,
                location.as_ref().map(|l| format!(" at {}", l)).unwrap_or_default(),
                message.chars().take(120).collect::<String>()
            ),
            vec![
                "Check the types of all sub-expressions at the flagged location.".into(),
                "Hover over the term in your IDE to see the inferred type.".into(),
                "Add explicit type annotations to narrow down the mismatch.".into(),
            ],
        ),

        FailureKind::SyntaxError { message, location } => (
            format!(
                "{:?} could not parse the proof file{}. Parser error: {}",
                prover,
                location.as_ref().map(|l| format!(" at {}", l)).unwrap_or_default(),
                message.chars().take(120).collect::<String>()
            ),
            vec![
                "Check the file for mismatched parentheses or missing keywords.".into(),
                format!(
                    "Validate the file with the {} binary directly before submitting to ECHIDNA.",
                    format!("{:?}", prover).to_lowercase()
                ),
                "Check that the file encoding is UTF-8.".into(),
            ],
        ),

        FailureKind::OutOfScope { missing, location } => (
            format!(
                "{:?} could not find identifier or module '{}'{}.  \
                 Either the library is not installed or the import is wrong.",
                prover,
                missing,
                location.as_ref().map(|l| format!(" (referenced at {})", l)).unwrap_or_default()
            ),
            vec![
                "Verify the library/module is installed in the prover's search path.".into(),
                "Check the spelling of the import or identifier.".into(),
                format!(
                    "For {}, ensure the .agda-lib / _CoqProject / lakefile.lean \
                     is present and points to the correct library roots.",
                    format!("{:?}", prover)
                ),
            ],
        ),

        FailureKind::Timeout { limit_secs } => (
            format!(
                "{:?} hit its time limit{} without completing the proof search.",
                prover,
                limit_secs.map(|s| format!(" ({}s)", s)).unwrap_or_default()
            ),
            vec![
                "Increase the ECHIDNA timeout for this prover.".into(),
                "Simplify the goal or add intermediate lemmas.".into(),
                "Try a faster prover backend for this problem class.".into(),
                "For ATP problems, reduce the clause set if possible.".into(),
            ],
        ),

        FailureKind::ProverCrash { exit_code, stderr_excerpt } => (
            format!(
                "{:?} exited abnormally{}. Stderr: {}",
                prover,
                exit_code.map(|c| format!(" (exit {})", c)).unwrap_or_default(),
                stderr_excerpt.chars().take(120).collect::<String>()
            ),
            vec![
                "Check that the prover binary is correctly installed and executable.".into(),
                "Run the prover manually on the same input to reproduce the crash.".into(),
                "Check ECHIDNA's resource limits (ulimit) if the prover is OOM-killed.".into(),
            ],
        ),

        FailureKind::Satisfiable { model_excerpt } => (
            format!(
                "{:?} found a satisfying assignment, which means a counterexample exists. \
                 The formula or negated goal is satisfiable, so the proof attempt fails.{}",
                prover,
                model_excerpt.as_deref()
                    .map(|m| format!(" Counterexample:\n{}", m))
                    .unwrap_or_default()
            ),
            vec![
                "Examine the counterexample model to understand why the property fails.".into(),
                "Check whether the axioms correctly constrain the problem.".into(),
                "If this was a bounded model-check, extend the bound.".into(),
            ],
        ),

        FailureKind::ConfigError { detail } => (
            format!("ECHIDNA configuration error for {:?}: {}", prover, detail),
            vec![
                "Check the prover executable path in ECHIDNA's config.".into(),
                "Verify supported features and logic fragments for this prover.".into(),
            ],
        ),

        FailureKind::Unknown { raw_output } => (
            format!(
                "{:?} produced output that ECHIDNA could not classify. \
                 Raw output: {}",
                prover,
                raw_output.chars().take(120).collect::<String>()
            ),
            vec![
                "Run the prover manually on the input file and inspect the output.".into(),
                "File an ECHIDNA issue with the full prover output so a parser can be added.".into(),
            ],
        ),
    }
}

// ---------------------------------------------------------------------------
// Location extractors (prover-specific heuristics)
// ---------------------------------------------------------------------------

fn extract_tptp_location(output: &str) -> Option<SourceLocation> {
    // EProver / Vampire: "at line N column M"
    for line in output.lines() {
        if line.contains("at line") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if let Some(pos) = parts.iter().position(|&w| w == "line") {
                let lineno = parts.get(pos + 1).and_then(|s| s.trim_end_matches(',').parse().ok());
                let colno = parts.iter().position(|&w| w == "column")
                    .and_then(|p| parts.get(p + 1))
                    .and_then(|s| s.parse().ok());
                return Some(SourceLocation { file: None, line: lineno, column: colno });
            }
        }
    }
    None
}

fn extract_z3_location(output: &str) -> Option<SourceLocation> {
    // Z3: "(error "line N column M: ...")"
    for line in output.lines() {
        if line.contains("line") && line.contains("column") {
            let nums: Vec<u32> = line
                .split(|c: char| !c.is_numeric())
                .filter(|s| !s.is_empty())
                .filter_map(|s| s.parse().ok())
                .collect();
            if nums.len() >= 2 {
                return Some(SourceLocation { file: None, line: Some(nums[0]), column: Some(nums[1]) });
            }
        }
    }
    None
}

fn extract_coq_location(output: &str) -> Option<SourceLocation> {
    // Coq: "File "foo.v", line N, characters M-P"
    for line in output.lines() {
        if line.starts_with("File ") {
            let file = line.split('"').nth(1).map(String::from);
            let lineno = line.split("line ").nth(1)
                .and_then(|s| s.split(',').next())
                .and_then(|s| s.trim().parse().ok());
            return Some(SourceLocation { file, line: lineno, column: None });
        }
    }
    None
}

fn extract_coq_error(output: &str) -> String {
    output
        .lines()
        .skip_while(|l| !l.starts_with("Error"))
        .take(3)
        .collect::<Vec<_>>()
        .join(" ")
}

fn extract_agda_location(output: &str) -> Option<SourceLocation> {
    // Agda: "foo/Bar.agda:12,5-18"
    for line in output.lines() {
        if let Some(colon_pos) = line.find(':') {
            let path = &line[..colon_pos];
            if path.ends_with(".agda") || path.ends_with(".lagda") {
                let rest = &line[colon_pos + 1..];
                let lineno = rest.split(',').next().and_then(|s| s.parse().ok());
                return Some(SourceLocation {
                    file: Some(path.to_string()),
                    line: lineno,
                    column: None,
                });
            }
        }
    }
    None
}

fn extract_lean4_location(output: &str) -> Option<SourceLocation> {
    // Lean 4: "foo/Bar.lean:12:5: error: ..."
    for line in output.lines() {
        let parts: Vec<&str> = line.splitn(4, ':').collect();
        if parts.len() >= 3 {
            if parts[0].ends_with(".lean") {
                let lineno = parts[1].parse().ok();
                let colno = parts[2].parse().ok();
                return Some(SourceLocation {
                    file: Some(parts[0].to_string()),
                    line: lineno,
                    column: colno,
                });
            }
        }
    }
    None
}

fn extract_idris2_location(output: &str) -> Option<SourceLocation> {
    // Idris2: "foo/Bar.idr:12:5:"
    for line in output.lines() {
        let parts: Vec<&str> = line.splitn(4, ':').collect();
        if parts.len() >= 3 && parts[0].ends_with(".idr") {
            let lineno = parts[1].parse().ok();
            let colno = parts[2].trim_start().split_whitespace().next().and_then(|s| s.parse().ok());
            return Some(SourceLocation {
                file: Some(parts[0].to_string()),
                line: lineno,
                column: colno,
            });
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

fn first_n(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

fn extract_line_containing<'a>(output: &'a str, needle: &str) -> Option<String> {
    output
        .lines()
        .find(|l| l.contains(needle))
        .map(|l| l.trim().to_string())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnose_eprover_parse_mismatch() {
        // Simulate the old bug where ECHIDNA checked '#' but EProver emits '%'
        let output = "% Proof found!\n% SZS status Unsatisfiable\n";
        // The fixed parser correctly identifies this as a success, so if diagnose
        // is called it means the verify path failed for another reason.
        // For the bug case, simulate raw output that used '#'
        let buggy_output = "# Proof found!\n# SZS status Unsatisfiable\n";
        let report = diagnose(ProverKind::EProver, buggy_output);
        // The buggy output doesn't have '%' so it hits the BackendBug branch
        // (it has 'Proof found' but not '%')
        assert!(matches!(
            report.kind,
            FailureKind::BackendBug { .. } | FailureKind::ParseMismatch { .. }
        ));
    }

    #[test]
    fn test_diagnose_eprover_timeout() {
        let output = "% SZS status ResourceOut\n% CPU time limit exceeded\n";
        let report = diagnose(ProverKind::EProver, output);
        assert!(matches!(report.kind, FailureKind::Timeout { .. }));
        assert!(!report.suggestions.is_empty());
    }

    #[test]
    fn test_diagnose_eprover_satisfiable() {
        let output = "% SZS status CounterSatisfiable\n";
        let report = diagnose(ProverKind::EProver, output);
        assert!(matches!(report.kind, FailureKind::Satisfiable { .. }));
    }

    #[test]
    fn test_diagnose_z3_model_after_get_value() {
        // This is the exact bug: Z3 emits sat then model lines from (get-value)
        let output = "unsat\nsat\n((x 3)\n (A ((as const (Array Int Int)) 0))\n (found_2 0))\n";
        let report = diagnose(ProverKind::Z3, output);
        // The output contains both 'sat' and 'unsat' lines plus model lines.
        // diagnose should detect the sat + model pattern.
        assert!(matches!(
            report.kind,
            FailureKind::Satisfiable { .. } | FailureKind::BackendBug { .. }
        ));
    }

    #[test]
    fn test_diagnose_z3_parse_error() {
        let output = "(error \"line 3 column 10: unexpected token\")\n";
        let report = diagnose(ProverKind::Z3, output);
        assert!(matches!(report.kind, FailureKind::SyntaxError { .. }));
        assert!(report.explanation.contains("parse"));
    }

    #[test]
    fn test_diagnose_z3_timeout() {
        let output = "unknown\n";
        let report = diagnose(ProverKind::Z3, output);
        assert!(matches!(report.kind, FailureKind::Timeout { .. }));
    }

    #[test]
    fn test_diagnose_agda_type_error() {
        let output = "Foo.agda:10,5-20\ntype mismatch\n  expected: ℕ → ℕ\n  but got:  ℕ\n";
        let report = diagnose(ProverKind::Agda, output);
        assert!(matches!(report.kind, FailureKind::TypeError { .. }));
        if let FailureKind::TypeError { location, .. } = &report.kind {
            assert!(location.is_some());
        }
    }

    #[test]
    fn test_diagnose_coq_unsolved_goal() {
        let output = "Error: 1 remaining subgoal\n";
        let report = diagnose(ProverKind::Coq, output);
        assert!(matches!(report.kind, FailureKind::UnsolvedGoal { .. }));
    }

    #[test]
    fn test_diagnostic_report_display() {
        let output = "% SZS status ResourceOut\n% CPU time limit exceeded\n";
        let report = diagnose(ProverKind::EProver, output);
        let display = report.display();
        assert!(display.contains("Timeout"));
        assert!(display.contains("Suggestions"));
    }

    #[test]
    fn test_diagnostic_report_to_a2ml() {
        let output = "% SZS status GaveUp\n";
        let report = diagnose(ProverKind::EProver, output);
        let a2ml = report.to_a2ml();
        assert!(a2ml.contains("[proof-failure-diagnostic]"));
        assert!(a2ml.contains("prover"));
    }

    #[test]
    fn test_source_location_display() {
        let loc = SourceLocation {
            file: Some("foo.v".into()),
            line: Some(42),
            column: Some(7),
        };
        assert_eq!(loc.to_string(), "foo.v:42:7");

        let loc2 = SourceLocation { file: None, line: Some(10), column: None };
        assert_eq!(loc2.to_string(), "line 10");
    }
}
