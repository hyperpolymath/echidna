// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Axiom usage tracking
//!
//! Parses ECHIDNA proof results for axiom usage patterns that indicate
//! incomplete or potentially unsound proofs. Detects:
//!
//! - `sorry` (Lean4) -- unproved goal marker
//! - `Admitted` (Coq) -- unproved lemma
//! - `postulate` (Agda) -- assumed axiom
//! - `choice` (Lean4/HOL) -- axiom of choice usage
//! - `--type-in-type` (Agda) -- type system inconsistency
//! - `oops` (Isabelle) -- retracted proof
//! - `axiom` (Lean4) -- user-declared axiom
//! - `assume` (Metamath) -- hypothesis without proof
//! - Classical logic axioms (excluded middle, double negation elimination)

use serde::{Deserialize, Serialize};

use crate::dispatcher::ProverKind;

/// Type of axiom flag detected in proof output
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AxiomFlag {
    /// `sorry` in Lean4 -- unproved goal
    Sorry,
    /// `Admitted` in Coq -- unproved lemma
    Admitted,
    /// `postulate` in Agda -- assumed proposition
    Postulate,
    /// `axiom` in Lean4 -- user-declared axiom
    UserAxiom,
    /// `choice` / axiom of choice
    AxiomOfChoice,
    /// `--type-in-type` in Agda -- makes type system inconsistent
    TypeInType,
    /// `oops` in Isabelle -- retracted proof
    Oops,
    /// `assume` in Metamath without discharge
    UndischargedAssumption,
    /// Classical logic axiom (excluded middle, etc.)
    ClassicalAxiom,
    /// Other axiom-like construct
    Other(String),
}

impl AxiomFlag {
    /// Severity of this axiom flag (higher = more concerning)
    ///
    /// - 3: Definitely unsound (sorry, Admitted, oops, type-in-type)
    /// - 2: Potentially problematic (postulate, user axiom, undischarged assumption)
    /// - 1: Informational (choice, classical axiom, other)
    pub fn severity(&self) -> u8 {
        match self {
            Self::Sorry | Self::Admitted | Self::Oops | Self::TypeInType => 3,
            Self::Postulate | Self::UserAxiom | Self::UndischargedAssumption => 2,
            Self::AxiomOfChoice | Self::ClassicalAxiom | Self::Other(_) => 1,
        }
    }

    /// Human-readable description
    pub fn description(&self) -> String {
        match self {
            Self::Sorry => "sorry: unproved goal (Lean4)".to_string(),
            Self::Admitted => "Admitted: unproved lemma (Coq)".to_string(),
            Self::Postulate => "postulate: assumed proposition (Agda)".to_string(),
            Self::UserAxiom => "axiom: user-declared axiom".to_string(),
            Self::AxiomOfChoice => "Axiom of Choice usage".to_string(),
            Self::TypeInType => "--type-in-type: inconsistent type system (Agda)".to_string(),
            Self::Oops => "oops: retracted proof (Isabelle)".to_string(),
            Self::UndischargedAssumption => "Undischarged assumption".to_string(),
            Self::ClassicalAxiom => "Classical logic axiom usage".to_string(),
            Self::Other(name) => format!("Other axiom: {}", name),
        }
    }

    /// Whether this flag indicates the proof is definitely incomplete
    pub fn is_unsound(&self) -> bool {
        self.severity() >= 3
    }
}

impl std::fmt::Display for AxiomFlag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

/// Report of all axiom flags detected in a proof output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AxiomReport {
    /// Prover that produced the output
    pub prover: ProverKind,
    /// All detected axiom flags
    pub flags: Vec<AxiomFlag>,
    /// Number of flags with severity >= 3 (unsound)
    pub unsound_count: usize,
    /// Number of flags with severity >= 2 (potentially problematic)
    pub warning_count: usize,
    /// Overall assessment
    pub clean: bool,
}

impl AxiomReport {
    /// Whether any unsound flags were detected (sorry, Admitted, etc.)
    pub fn has_unsound(&self) -> bool {
        self.unsound_count > 0
    }

    /// Get all flags at or above a given severity level
    pub fn flags_at_severity(&self, min_severity: u8) -> Vec<&AxiomFlag> {
        self.flags.iter().filter(|f| f.severity() >= min_severity).collect()
    }

    /// Format as a human-readable summary
    pub fn summary(&self) -> String {
        if self.clean {
            return "No axiom flags detected (clean proof)".to_string();
        }

        let mut parts = Vec::new();
        if self.unsound_count > 0 {
            parts.push(format!("{} unsound flag(s)", self.unsound_count));
        }
        if self.warning_count > 0 {
            parts.push(format!("{} warning(s)", self.warning_count));
        }
        let info = self.flags.len() - self.unsound_count - self.warning_count;
        if info > 0 {
            parts.push(format!("{} info", info));
        }
        parts.join(", ")
    }
}

/// Axiom usage tracker.
///
/// Scans prover output for axiom-related patterns and produces
/// reports about proof soundness.
pub struct AxiomTracker;

impl AxiomTracker {
    /// Scan prover output for axiom usage flags.
    ///
    /// # Arguments
    /// * `prover` - Which prover produced the output
    /// * `output` - Raw prover output (stdout + stderr)
    pub fn scan(prover: ProverKind, output: &str) -> AxiomReport {
        let mut flags = Vec::new();
        let output_lower = output.to_lowercase();

        // Prover-specific patterns
        match prover {
            ProverKind::Lean => scan_lean(&output_lower, &mut flags),
            ProverKind::Coq => scan_coq(&output_lower, &mut flags),
            ProverKind::Agda => scan_agda(output, &output_lower, &mut flags),
            ProverKind::Isabelle => scan_isabelle(&output_lower, &mut flags),
            ProverKind::Metamath => scan_metamath(&output_lower, &mut flags),
            _ => scan_generic(&output_lower, &mut flags),
        }

        // Universal patterns (apply to all provers)
        scan_universal(&output_lower, &mut flags);

        // Deduplicate flags
        flags.sort_by_key(|f| std::cmp::Reverse(f.severity()));
        flags.dedup();

        let unsound_count = flags.iter().filter(|f| f.severity() >= 3).count();
        let warning_count = flags.iter().filter(|f| f.severity() == 2).count();
        let clean = flags.is_empty();

        AxiomReport {
            prover,
            flags,
            unsound_count,
            warning_count,
            clean,
        }
    }
}

/// Scan for Lean4-specific axiom patterns
fn scan_lean(output: &str, flags: &mut Vec<AxiomFlag>) {
    if output.contains("sorry") {
        flags.push(AxiomFlag::Sorry);
    }
    if output.contains("axiom ") || output.contains("noncomputable axiom") {
        flags.push(AxiomFlag::UserAxiom);
    }
    if output.contains("classical.choice") || output.contains("quot.mk") {
        flags.push(AxiomFlag::AxiomOfChoice);
    }
}

/// Scan for Coq-specific axiom patterns
fn scan_coq(output: &str, flags: &mut Vec<AxiomFlag>) {
    if output.contains("admitted") {
        flags.push(AxiomFlag::Admitted);
    }
    if output.contains("axiom ") || output.contains("parameter ") {
        flags.push(AxiomFlag::UserAxiom);
    }
    // Coq's classical axioms
    if output.contains("classic") || output.contains("excluded_middle") {
        flags.push(AxiomFlag::ClassicalAxiom);
    }
}

/// Scan for Agda-specific axiom patterns
fn scan_agda(raw_output: &str, output: &str, flags: &mut Vec<AxiomFlag>) {
    if output.contains("postulate") {
        flags.push(AxiomFlag::Postulate);
    }
    // Check case-sensitive for --type-in-type flag
    if raw_output.contains("--type-in-type") || output.contains("type-in-type") {
        flags.push(AxiomFlag::TypeInType);
    }
}

/// Scan for Isabelle-specific axiom patterns
fn scan_isabelle(output: &str, flags: &mut Vec<AxiomFlag>) {
    if output.contains("oops") {
        flags.push(AxiomFlag::Oops);
    }
    if output.contains("sorry") {
        flags.push(AxiomFlag::Sorry);
    }
    if output.contains("axiomatization") {
        flags.push(AxiomFlag::UserAxiom);
    }
}

/// Scan for Metamath-specific axiom patterns
fn scan_metamath(output: &str, flags: &mut Vec<AxiomFlag>) {
    // Metamath uses $a for axiomatic assertions
    if output.contains("$a ") || output.contains("axiom") {
        flags.push(AxiomFlag::UserAxiom);
    }
    // Undischarged hypotheses
    if output.contains("hypothesis not discharged")
        || output.contains("floating hypothesis")
    {
        flags.push(AxiomFlag::UndischargedAssumption);
    }
}

/// Scan for generic patterns that apply to any prover
fn scan_generic(output: &str, flags: &mut Vec<AxiomFlag>) {
    if output.contains("sorry") {
        flags.push(AxiomFlag::Sorry);
    }
    if output.contains("admitted") {
        flags.push(AxiomFlag::Admitted);
    }
}

/// Scan for universal patterns across all provers
fn scan_universal(output: &str, flags: &mut Vec<AxiomFlag>) {
    // Axiom of choice (applies to most provers)
    if (output.contains("axiom of choice") || output.contains("hilbert choice"))
        && !flags.contains(&AxiomFlag::AxiomOfChoice)
    {
        flags.push(AxiomFlag::AxiomOfChoice);
    }

    // Classical logic indicators
    if (output.contains("excluded middle")
        || output.contains("double negation elimination")
        || output.contains("law of excluded middle"))
        && !flags.contains(&AxiomFlag::ClassicalAxiom)
    {
        flags.push(AxiomFlag::ClassicalAxiom);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clean_proof_no_flags() {
        let report = AxiomTracker::scan(
            ProverKind::Lean,
            "All goals discharged successfully.\nProof complete.",
        );
        assert!(report.clean);
        assert!(report.flags.is_empty());
        assert_eq!(report.unsound_count, 0);
    }

    #[test]
    fn test_lean_sorry_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Lean,
            "declaration uses 'sorry'\nTest.lean:42:5: error: tactic 'sorry' is not allowed",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::Sorry));
        assert!(report.has_unsound());
    }

    #[test]
    fn test_coq_admitted_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Coq,
            "Axioms:\nmyLemma : forall x, P x\n Admitted.",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::Admitted));
        assert!(report.has_unsound());
    }

    #[test]
    fn test_agda_postulate_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Agda,
            "postulate\n  funext : ...",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::Postulate));
        assert_eq!(report.flags[0].severity(), 2); // Warning level
    }

    #[test]
    fn test_agda_type_in_type_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Agda,
            "Checking with --type-in-type enabled\nAll goals discharged",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::TypeInType));
        assert!(report.has_unsound());
    }

    #[test]
    fn test_isabelle_oops_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Isabelle,
            "lemma foo: \"True\" oops",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::Oops));
        assert!(report.has_unsound());
    }

    #[test]
    fn test_metamath_axiom_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Metamath,
            "$a axiom |- ( ph -> ps )",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::UserAxiom));
    }

    #[test]
    fn test_classical_axiom_detected() {
        let report = AxiomTracker::scan(
            ProverKind::Coq,
            "Uses: Excluded Middle\nClassic imported",
        );
        assert!(!report.clean);
        assert!(report.flags.contains(&AxiomFlag::ClassicalAxiom));
    }

    #[test]
    fn test_axiom_flag_severity() {
        assert_eq!(AxiomFlag::Sorry.severity(), 3);
        assert_eq!(AxiomFlag::Admitted.severity(), 3);
        assert_eq!(AxiomFlag::Oops.severity(), 3);
        assert_eq!(AxiomFlag::TypeInType.severity(), 3);

        assert_eq!(AxiomFlag::Postulate.severity(), 2);
        assert_eq!(AxiomFlag::UserAxiom.severity(), 2);
        assert_eq!(AxiomFlag::UndischargedAssumption.severity(), 2);

        assert_eq!(AxiomFlag::AxiomOfChoice.severity(), 1);
        assert_eq!(AxiomFlag::ClassicalAxiom.severity(), 1);
    }

    #[test]
    fn test_is_unsound() {
        assert!(AxiomFlag::Sorry.is_unsound());
        assert!(AxiomFlag::Admitted.is_unsound());
        assert!(!AxiomFlag::Postulate.is_unsound());
        assert!(!AxiomFlag::AxiomOfChoice.is_unsound());
    }

    #[test]
    fn test_report_summary() {
        let report = AxiomTracker::scan(
            ProverKind::Lean,
            "sorry used\naxiom myAxiom\nclassical.choice",
        );
        let summary = report.summary();
        assert!(summary.contains("unsound"));
    }

    #[test]
    fn test_clean_report_summary() {
        let report = AxiomTracker::scan(
            ProverKind::Z3,
            "sat\n(model ...)",
        );
        let summary = report.summary();
        assert!(summary.contains("clean"));
    }

    #[test]
    fn test_flags_at_severity() {
        let report = AxiomTracker::scan(
            ProverKind::Lean,
            "sorry\naxiom myAxiom\nclassical.choice",
        );
        let critical = report.flags_at_severity(3);
        assert_eq!(critical.len(), 1); // Only sorry
        let warnings = report.flags_at_severity(2);
        assert!(warnings.len() >= 2); // sorry + axiom
    }
}
