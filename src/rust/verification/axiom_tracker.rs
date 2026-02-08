// SPDX-License-Identifier: PMPL-1.0-or-later

//! Axiom usage tracking and enforcement
//!
//! Scans proof results for dangerous axioms, escape hatches, and unsound
//! constructs across all supported provers. Enforces policies on axiom usage
//! to ensure proof trustworthiness.

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::provers::ProverKind;

/// Danger level of an axiom usage
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum DangerLevel {
    /// Standard library axiom -- allowed without restriction
    Safe,
    /// Classical axiom in constructive system -- noted but allowed
    Noted,
    /// Incomplete proof marker (sorry/Admitted) -- warning
    Warning,
    /// Known unsound construct -- REJECT
    Reject,
}

/// A tracked axiom usage found in proof content
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AxiomUsage {
    /// Prover that produced the proof
    pub prover: ProverKind,
    /// The axiom or construct found
    pub construct: String,
    /// Danger level
    pub danger_level: DangerLevel,
    /// Explanation of why this is dangerous
    pub explanation: String,
    /// Line number where found (if available)
    pub line: Option<usize>,
}

/// Axiom policy enforcement result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AxiomPolicy {
    /// Proof is clean -- only standard axioms used
    Clean,
    /// Proof has noted classical axiom usage
    ClassicalAxioms(Vec<AxiomUsage>),
    /// Proof has incomplete markers -- warning
    IncompleteProof(Vec<AxiomUsage>),
    /// Proof uses known unsound constructs -- REJECTED
    Rejected(Vec<AxiomUsage>),
}

impl AxiomPolicy {
    /// Whether the policy allows this proof to be trusted
    pub fn is_acceptable(&self) -> bool {
        !matches!(self, AxiomPolicy::Rejected(_))
    }

    /// Get the worst danger level in this policy
    pub fn worst_danger(&self) -> DangerLevel {
        match self {
            AxiomPolicy::Clean => DangerLevel::Safe,
            AxiomPolicy::ClassicalAxioms(_) => DangerLevel::Noted,
            AxiomPolicy::IncompleteProof(_) => DangerLevel::Warning,
            AxiomPolicy::Rejected(_) => DangerLevel::Reject,
        }
    }

    /// Get all axiom usages
    pub fn all_usages(&self) -> Vec<&AxiomUsage> {
        match self {
            AxiomPolicy::Clean => vec![],
            AxiomPolicy::ClassicalAxioms(u)
            | AxiomPolicy::IncompleteProof(u)
            | AxiomPolicy::Rejected(u) => u.iter().collect(),
        }
    }
}

/// Axiom tracker that scans proof content for dangerous constructs
pub struct AxiomTracker {
    /// Known dangerous patterns per prover
    patterns: HashMap<ProverKind, Vec<DangerousPattern>>,
}

/// A dangerous pattern to search for in proof content
#[derive(Debug, Clone)]
struct DangerousPattern {
    /// Pattern to search for (substring match)
    pattern: String,
    /// Danger level if found
    danger_level: DangerLevel,
    /// Explanation
    explanation: String,
}

impl AxiomTracker {
    /// Create a new axiom tracker with all known dangerous patterns
    pub fn new() -> Self {
        let mut patterns: HashMap<ProverKind, Vec<DangerousPattern>> = HashMap::new();

        // Lean4 dangerous constructs
        patterns.insert(ProverKind::Lean, vec![
            DangerousPattern {
                pattern: "sorry".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Incomplete proof -- 'sorry' is a placeholder for missing proof".to_string(),
            },
            DangerousPattern {
                pattern: "native_decide".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Uses native code evaluation -- bypasses kernel checking".to_string(),
            },
            DangerousPattern {
                pattern: "Decidable.decide".to_string(),
                danger_level: DangerLevel::Noted,
                explanation: "Decision procedure -- may not verify constructively".to_string(),
            },
        ]);

        // Coq dangerous constructs
        patterns.insert(ProverKind::Coq, vec![
            DangerousPattern {
                pattern: "Admitted".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Incomplete proof -- 'Admitted' accepts unproven goal".to_string(),
            },
            DangerousPattern {
                pattern: "admit".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Tactic 'admit' -- leaves goal unproven".to_string(),
            },
            DangerousPattern {
                pattern: "Axiom ".to_string(),
                danger_level: DangerLevel::Noted,
                explanation: "User-defined axiom -- not verified by kernel".to_string(),
            },
        ]);

        // Agda dangerous constructs
        patterns.insert(ProverKind::Agda, vec![
            DangerousPattern {
                pattern: "postulate".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Postulate -- assumed without proof".to_string(),
            },
            DangerousPattern {
                pattern: "--type-in-type".to_string(),
                danger_level: DangerLevel::Reject,
                explanation: "UNSOUND: --type-in-type collapses type hierarchy (Girard's paradox)".to_string(),
            },
            DangerousPattern {
                pattern: "OPTIONS --type-in-type".to_string(),
                danger_level: DangerLevel::Reject,
                explanation: "UNSOUND: --type-in-type in pragma collapses type hierarchy".to_string(),
            },
        ]);

        // Isabelle dangerous constructs
        patterns.insert(ProverKind::Isabelle, vec![
            DangerousPattern {
                pattern: "sorry".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Incomplete proof -- 'sorry' skips proof obligation".to_string(),
            },
            DangerousPattern {
                pattern: "oops".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Isabelle 'oops' -- intentionally incomplete proof".to_string(),
            },
        ]);

        // HOL4 dangerous constructs
        patterns.insert(ProverKind::HOL4, vec![
            DangerousPattern {
                pattern: "mk_thm".to_string(),
                danger_level: DangerLevel::Reject,
                explanation: "UNSOUND: mk_thm bypasses HOL4 kernel entirely".to_string(),
            },
        ]);

        // Idris2 dangerous constructs
        patterns.insert(ProverKind::Idris2, vec![
            DangerousPattern {
                pattern: "believe_me".to_string(),
                danger_level: DangerLevel::Reject,
                explanation: "UNSOUND: believe_me asserts any type equality without proof".to_string(),
            },
            DangerousPattern {
                pattern: "assert_total".to_string(),
                danger_level: DangerLevel::Warning,
                explanation: "Asserts totality without proof -- may hide non-termination".to_string(),
            },
        ]);

        Self { patterns }
    }

    /// Scan proof content for dangerous axiom usage
    pub fn scan(&self, prover: ProverKind, content: &str) -> Vec<AxiomUsage> {
        let mut usages = Vec::new();

        if let Some(prover_patterns) = self.patterns.get(&prover) {
            for (line_num, line) in content.lines().enumerate() {
                for pattern in prover_patterns {
                    if line.contains(&pattern.pattern) {
                        // Skip if it's in a comment
                        let trimmed = line.trim();
                        let is_comment = match prover {
                            ProverKind::Lean => trimmed.starts_with("--") || trimmed.starts_with("/-"),
                            ProverKind::Coq => trimmed.starts_with("(*"),
                            ProverKind::Agda => trimmed.starts_with("--") || (trimmed.starts_with("{-") && !trimmed.starts_with("{-#")),
                            ProverKind::Isabelle => trimmed.starts_with("(*"),
                            ProverKind::HOL4 => trimmed.starts_with("(*"),
                            ProverKind::Idris2 => trimmed.starts_with("--") || trimmed.starts_with("{-"),
                            _ => false,
                        };

                        if !is_comment {
                            usages.push(AxiomUsage {
                                prover,
                                construct: pattern.pattern.clone(),
                                danger_level: pattern.danger_level,
                                explanation: pattern.explanation.clone(),
                                line: Some(line_num + 1),
                            });
                        }
                    }
                }
            }
        }

        usages
    }

    /// Enforce axiom policy on scanned usages
    pub fn enforce_policy(&self, usages: &[AxiomUsage]) -> AxiomPolicy {
        if usages.is_empty() {
            return AxiomPolicy::Clean;
        }

        let has_rejected = usages.iter().any(|u| u.danger_level == DangerLevel::Reject);
        let has_warning = usages.iter().any(|u| u.danger_level == DangerLevel::Warning);
        let has_noted = usages.iter().any(|u| u.danger_level == DangerLevel::Noted);

        if has_rejected {
            let rejected: Vec<AxiomUsage> = usages.iter()
                .filter(|u| u.danger_level == DangerLevel::Reject)
                .cloned()
                .collect();
            AxiomPolicy::Rejected(rejected)
        } else if has_warning {
            let warnings: Vec<AxiomUsage> = usages.iter()
                .filter(|u| u.danger_level >= DangerLevel::Warning)
                .cloned()
                .collect();
            AxiomPolicy::IncompleteProof(warnings)
        } else if has_noted {
            let noted: Vec<AxiomUsage> = usages.iter()
                .filter(|u| u.danger_level >= DangerLevel::Noted)
                .cloned()
                .collect();
            AxiomPolicy::ClassicalAxioms(noted)
        } else {
            AxiomPolicy::Clean
        }
    }

    /// Convenience: scan and enforce in one call
    pub fn analyze(&self, prover: ProverKind, content: &str) -> AxiomPolicy {
        let usages = self.scan(prover, content);
        self.enforce_policy(&usages)
    }
}

impl Default for AxiomTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_sorry_detected() {
        let tracker = AxiomTracker::new();
        let content = "theorem foo : 1 + 1 = 2 := by sorry";
        let usages = tracker.scan(ProverKind::Lean, content);

        assert_eq!(usages.len(), 1);
        assert_eq!(usages[0].danger_level, DangerLevel::Warning);
        assert_eq!(usages[0].construct, "sorry");
    }

    #[test]
    fn test_agda_type_in_type_rejected() {
        let tracker = AxiomTracker::new();
        let content = "{-# OPTIONS --type-in-type #-}";
        let policy = tracker.analyze(ProverKind::Agda, content);

        assert!(!policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Reject);
    }

    #[test]
    fn test_clean_proof_passes() {
        let tracker = AxiomTracker::new();
        let content = "theorem plus_comm : forall a b, a + b = b + a := by omega";
        let policy = tracker.analyze(ProverKind::Lean, content);

        assert!(policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Safe);
    }

    #[test]
    fn test_hol4_mk_thm_rejected() {
        let tracker = AxiomTracker::new();
        let content = "val fake_thm = mk_thm ([], ``T``)";
        let policy = tracker.analyze(ProverKind::HOL4, content);

        assert!(!policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Reject);
    }

    #[test]
    fn test_coq_admitted_warning() {
        let tracker = AxiomTracker::new();
        let content = "Theorem foo : True.\nProof. Admitted.";
        let policy = tracker.analyze(ProverKind::Coq, content);

        assert!(policy.is_acceptable()); // Warning but not rejected
        assert_eq!(policy.worst_danger(), DangerLevel::Warning);
    }

    #[test]
    fn test_idris2_believe_me_rejected() {
        let tracker = AxiomTracker::new();
        let content = "unsafeProof : a = b\nunsafeProof = believe_me";
        let policy = tracker.analyze(ProverKind::Idris2, content);

        assert!(!policy.is_acceptable());
    }

    #[test]
    fn test_comment_not_flagged() {
        let tracker = AxiomTracker::new();
        let content = "-- sorry, this is just a comment\ntheorem foo : 1 = 1 := rfl";
        let usages = tracker.scan(ProverKind::Lean, content);

        // The 'sorry' in the comment should not be flagged
        assert!(usages.is_empty());
    }
}
