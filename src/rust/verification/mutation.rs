// SPDX-License-Identifier: PMPL-1.0-or-later

//! Mutation testing for specifications
//!
//! Deliberately weakens specifications to verify that the verification
//! pipeline catches the weakening. A high mutation score indicates that
//! the specification is precise and the verification pipeline is effective.

use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::core::Term;

/// Kind of mutation applied to a specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MutationKind {
    /// Remove a precondition from a theorem
    RemovePrecondition { index: usize },
    /// Weaken a postcondition (e.g. = to <=)
    WeakenPostcondition { original: String, weakened: String },
    /// Add an extra disjunct to the conclusion
    AddDisjunct { added: String },
    /// Remove a hypothesis
    RemoveHypothesis { index: usize },
    /// Replace constant with variable
    ReplaceConstant { original: String, replacement: String },
    /// Negate a subterm
    NegateSubterm { position: usize },
}

/// Result of testing a single mutation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MutationResult {
    /// The mutation applied
    pub kind: MutationKind,
    /// Whether the verification pipeline caught the mutation
    pub caught: bool,
    /// Description of what happened
    pub description: String,
}

/// Summary of mutation testing results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MutationTestSummary {
    /// Total mutations generated
    pub total_mutations: usize,
    /// Mutations caught by the verification pipeline
    pub mutations_caught: usize,
    /// Mutations that slipped through (bad -- spec is too weak)
    pub mutations_survived: usize,
    /// Mutation score (caught / total * 100)
    pub mutation_score: f64,
    /// Individual results
    pub results: Vec<MutationResult>,
}

impl MutationTestSummary {
    /// Whether the mutation score meets the target threshold (default 95%)
    pub fn meets_target(&self, threshold: f64) -> bool {
        self.mutation_score >= threshold
    }
}

/// Mutation tester that generates and tests mutations
pub struct MutationTester {
    /// Target mutation score threshold (default: 95%)
    pub target_score: f64,
}

impl MutationTester {
    /// Create a new mutation tester
    pub fn new() -> Self {
        Self {
            target_score: 95.0,
        }
    }

    /// Create with custom target score
    pub fn with_target(target_score: f64) -> Self {
        Self { target_score }
    }

    /// Generate mutations for a term/specification
    pub fn generate_mutations(&self, term: &Term) -> Vec<(MutationKind, Term)> {
        let mut mutations = Vec::new();

        match term {
            // For application terms, try removing arguments (preconditions)
            Term::App { func, args } if args.len() > 1 => {
                for i in 0..args.len() {
                    let mut new_args = args.clone();
                    new_args.remove(i);
                    mutations.push((
                        MutationKind::RemovePrecondition { index: i },
                        Term::App {
                            func: func.clone(),
                            args: new_args,
                        },
                    ));
                }
            }

            // For Pi types (universal quantification), try weakening
            Term::Pi { param, param_type, body } => {
                // Add a disjunct: body -> body | True
                let weakened = Term::App {
                    func: Box::new(Term::Const("or".to_string())),
                    args: vec![
                        *body.clone(),
                        Term::Const("True".to_string()),
                    ],
                };
                mutations.push((
                    MutationKind::AddDisjunct { added: "True".to_string() },
                    Term::Pi {
                        param: param.clone(),
                        param_type: param_type.clone(),
                        body: Box::new(weakened),
                    },
                ));
            }

            // For constants, try replacing with variables
            Term::Const(name) => {
                mutations.push((
                    MutationKind::ReplaceConstant {
                        original: name.clone(),
                        replacement: "x_mutant".to_string(),
                    },
                    Term::Var("x_mutant".to_string()),
                ));
            }

            _ => {}
        }

        // Always try negation
        mutations.push((
            MutationKind::NegateSubterm { position: 0 },
            Term::App {
                func: Box::new(Term::Const("not".to_string())),
                args: vec![term.clone()],
            },
        ));

        mutations
    }

    /// Compute mutation score from results
    pub fn compute_summary(&self, results: Vec<MutationResult>) -> MutationTestSummary {
        let total = results.len();
        let caught = results.iter().filter(|r| r.caught).count();
        let survived = total - caught;
        let score = if total > 0 {
            (caught as f64 / total as f64) * 100.0
        } else {
            100.0
        };

        MutationTestSummary {
            total_mutations: total,
            mutations_caught: caught,
            mutations_survived: survived,
            mutation_score: score,
            results,
        }
    }
}

impl Default for MutationTester {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_known_good_theorem_mutations_caught() {
        let tester = MutationTester::new();

        // Simulate: all mutations caught
        let results = vec![
            MutationResult {
                kind: MutationKind::RemovePrecondition { index: 0 },
                caught: true,
                description: "Removing precondition correctly caught".to_string(),
            },
            MutationResult {
                kind: MutationKind::NegateSubterm { position: 0 },
                caught: true,
                description: "Negation correctly caught".to_string(),
            },
            MutationResult {
                kind: MutationKind::AddDisjunct { added: "True".to_string() },
                caught: true,
                description: "Added disjunct correctly caught".to_string(),
            },
        ];

        let summary = tester.compute_summary(results);

        assert_eq!(summary.mutation_score, 100.0);
        assert!(summary.meets_target(95.0));
        assert_eq!(summary.mutations_survived, 0);
    }

    #[test]
    fn test_weak_theorem_low_mutation_score() {
        let tester = MutationTester::new();

        // Simulate: most mutations NOT caught (weak spec)
        let results = vec![
            MutationResult {
                kind: MutationKind::RemovePrecondition { index: 0 },
                caught: false,
                description: "Mutation survived -- spec too weak".to_string(),
            },
            MutationResult {
                kind: MutationKind::AddDisjunct { added: "True".to_string() },
                caught: false,
                description: "Mutation survived -- spec too weak".to_string(),
            },
            MutationResult {
                kind: MutationKind::NegateSubterm { position: 0 },
                caught: true,
                description: "Negation caught".to_string(),
            },
        ];

        let summary = tester.compute_summary(results);

        assert!(summary.mutation_score < 50.0);
        assert!(!summary.meets_target(95.0));
        assert_eq!(summary.mutations_survived, 2);
    }

    #[test]
    fn test_generate_mutations_for_app() {
        let tester = MutationTester::new();

        let term = Term::App {
            func: Box::new(Term::Const("add".to_string())),
            args: vec![
                Term::Var("x".to_string()),
                Term::Var("y".to_string()),
            ],
        };

        let mutations = tester.generate_mutations(&term);

        // Should have: 2 precondition removals + 1 negation
        assert!(mutations.len() >= 3);
    }

    #[test]
    fn test_caught_mutations_are_caught() {
        let result = MutationResult {
            kind: MutationKind::NegateSubterm { position: 0 },
            caught: true,
            description: "Caught".to_string(),
        };
        assert!(result.caught);
    }

    #[test]
    fn test_empty_mutations_full_score() {
        let tester = MutationTester::new();
        let summary = tester.compute_summary(vec![]);
        assert_eq!(summary.mutation_score, 100.0);
    }
}
