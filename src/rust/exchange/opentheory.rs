// SPDX-License-Identifier: PMPL-1.0-or-later

//! OpenTheory proof exchange format
//!
//! Enables cross-checking between HOL4, HOL Light, and Isabelle/HOL
//! by importing/exporting proofs in the OpenTheory format.

use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::core::{ProofState, Term, Theorem};

/// OpenTheory article representation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenTheoryArticle {
    /// Article name
    pub name: String,
    /// Assumptions (imported theorems)
    pub assumptions: Vec<OpenTheoryTheorem>,
    /// Conclusions (exported theorems)
    pub conclusions: Vec<OpenTheoryTheorem>,
    /// Raw OpenTheory commands
    pub commands: Vec<String>,
}

/// An OpenTheory theorem
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenTheoryTheorem {
    /// Hypotheses
    pub hypotheses: Vec<String>,
    /// Conclusion term
    pub conclusion: String,
}

/// Exporter for OpenTheory format
pub struct OpenTheoryExporter;

impl OpenTheoryExporter {
    /// Export a proof state to OpenTheory article format
    pub fn export(state: &ProofState) -> Result<OpenTheoryArticle> {
        let mut commands = Vec::new();

        // OpenTheory article header
        commands.push("version 6".to_string());

        // Export context theorems as assumptions
        let mut assumptions = Vec::new();
        for theorem in &state.context.theorems {
            let ot_thm = Self::term_to_opentheory(&theorem.statement);
            assumptions.push(OpenTheoryTheorem {
                hypotheses: vec![],
                conclusion: ot_thm.clone(),
            });
            commands.push(format!("assume {}", ot_thm));
        }

        // Export goals as conclusions
        let mut conclusions = Vec::new();
        for goal in &state.goals {
            let ot_goal = Self::term_to_opentheory(&goal.target);
            conclusions.push(OpenTheoryTheorem {
                hypotheses: vec![],
                conclusion: ot_goal,
            });
        }

        Ok(OpenTheoryArticle {
            name: "echidna-export".to_string(),
            assumptions,
            conclusions,
            commands,
        })
    }

    /// Import an OpenTheory article into a proof state
    pub fn import(article: &OpenTheoryArticle) -> Result<ProofState> {
        let mut state = ProofState::default();

        for assumption in &article.assumptions {
            state.context.theorems.push(Theorem {
                name: format!("ot_assumption_{}", state.context.theorems.len()),
                statement: Self::opentheory_to_term(&assumption.conclusion),
                proof: None,
                aspects: vec!["opentheory-import".to_string()],
            });
        }

        for conclusion in &article.conclusions {
            state.goals.push(crate::core::Goal {
                id: format!("ot_goal_{}", state.goals.len()),
                target: Self::opentheory_to_term(&conclusion.conclusion),
                hypotheses: vec![],
            });
        }

        Ok(state)
    }

    /// Convert an ECHIDNA term to OpenTheory notation
    fn term_to_opentheory(term: &Term) -> String {
        match term {
            Term::Var(name) => format!("var \"{}\"", name),
            Term::Const(name) => format!("const \"{}\"", name),
            Term::App { func, args } => {
                let mut result = Self::term_to_opentheory(func);
                for arg in args {
                    result = format!("app {} {}", result, Self::term_to_opentheory(arg));
                }
                result
            }
            Term::Lambda { param, body, .. } => {
                format!("abs (var \"{}\") {}", param, Self::term_to_opentheory(body))
            }
            _ => format!("const \"echidna_opaque\""),
        }
    }

    /// Convert OpenTheory notation to ECHIDNA term (simplified)
    fn opentheory_to_term(ot: &str) -> Term {
        let trimmed = ot.trim();
        if trimmed.starts_with("var ") {
            let name = trimmed.trim_start_matches("var ")
                .trim_matches('"')
                .to_string();
            Term::Var(name)
        } else if trimmed.starts_with("const ") {
            let name = trimmed.trim_start_matches("const ")
                .trim_matches('"')
                .to_string();
            Term::Const(name)
        } else {
            Term::Const(trimmed.to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_export_roundtrip() {
        let mut state = ProofState::default();
        state.context.theorems.push(Theorem {
            name: "test_thm".to_string(),
            statement: Term::Const("True".to_string()),
            proof: None,
            aspects: vec![],
        });

        let article = OpenTheoryExporter::export(&state).unwrap();

        assert_eq!(article.assumptions.len(), 1);
        assert!(article.commands.contains(&"version 6".to_string()));
    }

    #[test]
    fn test_import_creates_state() {
        let article = OpenTheoryArticle {
            name: "test".to_string(),
            assumptions: vec![
                OpenTheoryTheorem {
                    hypotheses: vec![],
                    conclusion: "const \"True\"".to_string(),
                },
            ],
            conclusions: vec![
                OpenTheoryTheorem {
                    hypotheses: vec![],
                    conclusion: "const \"False\"".to_string(),
                },
            ],
            commands: vec![],
        };

        let state = OpenTheoryExporter::import(&article).unwrap();

        assert_eq!(state.context.theorems.len(), 1);
        assert_eq!(state.goals.len(), 1);
    }

    #[test]
    fn test_export_import_roundtrip() {
        let mut state = ProofState::default();
        state.context.theorems.push(Theorem {
            name: "roundtrip_thm".to_string(),
            statement: Term::Var("x".to_string()),
            proof: None,
            aspects: vec![],
        });

        let article = OpenTheoryExporter::export(&state).unwrap();
        let reimported = OpenTheoryExporter::import(&article).unwrap();

        assert_eq!(reimported.context.theorems.len(), 1);
    }
}
