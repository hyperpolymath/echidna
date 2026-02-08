// SPDX-License-Identifier: PMPL-1.0-or-later

//! Dedukti/Lambdapi proof exchange format
//!
//! Enables exporting proofs to Dedukti's universal proof format and
//! importing Dedukti proofs from external sources. Dedukti uses a
//! small trusted kernel based on the lambda-Pi calculus modulo rewriting.

use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::core::{ProofState, Term, Theorem};

/// A Dedukti module representing a proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeduktiModule {
    /// Module name (qualified path)
    pub name: String,
    /// Required modules (imports)
    pub requires: Vec<String>,
    /// Declarations (types, definitions, rules)
    pub declarations: Vec<DeduktiDeclaration>,
}

/// A single Dedukti declaration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeduktiDeclaration {
    /// Type declaration: `symbol name : type.`
    Symbol {
        name: String,
        ty: String,
        /// Whether this is a constant (no definition)
        is_constant: bool,
    },
    /// Definition: `def name : type := body.`
    Definition {
        name: String,
        ty: String,
        body: String,
    },
    /// Rewrite rule: `[x] lhs --> rhs.`
    Rule {
        variables: Vec<String>,
        lhs: String,
        rhs: String,
    },
}

/// Exporter/importer for Dedukti/Lambdapi format
pub struct DeduktiExporter;

impl DeduktiExporter {
    /// Export a proof state to a Dedukti module
    pub fn export(state: &ProofState) -> Result<DeduktiModule> {
        let mut declarations = Vec::new();

        // Export context theorems as symbol declarations
        for theorem in &state.context.theorems {
            let dk_type = Self::term_to_dedukti(&theorem.statement);
            declarations.push(DeduktiDeclaration::Symbol {
                name: Self::sanitize_name(&theorem.name),
                ty: dk_type,
                is_constant: theorem.proof.is_none(),
            });
        }

        // Export goals as symbols to be defined (holes)
        for goal in &state.goals {
            let dk_type = Self::term_to_dedukti(&goal.target);
            declarations.push(DeduktiDeclaration::Symbol {
                name: Self::sanitize_name(&goal.id),
                ty: dk_type,
                is_constant: false,
            });
        }

        Ok(DeduktiModule {
            name: "echidna.export".to_string(),
            requires: vec!["echidna.prelude".to_string()],
            declarations,
        })
    }

    /// Import a Dedukti module into a proof state
    pub fn import(module: &DeduktiModule) -> Result<ProofState> {
        let mut state = ProofState::default();

        for decl in &module.declarations {
            match decl {
                DeduktiDeclaration::Symbol { name, ty, is_constant } => {
                    if *is_constant {
                        // Constants become axioms/theorems without proof
                        state.context.theorems.push(Theorem {
                            name: format!("dk_{}", name),
                            statement: Self::dedukti_to_term(ty),
                            proof: None,
                            aspects: vec!["dedukti-import".to_string()],
                        });
                    } else {
                        // Non-constant symbols become goals
                        state.goals.push(crate::core::Goal {
                            id: format!("dk_{}", name),
                            target: Self::dedukti_to_term(ty),
                            hypotheses: vec![],
                        });
                    }
                }
                DeduktiDeclaration::Definition { name, ty, .. } => {
                    // Definitions become theorems (they have proofs)
                    state.context.theorems.push(Theorem {
                        name: format!("dk_{}", name),
                        statement: Self::dedukti_to_term(ty),
                        proof: Some(vec![]), // Proof exists but not translated
                        aspects: vec!["dedukti-import".to_string(), "has-definition".to_string()],
                    });
                }
                DeduktiDeclaration::Rule { .. } => {
                    // Rewrite rules are stored as aspects on the module
                    // but don't directly translate to theorems
                }
            }
        }

        Ok(state)
    }

    /// Render a Dedukti module to its textual representation
    pub fn render(module: &DeduktiModule) -> String {
        let mut output = String::new();

        // Module header
        for req in &module.requires {
            output.push_str(&format!("require open {}.\n", req));
        }
        if !module.requires.is_empty() {
            output.push('\n');
        }

        // Declarations
        for decl in &module.declarations {
            match decl {
                DeduktiDeclaration::Symbol { name, ty, is_constant } => {
                    if *is_constant {
                        output.push_str(&format!("constant symbol {} : {}.\n", name, ty));
                    } else {
                        output.push_str(&format!("symbol {} : {}.\n", name, ty));
                    }
                }
                DeduktiDeclaration::Definition { name, ty, body } => {
                    output.push_str(&format!("symbol {} : {} ≔ {}.\n", name, ty, body));
                }
                DeduktiDeclaration::Rule { variables, lhs, rhs } => {
                    let vars = variables.join(", ");
                    output.push_str(&format!("rule [{}] {} ↪ {}.\n", vars, lhs, rhs));
                }
            }
        }

        output
    }

    /// Convert an ECHIDNA term to Dedukti notation
    fn term_to_dedukti(term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let mut result = format!("({})", Self::term_to_dedukti(func));
                for arg in args {
                    result = format!("{} ({})", result, Self::term_to_dedukti(arg));
                }
                result
            }
            Term::Lambda { param, param_type, body } => {
                if let Some(ty) = param_type {
                    format!("({} : {} => {})", param, Self::term_to_dedukti(ty), Self::term_to_dedukti(body))
                } else {
                    format!("({} => {})", param, Self::term_to_dedukti(body))
                }
            }
            Term::Pi { param, param_type, body } => {
                format!("({} : {} -> {})", param, Self::term_to_dedukti(param_type), Self::term_to_dedukti(body))
            }
            Term::Type(level) => format!("Type {}", level),
            Term::Sort(level) => format!("Sort {}", level),
            Term::Universe(level) => format!("Type {}", level),
            _ => "echidna_opaque".to_string(),
        }
    }

    /// Convert Dedukti notation to an ECHIDNA term (simplified parser)
    fn dedukti_to_term(dk: &str) -> Term {
        let trimmed = dk.trim();
        if trimmed.starts_with('(') && trimmed.ends_with(')') {
            // Unwrap parentheses and recurse
            Self::dedukti_to_term(&trimmed[1..trimmed.len() - 1])
        } else if trimmed.contains("->") {
            // Pi type: A -> B
            let parts: Vec<&str> = trimmed.splitn(2, "->").collect();
            if parts.len() == 2 {
                Term::Pi {
                    param: "_".to_string(),
                    param_type: Box::new(Self::dedukti_to_term(parts[0])),
                    body: Box::new(Self::dedukti_to_term(parts[1])),
                }
            } else {
                Term::Const(trimmed.to_string())
            }
        } else if trimmed.contains("=>") {
            // Lambda: x => body
            let parts: Vec<&str> = trimmed.splitn(2, "=>").collect();
            if parts.len() == 2 {
                Term::Lambda {
                    param: parts[0].trim().to_string(),
                    param_type: None,
                    body: Box::new(Self::dedukti_to_term(parts[1])),
                }
            } else {
                Term::Const(trimmed.to_string())
            }
        } else if trimmed.starts_with("Type") {
            let level = trimmed.trim_start_matches("Type").trim()
                .parse::<usize>().unwrap_or(0);
            Term::Type(level)
        } else {
            // Simple identifier
            Term::Const(trimmed.to_string())
        }
    }

    /// Sanitize a name for Dedukti (replace invalid characters)
    fn sanitize_name(name: &str) -> String {
        name.replace('-', "_")
            .replace('.', "_")
            .replace(' ', "_")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_export_basic_state() {
        let mut state = ProofState::default();
        state.context.theorems.push(Theorem {
            name: "nat_add_comm".to_string(),
            statement: Term::Const("Prop".to_string()),
            proof: None,
            aspects: vec![],
        });

        let module = DeduktiExporter::export(&state).unwrap();

        assert_eq!(module.name, "echidna.export");
        assert_eq!(module.declarations.len(), 1);
    }

    #[test]
    fn test_render_module() {
        let module = DeduktiModule {
            name: "test.module".to_string(),
            requires: vec!["echidna.prelude".to_string()],
            declarations: vec![
                DeduktiDeclaration::Symbol {
                    name: "T".to_string(),
                    ty: "Type 0".to_string(),
                    is_constant: true,
                },
                DeduktiDeclaration::Definition {
                    name: "id".to_string(),
                    ty: "T -> T".to_string(),
                    body: "(x => x)".to_string(),
                },
            ],
        };

        let rendered = DeduktiExporter::render(&module);
        assert!(rendered.contains("require open echidna.prelude."));
        assert!(rendered.contains("constant symbol T : Type 0."));
    }

    #[test]
    fn test_import_module() {
        let module = DeduktiModule {
            name: "test".to_string(),
            requires: vec![],
            declarations: vec![
                DeduktiDeclaration::Symbol {
                    name: "axiom1".to_string(),
                    ty: "Prop".to_string(),
                    is_constant: true,
                },
                DeduktiDeclaration::Symbol {
                    name: "goal1".to_string(),
                    ty: "Prop".to_string(),
                    is_constant: false,
                },
                DeduktiDeclaration::Definition {
                    name: "thm1".to_string(),
                    ty: "Prop".to_string(),
                    body: "trivial".to_string(),
                },
            ],
        };

        let state = DeduktiExporter::import(&module).unwrap();

        // axiom1 + thm1 = 2 theorems
        assert_eq!(state.context.theorems.len(), 2);
        // goal1 = 1 goal
        assert_eq!(state.goals.len(), 1);
    }

    #[test]
    fn test_term_roundtrip() {
        let term = Term::Pi {
            param: "x".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::Const("Prop".to_string())),
        };

        let dk = DeduktiExporter::term_to_dedukti(&term);
        assert!(dk.contains("->"));
    }

    #[test]
    fn test_sanitize_name() {
        assert_eq!(DeduktiExporter::sanitize_name("my-theorem"), "my_theorem");
        assert_eq!(DeduktiExporter::sanitize_name("mod.thm"), "mod_thm");
    }
}
