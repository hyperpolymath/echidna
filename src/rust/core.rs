// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Core types and abstractions for ECHIDNA theorem proving

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

/// Universal representation of a mathematical term across all provers
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Term {
    /// Variable with name
    Var(String),

    /// Constant/atom
    Const(String),

    /// Function application f(args...)
    App {
        func: Box<Term>,
        args: Vec<Term>,
    },

    /// Lambda abstraction λx. body
    Lambda {
        param: String,
        param_type: Option<Box<Term>>,
        body: Box<Term>,
    },

    /// Dependent product (Pi type) Π(x: A). B
    Pi {
        param: String,
        param_type: Box<Term>,
        body: Box<Term>,
    },

    /// Type universe at level
    Type(usize),

    /// Sort universe at level
    Sort(usize),

    /// Type universe (legacy alias for Type)
    Universe(usize),

    /// Let binding: let name : ty = value in body
    Let {
        name: String,
        ty: Option<Box<Term>>,
        value: Box<Term>,
        body: Box<Term>,
    },

    /// Pattern matching: match scrutinee with branches
    Match {
        scrutinee: Box<Term>,
        return_type: Option<Box<Term>>,
        branches: Vec<(Pattern, Term)>,
    },

    /// Fixed-point combinator: fix name. body
    Fix {
        name: String,
        ty: Option<Box<Term>>,
        body: Box<Term>,
    },

    /// Hole/goal marker
    Hole(String),

    /// Meta-variable (for unification)
    Meta(usize),

    /// Prover-specific term (escape hatch)
    ProverSpecific {
        prover: String,
        data: serde_json::Value,
    },
}

/// Pattern for match expressions
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Pattern {
    /// Wildcard pattern _
    Wildcard,
    /// Variable pattern
    Var(String),
    /// Constructor pattern C(p1, p2, ...)
    Constructor {
        name: String,
        args: Vec<Pattern>,
    },
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{}", name),
            Term::Const(name) => write!(f, "{}", name),
            Term::App { func, args } => {
                write!(f, "({} ", func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            },
            Term::Lambda { param, param_type, body } => {
                if let Some(ty) = param_type {
                    write!(f, "(λ {}: {}. {})", param, ty, body)
                } else {
                    write!(f, "(λ {}. {})", param, body)
                }
            },
            Term::Pi { param, param_type, body } => {
                write!(f, "(Π {}: {}. {})", param, param_type, body)
            },
            Term::Type(level) => write!(f, "Type{}", level),
            Term::Sort(level) => write!(f, "Sort{}", level),
            Term::Universe(level) => write!(f, "Type{}", level),
            Term::Let { name, ty, value, body } => {
                if let Some(t) = ty {
                    write!(f, "(let {} : {} = {} in {})", name, t, value, body)
                } else {
                    write!(f, "(let {} = {} in {})", name, value, body)
                }
            },
            Term::Match { scrutinee, .. } => {
                write!(f, "(match {} with ...)", scrutinee)
            },
            Term::Fix { name, body, .. } => {
                write!(f, "(fix {}. {})", name, body)
            },
            Term::Hole(name) => write!(f, "?{}", name),
            Term::Meta(id) => write!(f, "?{}", id),
            Term::ProverSpecific { prover, .. } => write!(f, "<{}-term>", prover),
        }
    }
}

/// Current state of a proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofState {
    /// Current goals to prove
    pub goals: Vec<Goal>,

    /// Available hypotheses/premises
    pub context: Context,

    /// Proof script so far
    pub proof_script: Vec<Tactic>,

    /// Metadata
    pub metadata: HashMap<String, serde_json::Value>,
}

/// A single proof goal
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Goal {
    /// Goal identifier
    pub id: String,

    /// Target term to prove
    pub target: Term,

    /// Local hypotheses for this goal
    pub hypotheses: Vec<Hypothesis>,
}

/// A hypothesis in the context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hypothesis {
    /// Hypothesis name
    pub name: String,

    /// Hypothesis type/statement
    pub ty: Term,

    /// Optional body (for definitions)
    pub body: Option<Term>,
}

/// Proof context with available premises
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Context {
    /// Available theorems/lemmas
    pub theorems: Vec<Theorem>,

    /// Type definitions
    pub definitions: Vec<Definition>,

    /// Local variables
    pub variables: Vec<Variable>,
}

/// A theorem/lemma
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Theorem {
    pub name: String,
    pub statement: Term,
    pub proof: Option<Vec<Tactic>>,
    pub aspects: Vec<String>,  // Aspect tags
}

/// A type/function definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Definition {
    pub name: String,
    pub ty: Term,
    pub body: Term,
}

/// A variable declaration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Variable {
    pub name: String,
    pub ty: Term,
}

/// A proof tactic/command
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Tactic {
    /// Apply a theorem/lemma
    Apply(String),

    /// Introduce a hypothesis
    Intro(Option<String>),

    /// Case split
    Cases(Term),

    /// Induction on a term
    Induction(Term),

    /// Rewrite using an equation
    Rewrite(String),

    /// Simplification
    Simplify,

    /// Reflexivity
    Reflexivity,

    /// Assumption (solve with hypothesis)
    Assumption,

    /// Exact term
    Exact(Term),

    /// Custom tactic for specific prover
    Custom {
        prover: String,
        command: String,
        args: Vec<String>,
    },
}

/// Result of applying a tactic
#[derive(Debug, Clone)]
pub enum TacticResult {
    /// Tactic succeeded, new state
    Success(ProofState),

    /// Tactic failed with error
    Error(String),

    /// Proof complete!
    QED,
}

impl ProofState {
    pub fn new(goal: Term) -> Self {
        ProofState {
            goals: vec![Goal {
                id: "goal_0".to_string(),
                target: goal,
                hypotheses: vec![],
            }],
            context: Context::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        }
    }

    pub fn is_complete(&self) -> bool {
        self.goals.is_empty()
    }
}
