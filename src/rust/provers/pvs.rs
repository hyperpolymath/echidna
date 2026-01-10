// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! PVS (Prototype Verification System) backend implementation.
//!
//! PVS is a specification and verification system from SRI International.
//! It features:
//! - Higher-order logic specification language
//! - Rich type system with subtypes, dependent types, predicate subtypes
//! - Tactic-based proof assistant with powerful automation
//! - Type Correctness Conditions (TCCs) generation
//! - Decision procedures integration (Yices, Z3)

use async_trait::async_trait;
use anyhow::{Result, Context, bail};
use std::collections::HashMap;
use std::path::PathBuf;
use tokio::sync::Mutex;
use tokio::process::Command;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout};

use crate::core::{
    Context as CoreContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult, Term, Theorem,
};
use super::{ProverBackend, ProverConfig, ProverKind};

// ============================================================================
// PVS AST Types
// ============================================================================

/// PVS expression types
#[derive(Debug, Clone, PartialEq)]
pub enum PVSExpr {
    /// Variable or constant reference
    Name(String),
    /// Numeric literal
    Number(i64),
    /// Rational literal
    Rational(i64, i64),
    /// String literal
    StringLit(String),
    /// Function application: f(a1, ..., an)
    Application {
        function: Box<PVSExpr>,
        arguments: Vec<PVSExpr>,
    },
    /// Lambda expression: LAMBDA (x: T): e
    Lambda {
        bindings: Vec<PVSBinding>,
        body: Box<PVSExpr>,
    },
    /// Universal quantification: FORALL (x: T): e
    Forall {
        bindings: Vec<PVSBinding>,
        body: Box<PVSExpr>,
    },
    /// Existential quantification: EXISTS (x: T): e
    Exists {
        bindings: Vec<PVSBinding>,
        body: Box<PVSExpr>,
    },
    /// Conditional: IF c THEN t ELSE e ENDIF
    IfThenElse {
        condition: Box<PVSExpr>,
        then_branch: Box<PVSExpr>,
        else_branch: Box<PVSExpr>,
    },
    /// Let binding: LET x = e IN body
    Let {
        bindings: Vec<(String, PVSExpr)>,
        body: Box<PVSExpr>,
    },
    /// Case expression: CASES e OF ... ENDCASES
    Cases {
        expr: Box<PVSExpr>,
        selections: Vec<PVSCaseSelection>,
        else_clause: Option<Box<PVSExpr>>,
    },
    /// Record expression: (# field1 := e1, ... #)
    Record(Vec<(String, PVSExpr)>),
    /// Record field access: e`field
    RecordAccess {
        record: Box<PVSExpr>,
        field: String,
    },
    /// Tuple expression: (e1, e2, ...)
    Tuple(Vec<PVSExpr>),
    /// Projection: e`n
    Projection {
        tuple: Box<PVSExpr>,
        index: usize,
    },
    /// Array/function update: e WITH [i := v]
    Update {
        base: Box<PVSExpr>,
        assignments: Vec<(Vec<PVSExpr>, PVSExpr)>,
    },
    /// Type coercion: e :: T
    Coercion {
        expr: Box<PVSExpr>,
        target_type: Box<PVSType>,
    },
    /// Set enumeration: {e1, e2, ...}
    SetEnumeration(Vec<PVSExpr>),
    /// Set comprehension: {x: T | P(x)}
    SetComprehension {
        binding: PVSBinding,
        predicate: Box<PVSExpr>,
    },
}

/// PVS binding (variable with type)
#[derive(Debug, Clone, PartialEq)]
pub struct PVSBinding {
    pub name: String,
    pub var_type: Box<PVSType>,
}

/// PVS case selection
#[derive(Debug, Clone, PartialEq)]
pub struct PVSCaseSelection {
    pub pattern: PVSPattern,
    pub expr: PVSExpr,
}

/// PVS pattern for case matching
#[derive(Debug, Clone, PartialEq)]
pub enum PVSPattern {
    /// Wildcard pattern _
    Wildcard,
    /// Variable pattern
    Variable(String),
    /// Constructor pattern
    Constructor {
        name: String,
        args: Vec<String>,
    },
    /// Literal pattern
    Literal(PVSExpr),
}

/// PVS type expressions
#[derive(Debug, Clone, PartialEq)]
pub enum PVSType {
    /// Type name reference
    Name(String),
    /// Type application: T[a1, ..., an]
    Application {
        base: Box<PVSType>,
        arguments: Vec<PVSType>,
    },
    /// Function type: [D -> R]
    Function {
        domain: Box<PVSType>,
        range: Box<PVSType>,
    },
    /// Product/tuple type: [T1, T2, ...]
    Product(Vec<PVSType>),
    /// Record type: [# field1: T1, ... #]
    Record(Vec<(String, PVSType)>),
    /// Subtype: {x: T | P(x)}
    Subtype {
        base: Box<PVSType>,
        predicate: Box<PVSExpr>,
    },
    /// Dependent function type: [x: D -> R(x)]
    Dependent {
        binding: PVSBinding,
        range: Box<PVSType>,
    },
    /// Set type: set[T]
    SetOf(Box<PVSType>),
    /// Sequence type: sequence[T]
    Sequence(Box<PVSType>),
}

// ============================================================================
// PVS Theory Structure
// ============================================================================

/// A PVS theory declaration
#[derive(Debug, Clone)]
pub struct PVSTheory {
    pub name: String,
    pub parameters: Vec<PVSFormalParameter>,
    pub assuming: Vec<PVSAssumption>,
    pub declarations: Vec<PVSDeclaration>,
    pub importing: Vec<PVSImporting>,
}

/// Formal parameter for parameterised theories
#[derive(Debug, Clone)]
pub struct PVSFormalParameter {
    pub name: String,
    pub kind: PVSParameterKind,
}

#[derive(Debug, Clone)]
pub enum PVSParameterKind {
    Type,
    Constant(PVSType),
    Theory(String),
}

/// Assumption (ASSUMING clause)
#[derive(Debug, Clone)]
pub struct PVSAssumption {
    pub name: String,
    pub formula: PVSExpr,
}

/// Theory importing
#[derive(Debug, Clone)]
pub struct PVSImporting {
    pub theory: String,
    pub actuals: Vec<PVSExpr>,
}

/// PVS declaration within a theory
#[derive(Debug, Clone)]
pub enum PVSDeclaration {
    /// Type declaration
    TypeDecl {
        name: String,
        definition: Option<PVSType>,
    },
    /// Constant declaration
    ConstDecl {
        name: String,
        declared_type: PVSType,
        definition: Option<PVSExpr>,
    },
    /// Formula (axiom, lemma, theorem)
    FormulaDecl {
        name: String,
        kind: PVSFormulaKind,
        formula: PVSExpr,
    },
    /// Inductive datatype
    Datatype {
        name: String,
        constructors: Vec<PVSConstructor>,
    },
    /// Recursive function definition
    RecursiveDecl {
        name: String,
        signature: PVSType,
        measure: Option<PVSExpr>,
        body: PVSExpr,
    },
    /// Judgement declaration
    Judgement {
        kind: PVSJudgementKind,
        name: Option<String>,
        expr: PVSExpr,
        target_type: PVSType,
    },
    /// Conversion declaration
    Conversion {
        expr: PVSExpr,
        direction: PVSConversionDirection,
    },
    /// Auto-rewrite declaration
    AutoRewrite {
        names: Vec<String>,
        kind: PVSAutoRewriteKind,
    },
    /// TCC (Type Correctness Condition)
    TCC {
        name: String,
        origin: String,
        formula: PVSExpr,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PVSFormulaKind {
    Axiom,
    Assumption,
    Lemma,
    Theorem,
    Corollary,
    Proposition,
    Obligation,
    Challenge,
    Claim,
}

#[derive(Debug, Clone)]
pub struct PVSConstructor {
    pub name: String,
    pub accessors: Vec<(String, PVSType)>,
    pub recogniser: Option<String>,
}

#[derive(Debug, Clone, Copy)]
pub enum PVSJudgementKind {
    HasType,
    Subtype,
}

#[derive(Debug, Clone, Copy)]
pub enum PVSConversionDirection {
    Plus,  // CONVERSION+
    Minus, // CONVERSION-
    Both,  // CONVERSION
}

#[derive(Debug, Clone, Copy)]
pub enum PVSAutoRewriteKind {
    Plus,  // AUTO_REWRITE+
    Minus, // AUTO_REWRITE-
    Both,  // AUTO_REWRITE
}

// ============================================================================
// PVS Tactics (Strategies)
// ============================================================================

/// PVS prover commands (strategies)
#[derive(Debug, Clone)]
pub enum PVSStrategy {
    /// Automatic grinding strategy
    Grind {
        defs: Option<Vec<String>>,
        rewrites: Option<Vec<String>>,
        theories: Option<Vec<String>>,
        exclude: Option<Vec<String>>,
    },
    /// Ground decision procedures
    Ground,
    /// Propositional reasoning
    Prop,
    /// BDD-based simplification
    BddSimp,
    /// Skolemisation
    Skolem(Option<Vec<String>>),
    /// Skolemise and simplify
    SkoSimp,
    /// Instantiate universal formula
    Inst {
        fnum: Option<i32>,
        terms: Vec<PVSExpr>,
    },
    /// Case split
    Case(PVSExpr),
    /// Split conjunctive goals
    Split,
    /// Flatten nested connectives
    Flatten,
    /// Lift if-then-else to top level
    LiftIf,
    /// Induction
    Induct {
        var: String,
        scheme: Option<String>,
    },
    /// Expand definition
    Expand {
        names: Vec<String>,
        fnum: Option<i32>,
    },
    /// Use lemma
    Lemma(String),
    /// Use type predicates
    TypePred {
        exprs: Option<Vec<PVSExpr>>,
    },
    /// Apply rewrite rules
    Rewrite {
        names: Vec<String>,
        fnum: Option<i32>,
        target_fnum: Option<i32>,
    },
    /// Replace equality
    Replace {
        fnum: i32,
        direction: Option<PVSReplaceDirection>,
    },
    /// Assert formula
    Assert,
    /// Simplify
    Simplify,
    /// Beta reduction
    Beta,
    /// Try first succeeding strategy
    Try(Vec<PVSStrategy>),
    /// Apply strategy to all branches
    Branch(Box<PVSStrategy>, Vec<PVSStrategy>),
    /// Repeat strategy
    Repeat(Box<PVSStrategy>),
    /// Sequential composition
    Then(Vec<PVSStrategy>),
    /// Apply to specific formula
    FormulaApply {
        fnum: i32,
        strategy: Box<PVSStrategy>,
    },
    /// Hide formula
    Hide(i32),
    /// Reveal hidden formula
    Reveal(i32),
    /// Copy formula
    Copy(i32),
    /// Name expression
    Name {
        name: String,
        expr: PVSExpr,
    },
    /// Postpone current goal
    Postpone,
    /// Undo last step
    Undo,
    /// Custom strategy
    Custom {
        name: String,
        args: Vec<PVSExpr>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum PVSReplaceDirection {
    LeftToRight,
    RightToLeft,
}

// ============================================================================
// PVS Proof State
// ============================================================================

/// PVS prover session state
#[derive(Debug)]
pub struct PVSSession {
    process: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    current_theory: Option<String>,
    current_formula: Option<String>,
}

/// PVS sequent (proof goal)
#[derive(Debug, Clone)]
pub struct PVSSequent {
    pub antecedents: Vec<PVSLabelledFormula>,
    pub succedents: Vec<PVSLabelledFormula>,
}

/// Labelled formula in sequent
#[derive(Debug, Clone)]
pub struct PVSLabelledFormula {
    pub label: i32,
    pub formula: PVSExpr,
    pub hidden: bool,
}

// ============================================================================
// Parser
// ============================================================================

/// PVS parser for .pvs files
pub struct PVSParser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> PVSParser<'a> {
    pub fn new(input: &'a str) -> Self {
        PVSParser { input, position: 0 }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.position..]
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while self.position < self.input.len() {
                let ch = self.input[self.position..].chars().next().unwrap();
                if ch.is_whitespace() {
                    self.position += ch.len_utf8();
                } else {
                    break;
                }
            }

            // Skip comments (% to end of line)
            if self.remaining().starts_with('%') {
                while self.position < self.input.len() {
                    let ch = self.input[self.position..].chars().next().unwrap();
                    self.position += ch.len_utf8();
                    if ch == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        self.skip_whitespace_and_comments();
        self.remaining().chars().next()
    }

    fn consume_char(&mut self) -> Option<char> {
        self.skip_whitespace_and_comments();
        let ch = self.remaining().chars().next()?;
        self.position += ch.len_utf8();
        Some(ch)
    }

    fn expect_char(&mut self, expected: char) -> Result<()> {
        let ch = self.consume_char()
            .ok_or_else(|| anyhow::anyhow!("Unexpected end of input, expected '{}'", expected))?;
        if ch != expected {
            bail!("Expected '{}', found '{}'", expected, ch);
        }
        Ok(())
    }

    fn try_consume(&mut self, text: &str) -> bool {
        self.skip_whitespace_and_comments();
        if self.remaining().to_uppercase().starts_with(&text.to_uppercase()) {
            // Check it's not part of a longer identifier
            let next_char = self.remaining().chars().nth(text.len());
            if let Some(ch) = next_char {
                if ch.is_alphanumeric() || ch == '_' || ch == '?' {
                    return false;
                }
            }
            self.position += text.len();
            true
        } else {
            false
        }
    }

    fn parse_identifier(&mut self) -> Result<String> {
        self.skip_whitespace_and_comments();
        let start = self.position;

        // First character must be alphabetic or _
        let first = self.remaining().chars().next()
            .ok_or_else(|| anyhow::anyhow!("Expected identifier"))?;

        if !first.is_alphabetic() && first != '_' {
            bail!("Invalid identifier start: '{}'", first);
        }
        self.position += first.len_utf8();

        // Rest can be alphanumeric, _, ?, !
        while let Some(ch) = self.remaining().chars().next() {
            if ch.is_alphanumeric() || ch == '_' || ch == '?' || ch == '!' {
                self.position += ch.len_utf8();
            } else {
                break;
            }
        }

        Ok(self.input[start..self.position].to_string())
    }

    fn parse_number(&mut self) -> Result<i64> {
        self.skip_whitespace_and_comments();
        let start = self.position;
        let negative = self.try_consume("-");

        while let Some(ch) = self.remaining().chars().next() {
            if ch.is_ascii_digit() {
                self.position += 1;
            } else {
                break;
            }
        }

        if self.position == start || (negative && self.position == start + 1) {
            bail!("Expected number");
        }

        let num_str = &self.input[start..self.position];
        num_str.parse().context("Invalid number")
    }

    fn parse_string_literal(&mut self) -> Result<String> {
        self.expect_char('"')?;
        let mut result = String::new();

        loop {
            let ch = self.input[self.position..].chars().next()
                .ok_or_else(|| anyhow::anyhow!("Unterminated string"))?;
            self.position += ch.len_utf8();

            if ch == '"' {
                break;
            } else if ch == '\\' {
                let escaped = self.input[self.position..].chars().next()
                    .ok_or_else(|| anyhow::anyhow!("Unterminated escape"))?;
                self.position += escaped.len_utf8();
                result.push(match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '"' => '"',
                    '\\' => '\\',
                    _ => escaped,
                });
            } else {
                result.push(ch);
            }
        }

        Ok(result)
    }

    /// Parse a PVS expression
    pub fn parse_expr(&mut self) -> Result<PVSExpr> {
        self.parse_implies_expr()
    }

    fn parse_implies_expr(&mut self) -> Result<PVSExpr> {
        let mut expr = self.parse_or_expr()?;

        while self.try_consume("=>") || self.try_consume("IMPLIES") {
            let right = self.parse_or_expr()?;
            expr = PVSExpr::Application {
                function: Box::new(PVSExpr::Name("IMPLIES".to_string())),
                arguments: vec![expr, right],
            };
        }

        if self.try_consume("<=>") || self.try_consume("IFF") {
            let right = self.parse_implies_expr()?;
            expr = PVSExpr::Application {
                function: Box::new(PVSExpr::Name("IFF".to_string())),
                arguments: vec![expr, right],
            };
        }

        Ok(expr)
    }

    fn parse_or_expr(&mut self) -> Result<PVSExpr> {
        let mut expr = self.parse_and_expr()?;

        while self.try_consume("OR") || self.try_consume("\\/") {
            let right = self.parse_and_expr()?;
            expr = PVSExpr::Application {
                function: Box::new(PVSExpr::Name("OR".to_string())),
                arguments: vec![expr, right],
            };
        }

        Ok(expr)
    }

    fn parse_and_expr(&mut self) -> Result<PVSExpr> {
        let mut expr = self.parse_not_expr()?;

        while self.try_consume("AND") || self.try_consume("&") || self.try_consume("/\\") {
            let right = self.parse_not_expr()?;
            expr = PVSExpr::Application {
                function: Box::new(PVSExpr::Name("AND".to_string())),
                arguments: vec![expr, right],
            };
        }

        Ok(expr)
    }

    fn parse_not_expr(&mut self) -> Result<PVSExpr> {
        if self.try_consume("NOT") || self.try_consume("~") {
            let expr = self.parse_not_expr()?;
            Ok(PVSExpr::Application {
                function: Box::new(PVSExpr::Name("NOT".to_string())),
                arguments: vec![expr],
            })
        } else {
            self.parse_relational_expr()
        }
    }

    fn parse_relational_expr(&mut self) -> Result<PVSExpr> {
        let left = self.parse_additive_expr()?;

        let op = if self.try_consume("<=") {
            Some("<=")
        } else if self.try_consume(">=") {
            Some(">=")
        } else if self.try_consume("/=") {
            Some("/=")
        } else if self.try_consume("=") {
            Some("=")
        } else if self.try_consume("<") {
            Some("<")
        } else if self.try_consume(">") {
            Some(">")
        } else {
            None
        };

        if let Some(operator) = op {
            let right = self.parse_additive_expr()?;
            Ok(PVSExpr::Application {
                function: Box::new(PVSExpr::Name(operator.to_string())),
                arguments: vec![left, right],
            })
        } else {
            Ok(left)
        }
    }

    fn parse_additive_expr(&mut self) -> Result<PVSExpr> {
        let mut expr = self.parse_multiplicative_expr()?;

        loop {
            let op = if self.try_consume("+") {
                Some("+")
            } else if self.try_consume("-") {
                Some("-")
            } else {
                None
            };

            if let Some(operator) = op {
                let right = self.parse_multiplicative_expr()?;
                expr = PVSExpr::Application {
                    function: Box::new(PVSExpr::Name(operator.to_string())),
                    arguments: vec![expr, right],
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_multiplicative_expr(&mut self) -> Result<PVSExpr> {
        let mut expr = self.parse_unary_expr()?;

        loop {
            let op = if self.try_consume("*") {
                Some("*")
            } else if self.try_consume("/") {
                Some("/")
            } else {
                None
            };

            if let Some(operator) = op {
                let right = self.parse_unary_expr()?;
                expr = PVSExpr::Application {
                    function: Box::new(PVSExpr::Name(operator.to_string())),
                    arguments: vec![expr, right],
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<PVSExpr> {
        if self.try_consume("-") {
            let expr = self.parse_primary_expr()?;
            Ok(PVSExpr::Application {
                function: Box::new(PVSExpr::Name("-".to_string())),
                arguments: vec![expr],
            })
        } else {
            self.parse_primary_expr()
        }
    }

    fn parse_primary_expr(&mut self) -> Result<PVSExpr> {
        self.skip_whitespace_and_comments();

        // Quantifiers
        if self.try_consume("FORALL") {
            let bindings = self.parse_bindings()?;
            self.expect_char(':')?;
            let body = self.parse_expr()?;
            return Ok(PVSExpr::Forall {
                bindings,
                body: Box::new(body),
            });
        }

        if self.try_consume("EXISTS") {
            let bindings = self.parse_bindings()?;
            self.expect_char(':')?;
            let body = self.parse_expr()?;
            return Ok(PVSExpr::Exists {
                bindings,
                body: Box::new(body),
            });
        }

        // Lambda
        if self.try_consume("LAMBDA") {
            let bindings = self.parse_bindings()?;
            self.expect_char(':')?;
            let body = self.parse_expr()?;
            return Ok(PVSExpr::Lambda {
                bindings,
                body: Box::new(body),
            });
        }

        // IF-THEN-ELSE
        if self.try_consume("IF") {
            let condition = self.parse_expr()?;
            if !self.try_consume("THEN") {
                bail!("Expected THEN");
            }
            let then_branch = self.parse_expr()?;
            if !self.try_consume("ELSE") {
                bail!("Expected ELSE");
            }
            let else_branch = self.parse_expr()?;
            if !self.try_consume("ENDIF") {
                bail!("Expected ENDIF");
            }
            return Ok(PVSExpr::IfThenElse {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            });
        }

        // LET
        if self.try_consume("LET") {
            let mut bindings = Vec::new();
            loop {
                let name = self.parse_identifier()?;
                self.expect_char('=')?;
                let value = self.parse_expr()?;
                bindings.push((name, value));

                if !self.try_consume(",") {
                    break;
                }
            }
            if !self.try_consume("IN") {
                bail!("Expected IN");
            }
            let body = self.parse_expr()?;
            return Ok(PVSExpr::Let {
                bindings,
                body: Box::new(body),
            });
        }

        // TRUE/FALSE
        if self.try_consume("TRUE") {
            return Ok(PVSExpr::Name("TRUE".to_string()));
        }
        if self.try_consume("FALSE") {
            return Ok(PVSExpr::Name("FALSE".to_string()));
        }

        // Parenthesised expression or tuple
        if self.peek_char() == Some('(') {
            self.consume_char();

            // Check for record: (# ... #)
            if self.try_consume("#") {
                let fields = self.parse_record_fields()?;
                self.expect_char('#')?;
                self.expect_char(')')?;
                return Ok(PVSExpr::Record(fields));
            }

            let first = self.parse_expr()?;

            if self.try_consume(",") {
                // Tuple
                let mut elements = vec![first];
                loop {
                    elements.push(self.parse_expr()?);
                    if !self.try_consume(",") {
                        break;
                    }
                }
                self.expect_char(')')?;
                return Ok(PVSExpr::Tuple(elements));
            }

            self.expect_char(')')?;
            return Ok(first);
        }

        // Set enumeration or comprehension
        if self.peek_char() == Some('{') {
            self.consume_char();

            // Check for set comprehension: {x: T | P}
            let first = self.parse_expr()?;

            if self.try_consume(":") {
                // Set comprehension
                let var_type = self.parse_type()?;
                self.expect_char('|')?;
                let predicate = self.parse_expr()?;
                self.expect_char('}')?;

                if let PVSExpr::Name(name) = first {
                    return Ok(PVSExpr::SetComprehension {
                        binding: PVSBinding { name, var_type: Box::new(var_type) },
                        predicate: Box::new(predicate),
                    });
                } else {
                    bail!("Set comprehension requires variable name");
                }
            }

            // Set enumeration
            let mut elements = vec![first];
            while self.try_consume(",") {
                elements.push(self.parse_expr()?);
            }
            self.expect_char('}')?;
            return Ok(PVSExpr::SetEnumeration(elements));
        }

        // String literal
        if self.peek_char() == Some('"') {
            let s = self.parse_string_literal()?;
            return Ok(PVSExpr::StringLit(s));
        }

        // Number
        if self.peek_char().map(|c| c.is_ascii_digit() || c == '-').unwrap_or(false) {
            let num = self.parse_number()?;

            // Check for rational
            if self.try_consume("/") {
                let denom = self.parse_number()?;
                return Ok(PVSExpr::Rational(num, denom));
            }

            return Ok(PVSExpr::Number(num));
        }

        // Identifier (with possible application, projection, or field access)
        let name = self.parse_identifier()?;
        let mut expr = PVSExpr::Name(name);

        // Handle postfix operations
        loop {
            self.skip_whitespace_and_comments();

            // Function application
            if self.peek_char() == Some('(') {
                self.consume_char();
                let mut args = Vec::new();

                if self.peek_char() != Some(')') {
                    loop {
                        args.push(self.parse_expr()?);
                        if !self.try_consume(",") {
                            break;
                        }
                    }
                }

                self.expect_char(')')?;
                expr = PVSExpr::Application {
                    function: Box::new(expr),
                    arguments: args,
                };
            }
            // Field access or projection
            else if self.try_consume("`") {
                self.skip_whitespace_and_comments();

                // Check for number (projection)
                if self.peek_char().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                    let index = self.parse_number()? as usize;
                    expr = PVSExpr::Projection {
                        tuple: Box::new(expr),
                        index,
                    };
                } else {
                    // Field access
                    let field = self.parse_identifier()?;
                    expr = PVSExpr::RecordAccess {
                        record: Box::new(expr),
                        field,
                    };
                }
            }
            // WITH update
            else if self.try_consume("WITH") {
                self.expect_char('[')?;
                let mut assignments = Vec::new();

                loop {
                    // Parse indices
                    let mut indices = Vec::new();
                    if self.peek_char() == Some('(') {
                        self.consume_char();
                        loop {
                            indices.push(self.parse_expr()?);
                            if !self.try_consume(",") {
                                break;
                            }
                        }
                        self.expect_char(')')?;
                    } else {
                        indices.push(self.parse_expr()?);
                    }

                    self.expect_char(':')?;
                    self.expect_char('=')?;
                    let value = self.parse_expr()?;
                    assignments.push((indices, value));

                    if !self.try_consume(",") {
                        break;
                    }
                }

                self.expect_char(']')?;
                expr = PVSExpr::Update {
                    base: Box::new(expr),
                    assignments,
                };
            }
            // Type coercion
            else if self.try_consume("::") {
                let target_type = self.parse_type()?;
                expr = PVSExpr::Coercion {
                    expr: Box::new(expr),
                    target_type: Box::new(target_type),
                };
            }
            else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_bindings(&mut self) -> Result<Vec<PVSBinding>> {
        let mut bindings = Vec::new();

        self.expect_char('(')?;
        loop {
            let name = self.parse_identifier()?;
            self.expect_char(':')?;
            let var_type = self.parse_type()?;
            bindings.push(PVSBinding { name, var_type: Box::new(var_type) });

            if !self.try_consume(",") {
                break;
            }
        }
        self.expect_char(')')?;

        Ok(bindings)
    }

    fn parse_record_fields(&mut self) -> Result<Vec<(String, PVSExpr)>> {
        let mut fields = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some('#') {
                break;
            }

            let name = self.parse_identifier()?;
            self.expect_char(':')?;
            self.expect_char('=')?;
            let value = self.parse_expr()?;
            fields.push((name, value));

            if !self.try_consume(",") {
                break;
            }
        }

        Ok(fields)
    }

    /// Parse a PVS type
    pub fn parse_type(&mut self) -> Result<PVSType> {
        self.parse_function_type()
    }

    fn parse_function_type(&mut self) -> Result<PVSType> {
        // Check for function type [D -> R]
        if self.peek_char() == Some('[') {
            self.consume_char();

            // Check for record type [# ... #]
            if self.try_consume("#") {
                let fields = self.parse_record_type_fields()?;
                self.expect_char('#')?;
                self.expect_char(']')?;
                return Ok(PVSType::Record(fields));
            }

            let first = self.parse_type()?;

            // Function type
            if self.try_consume("->") {
                let range = self.parse_type()?;
                self.expect_char(']')?;
                return Ok(PVSType::Function {
                    domain: Box::new(first),
                    range: Box::new(range),
                });
            }

            // Product type
            if self.try_consume(",") {
                let mut types = vec![first];
                loop {
                    types.push(self.parse_type()?);
                    if !self.try_consume(",") {
                        break;
                    }
                }
                self.expect_char(']')?;
                return Ok(PVSType::Product(types));
            }

            self.expect_char(']')?;
            return Ok(first);
        }

        // Subtype {x: T | P}
        if self.peek_char() == Some('{') {
            self.consume_char();
            let name = self.parse_identifier()?;
            self.expect_char(':')?;
            let base = self.parse_type()?;
            self.expect_char('|')?;
            let predicate = self.parse_expr()?;
            self.expect_char('}')?;

            return Ok(PVSType::Subtype {
                base: Box::new(base),
                predicate: Box::new(predicate),
            });
        }

        self.parse_base_type()
    }

    fn parse_base_type(&mut self) -> Result<PVSType> {
        let name = self.parse_identifier()?;
        let mut base = PVSType::Name(name);

        // Type application
        if self.peek_char() == Some('[') {
            self.consume_char();
            let mut args = Vec::new();
            loop {
                args.push(self.parse_type()?);
                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect_char(']')?;
            base = PVSType::Application {
                base: Box::new(base),
                arguments: args,
            };
        }

        Ok(base)
    }

    fn parse_record_type_fields(&mut self) -> Result<Vec<(String, PVSType)>> {
        let mut fields = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some('#') {
                break;
            }

            let name = self.parse_identifier()?;
            self.expect_char(':')?;
            let field_type = self.parse_type()?;
            fields.push((name, field_type));

            if !self.try_consume(",") {
                break;
            }
        }

        Ok(fields)
    }

    /// Parse a complete PVS theory
    pub fn parse_theory(&mut self) -> Result<PVSTheory> {
        let name = self.parse_identifier()?;

        // Optional parameters
        let mut parameters = Vec::new();
        if self.peek_char() == Some('[') {
            self.consume_char();
            // Parse formal parameters
            while self.peek_char() != Some(']') {
                let param_name = self.parse_identifier()?;
                self.expect_char(':')?;

                let kind = if self.try_consume("TYPE") {
                    PVSParameterKind::Type
                } else {
                    let t = self.parse_type()?;
                    PVSParameterKind::Constant(t)
                };

                parameters.push(PVSFormalParameter { name: param_name, kind });

                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect_char(']')?;
        }

        self.expect_char(':')?;

        if !self.try_consume("THEORY") {
            bail!("Expected THEORY keyword");
        }

        if !self.try_consume("BEGIN") {
            bail!("Expected BEGIN keyword");
        }

        // Parse imports
        let mut importing = Vec::new();
        while self.try_consume("IMPORTING") {
            loop {
                let theory_name = self.parse_identifier()?;
                let mut actuals = Vec::new();

                if self.peek_char() == Some('[') {
                    self.consume_char();
                    while self.peek_char() != Some(']') {
                        actuals.push(self.parse_expr()?);
                        if !self.try_consume(",") {
                            break;
                        }
                    }
                    self.expect_char(']')?;
                }

                importing.push(PVSImporting { theory: theory_name, actuals });

                if !self.try_consume(",") {
                    break;
                }
            }
        }

        // Parse declarations
        let mut declarations = Vec::new();
        let mut assuming = Vec::new();

        while !self.try_consume("END") {
            if let Some(decl) = self.parse_declaration()? {
                declarations.push(decl);
            }
        }

        // Parse theory name at end
        let end_name = self.parse_identifier()?;
        if end_name != name {
            bail!("Theory end name '{}' doesn't match '{}'", end_name, name);
        }

        Ok(PVSTheory {
            name,
            parameters,
            assuming,
            declarations,
            importing,
        })
    }

    fn parse_declaration(&mut self) -> Result<Option<PVSDeclaration>> {
        self.skip_whitespace_and_comments();

        // Check for END
        if self.remaining().to_uppercase().starts_with("END") {
            return Ok(None);
        }

        let name = self.parse_identifier()?;
        self.expect_char(':')?;

        // Type declaration
        if self.try_consume("TYPE") {
            let definition = if self.try_consume("=") {
                Some(self.parse_type()?)
            } else {
                None
            };
            return Ok(Some(PVSDeclaration::TypeDecl { name, definition }));
        }

        // Formula declaration
        let formula_kind = if self.try_consume("AXIOM") {
            Some(PVSFormulaKind::Axiom)
        } else if self.try_consume("LEMMA") {
            Some(PVSFormulaKind::Lemma)
        } else if self.try_consume("THEOREM") {
            Some(PVSFormulaKind::Theorem)
        } else if self.try_consume("COROLLARY") {
            Some(PVSFormulaKind::Corollary)
        } else if self.try_consume("PROPOSITION") {
            Some(PVSFormulaKind::Proposition)
        } else if self.try_consume("ASSUMPTION") {
            Some(PVSFormulaKind::Assumption)
        } else if self.try_consume("OBLIGATION") {
            Some(PVSFormulaKind::Obligation)
        } else {
            None
        };

        if let Some(kind) = formula_kind {
            let formula = self.parse_expr()?;
            return Ok(Some(PVSDeclaration::FormulaDecl { name, kind, formula }));
        }

        // Constant declaration (with optional definition)
        let declared_type = self.parse_type()?;
        let definition = if self.try_consume("=") {
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(Some(PVSDeclaration::ConstDecl {
            name,
            declared_type,
            definition,
        }))
    }

    /// Parse a PVS strategy (tactic)
    pub fn parse_strategy(&mut self) -> Result<PVSStrategy> {
        self.skip_whitespace_and_comments();

        self.expect_char('(')?;
        let name = self.parse_identifier()?;

        let strategy = match name.to_lowercase().as_str() {
            "grind" => {
                let mut defs = None;
                let mut rewrites = None;
                let mut theories = None;
                let mut exclude = None;

                while self.peek_char() != Some(')') {
                    if self.try_consume(":defs") {
                        defs = Some(self.parse_name_list()?);
                    } else if self.try_consume(":rewrites") {
                        rewrites = Some(self.parse_name_list()?);
                    } else if self.try_consume(":theories") {
                        theories = Some(self.parse_name_list()?);
                    } else if self.try_consume(":exclude") {
                        exclude = Some(self.parse_name_list()?);
                    } else {
                        break;
                    }
                }

                PVSStrategy::Grind { defs, rewrites, theories, exclude }
            }
            "ground" => PVSStrategy::Ground,
            "prop" => PVSStrategy::Prop,
            "bddsimp" => PVSStrategy::BddSimp,
            "skolem" | "skolem!" => {
                let constants = if self.peek_char() != Some(')') {
                    Some(self.parse_name_list()?)
                } else {
                    None
                };
                PVSStrategy::Skolem(constants)
            }
            "skosimp" | "skosimp*" => PVSStrategy::SkoSimp,
            "inst" => {
                let fnum = if self.try_consume("-") || self.peek_char().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                    Some(self.parse_fnum()?)
                } else {
                    None
                };
                let terms = self.parse_expr_list()?;
                PVSStrategy::Inst { fnum, terms }
            }
            "case" => {
                let expr = self.parse_expr()?;
                PVSStrategy::Case(expr)
            }
            "split" => PVSStrategy::Split,
            "flatten" => PVSStrategy::Flatten,
            "lift-if" => PVSStrategy::LiftIf,
            "induct" => {
                self.skip_whitespace_and_comments();
                // Variable can be bare identifier or quoted string
                let var = if self.peek_char() == Some('"') {
                    self.parse_string_literal()?
                } else {
                    self.parse_identifier()?
                };
                let scheme = if self.peek_char() != Some(')') {
                    self.skip_whitespace_and_comments();
                    if self.peek_char() == Some('"') {
                        Some(self.parse_string_literal()?)
                    } else {
                        Some(self.parse_identifier()?)
                    }
                } else {
                    None
                };
                PVSStrategy::Induct { var, scheme }
            }
            "expand" => {
                let names = self.parse_name_list()?;
                let fnum = if self.try_consume(":fnum") {
                    Some(self.parse_fnum()?)
                } else {
                    None
                };
                PVSStrategy::Expand { names, fnum }
            }
            "lemma" => {
                let lemma_name = self.parse_identifier()?;
                PVSStrategy::Lemma(lemma_name)
            }
            "typepred" => {
                let exprs = if self.peek_char() != Some(')') {
                    Some(self.parse_expr_list()?)
                } else {
                    None
                };
                PVSStrategy::TypePred { exprs }
            }
            "rewrite" => {
                let names = self.parse_name_list()?;
                PVSStrategy::Rewrite { names, fnum: None, target_fnum: None }
            }
            "replace" => {
                let fnum = self.parse_fnum()?;
                PVSStrategy::Replace { fnum, direction: None }
            }
            "assert" => PVSStrategy::Assert,
            "simplify" => PVSStrategy::Simplify,
            "beta" => PVSStrategy::Beta,
            "try" => {
                let strategies = self.parse_strategy_list()?;
                PVSStrategy::Try(strategies)
            }
            "then" | "spread" => {
                let strategies = self.parse_strategy_list()?;
                PVSStrategy::Then(strategies)
            }
            "repeat" | "repeat*" => {
                let inner = self.parse_strategy()?;
                PVSStrategy::Repeat(Box::new(inner))
            }
            "hide" => {
                let fnum = self.parse_fnum()?;
                PVSStrategy::Hide(fnum)
            }
            "reveal" => {
                let fnum = self.parse_fnum()?;
                PVSStrategy::Reveal(fnum)
            }
            "copy" => {
                let fnum = self.parse_fnum()?;
                PVSStrategy::Copy(fnum)
            }
            "postpone" => PVSStrategy::Postpone,
            "undo" => PVSStrategy::Undo,
            _ => {
                let args = self.parse_expr_list()?;
                PVSStrategy::Custom { name, args }
            }
        };

        self.expect_char(')')?;
        Ok(strategy)
    }

    fn parse_fnum(&mut self) -> Result<i32> {
        let negative = self.try_consume("-");
        let num = self.parse_number()? as i32;
        Ok(if negative { -num } else { num })
    }

    fn parse_name_list(&mut self) -> Result<Vec<String>> {
        let mut names = Vec::new();

        if self.peek_char() == Some('(') {
            self.consume_char();
            while self.peek_char() != Some(')') {
                names.push(self.parse_identifier()?);
                self.try_consume(",");
            }
            self.expect_char(')')?;
        } else if self.peek_char() == Some('"') {
            names.push(self.parse_string_literal()?);
        } else {
            names.push(self.parse_identifier()?);
        }

        Ok(names)
    }

    fn parse_expr_list(&mut self) -> Result<Vec<PVSExpr>> {
        let mut exprs = Vec::new();

        while self.peek_char() != Some(')') {
            exprs.push(self.parse_expr()?);
            self.try_consume(",");
        }

        Ok(exprs)
    }

    fn parse_strategy_list(&mut self) -> Result<Vec<PVSStrategy>> {
        let mut strategies = Vec::new();

        while self.peek_char() != Some(')') {
            strategies.push(self.parse_strategy()?);
        }

        Ok(strategies)
    }
}

// ============================================================================
// PVS Backend Implementation
// ============================================================================

pub struct PVSBackend {
    config: ProverConfig,
    session: Mutex<Option<PVSSession>>,
}

impl PVSBackend {
    pub fn new(config: ProverConfig) -> Self {
        PVSBackend {
            config,
            session: Mutex::new(None),
        }
    }

    /// Start PVS in batch mode
    async fn start_session(&self) -> Result<PVSSession> {
        let pvs_path = self.config.executable.clone();

        let mut process = Command::new(&pvs_path)
            .arg("-batch")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .context("Failed to start PVS")?;

        let stdin = process.stdin.take()
            .ok_or_else(|| anyhow::anyhow!("Failed to get PVS stdin"))?;
        let stdout = process.stdout.take()
            .ok_or_else(|| anyhow::anyhow!("Failed to get PVS stdout"))?;

        Ok(PVSSession {
            process,
            stdin,
            stdout: BufReader::new(stdout),
            current_theory: None,
            current_formula: None,
        })
    }

    /// Send command to PVS and get response
    async fn send_command(session: &mut PVSSession, command: &str) -> Result<String> {
        session.stdin.write_all(command.as_bytes()).await?;
        session.stdin.write_all(b"\n").await?;
        session.stdin.flush().await?;

        let mut response = String::new();
        let mut line = String::new();

        loop {
            line.clear();
            let bytes_read = session.stdout.read_line(&mut line).await?;

            if bytes_read == 0 {
                break;
            }

            response.push_str(&line);

            // Check for PVS prompt or completion markers
            if line.contains("Rule?") || line.contains("pvs>") || line.contains("Q.E.D.") {
                break;
            }
        }

        Ok(response)
    }

    /// Convert PVS expression to universal Term
    fn expr_to_term(expr: &PVSExpr) -> Term {
        match expr {
            PVSExpr::Name(n) => {
                if n == "TRUE" || n == "FALSE" {
                    Term::Const(n.clone())
                } else {
                    Term::Var(n.clone())
                }
            }
            PVSExpr::Number(n) => Term::Const(n.to_string()),
            PVSExpr::Rational(num, denom) => Term::Const(format!("{}/{}", num, denom)),
            PVSExpr::StringLit(s) => Term::Const(format!("\"{}\"", s)),
            PVSExpr::Application { function, arguments } => {
                let func_term = Self::expr_to_term(function);
                let arg_terms: Vec<Term> = arguments.iter()
                    .map(|a| Self::expr_to_term(a))
                    .collect();
                Term::App {
                    func: Box::new(func_term),
                    args: arg_terms,
                }
            }
            PVSExpr::Lambda { bindings, body } => {
                let mut term = Self::expr_to_term(body);
                for binding in bindings.iter().rev() {
                    term = Term::Lambda {
                        param: binding.name.clone(),
                        param_type: Some(Box::new(Term::Const(Self::type_to_string(&binding.var_type)))),
                        body: Box::new(term),
                    };
                }
                term
            }
            PVSExpr::Forall { bindings, body } => {
                // Encode forall as Pi type (dependent function)
                let mut term = Self::expr_to_term(body);
                for binding in bindings.iter().rev() {
                    term = Term::Pi {
                        param: binding.name.clone(),
                        param_type: Box::new(Term::Const(Self::type_to_string(&binding.var_type))),
                        body: Box::new(term),
                    };
                }
                term
            }
            PVSExpr::Exists { bindings, body } => {
                // Encode exists using ProverSpecific
                let body_term = Self::expr_to_term(body);
                let mut term = body_term;
                for binding in bindings.iter().rev() {
                    term = Term::App {
                        func: Box::new(Term::Const("exists".to_string())),
                        args: vec![
                            Term::Const(Self::type_to_string(&binding.var_type)),
                            Term::Lambda {
                                param: binding.name.clone(),
                                param_type: Some(Box::new(Term::Const(Self::type_to_string(&binding.var_type)))),
                                body: Box::new(term),
                            },
                        ],
                    };
                }
                term
            }
            PVSExpr::IfThenElse { condition, then_branch, else_branch } => {
                Term::App {
                    func: Box::new(Term::Const("if_then_else".to_string())),
                    args: vec![
                        Self::expr_to_term(condition),
                        Self::expr_to_term(then_branch),
                        Self::expr_to_term(else_branch),
                    ],
                }
            }
            PVSExpr::Let { bindings, body } => {
                let mut term = Self::expr_to_term(body);
                for (name, value) in bindings.iter().rev() {
                    term = Term::Let {
                        name: name.clone(),
                        ty: None,
                        value: Box::new(Self::expr_to_term(value)),
                        body: Box::new(term),
                    };
                }
                term
            }
            PVSExpr::Tuple(elements) => {
                Term::App {
                    func: Box::new(Term::Const("tuple".to_string())),
                    args: elements.iter().map(|e| Self::expr_to_term(e)).collect(),
                }
            }
            PVSExpr::Record(fields) => {
                let field_terms: Vec<Term> = fields.iter()
                    .flat_map(|(name, value)| {
                        vec![
                            Term::Const(name.clone()),
                            Self::expr_to_term(value),
                        ]
                    })
                    .collect();
                Term::App {
                    func: Box::new(Term::Const("record".to_string())),
                    args: field_terms,
                }
            }
            PVSExpr::RecordAccess { record, field } => {
                Term::App {
                    func: Box::new(Term::Const(format!("field_{}", field))),
                    args: vec![Self::expr_to_term(record)],
                }
            }
            PVSExpr::Projection { tuple, index } => {
                Term::App {
                    func: Box::new(Term::Const(format!("proj_{}", index))),
                    args: vec![Self::expr_to_term(tuple)],
                }
            }
            PVSExpr::Update { base, assignments } => {
                let mut args = vec![Self::expr_to_term(base)];
                for (indices, value) in assignments {
                    for idx in indices {
                        args.push(Self::expr_to_term(idx));
                    }
                    args.push(Self::expr_to_term(value));
                }
                Term::App {
                    func: Box::new(Term::Const("update".to_string())),
                    args,
                }
            }
            PVSExpr::Cases { expr, selections, else_clause } => {
                let mut args = vec![Self::expr_to_term(expr)];
                for selection in selections {
                    args.push(Self::expr_to_term(&selection.expr));
                }
                if let Some(else_expr) = else_clause {
                    args.push(Self::expr_to_term(else_expr));
                }
                Term::App {
                    func: Box::new(Term::Const("cases".to_string())),
                    args,
                }
            }
            PVSExpr::SetEnumeration(elements) => {
                Term::App {
                    func: Box::new(Term::Const("set_enum".to_string())),
                    args: elements.iter().map(|e| Self::expr_to_term(e)).collect(),
                }
            }
            PVSExpr::SetComprehension { binding, predicate } => {
                Term::App {
                    func: Box::new(Term::Const("set_comprehension".to_string())),
                    args: vec![
                        Term::Lambda {
                            param: binding.name.clone(),
                            param_type: Some(Box::new(Term::Const(Self::type_to_string(&binding.var_type)))),
                            body: Box::new(Self::expr_to_term(predicate)),
                        },
                    ],
                }
            }
            PVSExpr::Coercion { expr, .. } => Self::expr_to_term(expr),
        }
    }

    /// Convert PVS type to string representation
    fn type_to_string(t: &PVSType) -> String {
        match t {
            PVSType::Name(n) => n.clone(),
            PVSType::Application { base, arguments } => {
                let base_str = Self::type_to_string(base);
                let args_str: Vec<String> = arguments.iter()
                    .map(|a| Self::type_to_string(a))
                    .collect();
                format!("{}[{}]", base_str, args_str.join(", "))
            }
            PVSType::Function { domain, range } => {
                format!("[{} -> {}]", Self::type_to_string(domain), Self::type_to_string(range))
            }
            PVSType::Product(types) => {
                let type_strs: Vec<String> = types.iter()
                    .map(|t| Self::type_to_string(t))
                    .collect();
                format!("[{}]", type_strs.join(", "))
            }
            PVSType::Record(fields) => {
                let field_strs: Vec<String> = fields.iter()
                    .map(|(n, t)| format!("{}: {}", n, Self::type_to_string(t)))
                    .collect();
                format!("[# {} #]", field_strs.join(", "))
            }
            PVSType::Subtype { base, predicate: _ } => {
                format!("{{x: {} | ...}}", Self::type_to_string(base))
            }
            PVSType::Dependent { binding, range } => {
                format!("[{}: {} -> {}]", binding.name, Self::type_to_string(&binding.var_type), Self::type_to_string(range))
            }
            PVSType::SetOf(elem) => format!("set[{}]", Self::type_to_string(elem)),
            PVSType::Sequence(elem) => format!("sequence[{}]", Self::type_to_string(elem)),
        }
    }

    /// Convert universal Term to PVS expression
    fn term_to_expr(term: &Term) -> PVSExpr {
        match term {
            Term::Var(name) => PVSExpr::Name(name.clone()),
            Term::Const(name) => {
                if let Ok(n) = name.parse::<i64>() {
                    PVSExpr::Number(n)
                } else {
                    PVSExpr::Name(name.clone())
                }
            }
            Term::App { func, args } => {
                PVSExpr::Application {
                    function: Box::new(Self::term_to_expr(func)),
                    arguments: args.iter().map(|a| Self::term_to_expr(a)).collect(),
                }
            }
            Term::Lambda { param, param_type, body } => {
                PVSExpr::Lambda {
                    bindings: vec![PVSBinding {
                        name: param.clone(),
                        var_type: Box::new(param_type.as_ref()
                            .map(|t| Self::term_to_type(t))
                            .unwrap_or(PVSType::Name("T".to_string()))),
                    }],
                    body: Box::new(Self::term_to_expr(body)),
                }
            }
            Term::Pi { param, param_type, body } => {
                // Pi types map to FORALL in PVS
                PVSExpr::Forall {
                    bindings: vec![PVSBinding {
                        name: param.clone(),
                        var_type: Box::new(Self::term_to_type(param_type)),
                    }],
                    body: Box::new(Self::term_to_expr(body)),
                }
            }
            Term::Let { name, value, body, .. } => {
                PVSExpr::Let {
                    bindings: vec![(name.clone(), Self::term_to_expr(value))],
                    body: Box::new(Self::term_to_expr(body)),
                }
            }
            Term::Match { scrutinee, branches, .. } => {
                let selections: Vec<PVSCaseSelection> = branches.iter()
                    .map(|(pat, expr)| PVSCaseSelection {
                        pattern: Self::pattern_to_pvs(pat),
                        expr: Self::term_to_expr(expr),
                    })
                    .collect();
                PVSExpr::Cases {
                    expr: Box::new(Self::term_to_expr(scrutinee)),
                    selections,
                    else_clause: None,
                }
            }
            Term::Hole(name) => {
                PVSExpr::Name(if name.is_empty() { "_".to_string() } else { name.clone() })
            }
            Term::Type(level) => PVSExpr::Name(format!("TYPE_{}", level)),
            Term::Sort(level) => PVSExpr::Name(format!("SORT_{}", level)),
            Term::Universe(level) => PVSExpr::Name(format!("TYPE_{}", level)),
            Term::Fix { name, body, .. } => {
                // Encode fix point as a recursive definition
                PVSExpr::Application {
                    function: Box::new(PVSExpr::Name("fix".to_string())),
                    arguments: vec![
                        PVSExpr::Lambda {
                            bindings: vec![PVSBinding {
                                name: name.clone(),
                                var_type: Box::new(PVSType::Name("T".to_string())),
                            }],
                            body: Box::new(Self::term_to_expr(body)),
                        },
                    ],
                }
            }
            Term::Meta(id) => PVSExpr::Name(format!("?{}", id)),
            Term::ProverSpecific { data, .. } => {
                // Try to extract a meaningful representation
                PVSExpr::Name(data.to_string())
            }
        }
    }

    /// Convert Term to PVSType (for type annotations)
    fn term_to_type(term: &Term) -> PVSType {
        match term {
            Term::Var(name) | Term::Const(name) => PVSType::Name(name.clone()),
            Term::App { func, args } => {
                PVSType::Application {
                    base: Box::new(Self::term_to_type(func)),
                    arguments: args.iter().map(|a| Self::term_to_type(a)).collect(),
                }
            }
            Term::Pi { param, param_type, body } => {
                PVSType::Dependent {
                    binding: PVSBinding {
                        name: param.clone(),
                        var_type: Box::new(Self::term_to_type(param_type)),
                    },
                    range: Box::new(Self::term_to_type(body)),
                }
            }
            _ => PVSType::Name("T".to_string()),
        }
    }

    /// Convert Pattern to PVS pattern
    fn pattern_to_pvs(pat: &crate::core::Pattern) -> PVSPattern {
        match pat {
            crate::core::Pattern::Wildcard => PVSPattern::Wildcard,
            crate::core::Pattern::Var(name) => PVSPattern::Variable(name.clone()),
            crate::core::Pattern::Constructor { name, args } => {
                if args.is_empty() {
                    PVSPattern::Literal(PVSExpr::Name(name.clone()))
                } else {
                    PVSPattern::Constructor {
                        name: name.clone(),
                        args: args.iter().map(|p| Self::pattern_to_string(p)).collect(),
                    }
                }
            }
        }
    }

    /// Extract string name from a pattern (for PVS constructor arguments)
    fn pattern_to_string(pat: &crate::core::Pattern) -> String {
        match pat {
            crate::core::Pattern::Wildcard => "_".to_string(),
            crate::core::Pattern::Var(name) => name.clone(),
            crate::core::Pattern::Constructor { name, .. } => name.clone(),
        }
    }

    /// Convert universal Tactic to PVS strategy
    fn tactic_to_strategy(tactic: &Tactic) -> PVSStrategy {
        match tactic {
            Tactic::Apply(name) => PVSStrategy::Lemma(name.clone()),
            Tactic::Intro(_) => PVSStrategy::SkoSimp,
            Tactic::Cases(term) => PVSStrategy::Case(Self::term_to_expr(term)),
            Tactic::Induction(term) => {
                // Extract variable name from term if possible
                let var = match term {
                    Term::Var(v) => v.clone(),
                    _ => "x".to_string(),
                };
                PVSStrategy::Induct { var, scheme: None }
            }
            Tactic::Rewrite(lemma) => PVSStrategy::Rewrite {
                names: vec![lemma.clone()],
                fnum: None,
                target_fnum: None,
            },
            Tactic::Simplify => PVSStrategy::Simplify,
            Tactic::Reflexivity => PVSStrategy::Assert,
            Tactic::Assumption => PVSStrategy::Assert,
            Tactic::Exact(term) => PVSStrategy::Custom {
                name: "claim".to_string(),
                args: vec![Self::term_to_expr(term)],
            },
            Tactic::Custom { prover, command, args } => {
                // If the custom tactic is for PVS or generic, use it
                if prover == "PVS" || prover == "pvs" || prover.is_empty() {
                    // Try to parse command as a known strategy
                    match command.as_str() {
                        "grind" => PVSStrategy::Grind {
                            defs: None,
                            rewrites: None,
                            theories: None,
                            exclude: None,
                        },
                        "ground" => PVSStrategy::Ground,
                        "prop" => PVSStrategy::Prop,
                        "split" => PVSStrategy::Split,
                        "flatten" => PVSStrategy::Flatten,
                        "skosimp" | "skolem" => PVSStrategy::SkoSimp,
                        _ => PVSStrategy::Custom {
                            name: command.clone(),
                            args: args.iter().map(|a| PVSExpr::Name(a.clone())).collect(),
                        },
                    }
                } else {
                    // Fallback to grind for non-PVS tactics
                    PVSStrategy::Grind {
                        defs: None,
                        rewrites: None,
                        theories: None,
                        exclude: None,
                    }
                }
            }
        }
    }

    /// Convert PVS strategy to universal Tactic
    fn strategy_to_tactic(strategy: &PVSStrategy) -> Tactic {
        match strategy {
            PVSStrategy::Grind { .. } => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "grind".to_string(),
                args: vec![],
            },
            PVSStrategy::Ground => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "ground".to_string(),
                args: vec![],
            },
            PVSStrategy::Prop => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "prop".to_string(),
                args: vec![],
            },
            PVSStrategy::BddSimp => Tactic::Simplify,
            PVSStrategy::Skolem(_) | PVSStrategy::SkoSimp => Tactic::Intro(None),
            PVSStrategy::Inst { terms, .. } => {
                if let Some(first) = terms.first() {
                    Tactic::Exact(Self::expr_to_term(first))
                } else {
                    Tactic::Custom {
                        prover: "PVS".to_string(),
                        command: "inst".to_string(),
                        args: vec![],
                    }
                }
            }
            PVSStrategy::Case(expr) => Tactic::Cases(Self::expr_to_term(expr)),
            PVSStrategy::Split => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "split".to_string(),
                args: vec![],
            },
            PVSStrategy::Flatten => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "flatten".to_string(),
                args: vec![],
            },
            PVSStrategy::Induct { var, .. } => Tactic::Induction(Term::Var(var.clone())),
            PVSStrategy::Expand { names, .. } => {
                if let Some(name) = names.first() {
                    Tactic::Custom {
                        prover: "PVS".to_string(),
                        command: "expand".to_string(),
                        args: vec![name.clone()],
                    }
                } else {
                    Tactic::Simplify
                }
            }
            PVSStrategy::Lemma(name) => Tactic::Apply(name.clone()),
            PVSStrategy::Rewrite { names, .. } => {
                if let Some(name) = names.first() {
                    Tactic::Rewrite(name.clone())
                } else {
                    Tactic::Simplify
                }
            }
            PVSStrategy::Assert | PVSStrategy::Simplify => Tactic::Simplify,
            PVSStrategy::Beta => Tactic::Simplify,
            PVSStrategy::Custom { name, args } => Tactic::Custom {
                prover: "PVS".to_string(),
                command: name.clone(),
                args: args.iter().map(|a| Self::format_expr(a)).collect(),
            },
            _ => Tactic::Custom {
                prover: "PVS".to_string(),
                command: "pvs_strategy".to_string(),
                args: vec![],
            },
        }
    }

    /// Format PVS expression as string
    fn format_expr(expr: &PVSExpr) -> String {
        match expr {
            PVSExpr::Name(n) => n.clone(),
            PVSExpr::Number(n) => n.to_string(),
            PVSExpr::Rational(num, denom) => format!("{}/{}", num, denom),
            PVSExpr::StringLit(s) => format!("\"{}\"", s),
            PVSExpr::Application { function, arguments } => {
                let func = Self::format_expr(function);
                if arguments.is_empty() {
                    func
                } else {
                    let args: Vec<String> = arguments.iter()
                        .map(|a| Self::format_expr(a))
                        .collect();
                    format!("{}({})", func, args.join(", "))
                }
            }
            PVSExpr::Lambda { bindings, body } => {
                let params: Vec<String> = bindings.iter()
                    .map(|b| format!("{}: {}", b.name, Self::type_to_string(&b.var_type)))
                    .collect();
                format!("LAMBDA ({}): {}", params.join(", "), Self::format_expr(body))
            }
            PVSExpr::Forall { bindings, body } => {
                let params: Vec<String> = bindings.iter()
                    .map(|b| format!("{}: {}", b.name, Self::type_to_string(&b.var_type)))
                    .collect();
                format!("FORALL ({}): {}", params.join(", "), Self::format_expr(body))
            }
            PVSExpr::Exists { bindings, body } => {
                let params: Vec<String> = bindings.iter()
                    .map(|b| format!("{}: {}", b.name, Self::type_to_string(&b.var_type)))
                    .collect();
                format!("EXISTS ({}): {}", params.join(", "), Self::format_expr(body))
            }
            PVSExpr::IfThenElse { condition, then_branch, else_branch } => {
                format!("IF {} THEN {} ELSE {} ENDIF",
                    Self::format_expr(condition),
                    Self::format_expr(then_branch),
                    Self::format_expr(else_branch))
            }
            PVSExpr::Let { bindings, body } => {
                let lets: Vec<String> = bindings.iter()
                    .map(|(n, v)| format!("{} = {}", n, Self::format_expr(v)))
                    .collect();
                format!("LET {} IN {}", lets.join(", "), Self::format_expr(body))
            }
            PVSExpr::Tuple(elements) => {
                let elems: Vec<String> = elements.iter()
                    .map(|e| Self::format_expr(e))
                    .collect();
                format!("({})", elems.join(", "))
            }
            PVSExpr::Record(fields) => {
                let field_strs: Vec<String> = fields.iter()
                    .map(|(n, v)| format!("{} := {}", n, Self::format_expr(v)))
                    .collect();
                format!("(# {} #)", field_strs.join(", "))
            }
            PVSExpr::RecordAccess { record, field } => {
                format!("{}`{}", Self::format_expr(record), field)
            }
            PVSExpr::Projection { tuple, index } => {
                format!("{}`{}", Self::format_expr(tuple), index)
            }
            PVSExpr::Update { base, assignments } => {
                let updates: Vec<String> = assignments.iter()
                    .map(|(indices, value)| {
                        let idx_str: Vec<String> = indices.iter()
                            .map(|i| Self::format_expr(i))
                            .collect();
                        format!("({}) := {}", idx_str.join(", "), Self::format_expr(value))
                    })
                    .collect();
                format!("{} WITH [{}]", Self::format_expr(base), updates.join(", "))
            }
            PVSExpr::SetEnumeration(elements) => {
                let elems: Vec<String> = elements.iter()
                    .map(|e| Self::format_expr(e))
                    .collect();
                format!("{{{}}}", elems.join(", "))
            }
            PVSExpr::SetComprehension { binding, predicate } => {
                format!("{{{}: {} | {}}}",
                    binding.name,
                    Self::type_to_string(&binding.var_type),
                    Self::format_expr(predicate))
            }
            PVSExpr::Coercion { expr, target_type } => {
                format!("{} :: {}", Self::format_expr(expr), Self::type_to_string(target_type))
            }
            PVSExpr::Cases { expr, selections, else_clause } => {
                let mut result = format!("CASES {} OF\n", Self::format_expr(expr));
                for sel in selections {
                    result.push_str(&format!("  {} : {},\n",
                        match &sel.pattern {
                            PVSPattern::Wildcard => "_".to_string(),
                            PVSPattern::Variable(name) => name.clone(),
                            PVSPattern::Constructor { name, args } => {
                                if args.is_empty() {
                                    name.clone()
                                } else {
                                    format!("{}({})", name, args.join(", "))
                                }
                            }
                            PVSPattern::Literal(e) => Self::format_expr(e),
                        },
                        Self::format_expr(&sel.expr)));
                }
                if let Some(else_expr) = else_clause {
                    result.push_str(&format!("  ELSE {}\n", Self::format_expr(else_expr)));
                }
                result.push_str("ENDCASES");
                result
            }
        }
    }

    /// Format PVS strategy as string
    fn format_strategy(strategy: &PVSStrategy) -> String {
        match strategy {
            PVSStrategy::Grind { defs, rewrites, theories, exclude } => {
                let mut parts = vec!["grind".to_string()];
                if let Some(d) = defs {
                    parts.push(format!(":defs ({})", d.join(" ")));
                }
                if let Some(r) = rewrites {
                    parts.push(format!(":rewrites ({})", r.join(" ")));
                }
                if let Some(t) = theories {
                    parts.push(format!(":theories ({})", t.join(" ")));
                }
                if let Some(e) = exclude {
                    parts.push(format!(":exclude ({})", e.join(" ")));
                }
                format!("({})", parts.join(" "))
            }
            PVSStrategy::Ground => "(ground)".to_string(),
            PVSStrategy::Prop => "(prop)".to_string(),
            PVSStrategy::BddSimp => "(bddsimp)".to_string(),
            PVSStrategy::Skolem(names) => {
                if let Some(ns) = names {
                    format!("(skolem ({}))", ns.join(" "))
                } else {
                    "(skolem!)".to_string()
                }
            }
            PVSStrategy::SkoSimp => "(skosimp*)".to_string(),
            PVSStrategy::Inst { fnum, terms } => {
                let term_strs: Vec<String> = terms.iter()
                    .map(|t| format!("\"{}\"", Self::format_expr(t)))
                    .collect();
                if let Some(f) = fnum {
                    format!("(inst {} {})", f, term_strs.join(" "))
                } else {
                    format!("(inst {})", term_strs.join(" "))
                }
            }
            PVSStrategy::Case(expr) => {
                format!("(case \"{}\")", Self::format_expr(expr))
            }
            PVSStrategy::Split => "(split)".to_string(),
            PVSStrategy::Flatten => "(flatten)".to_string(),
            PVSStrategy::LiftIf => "(lift-if)".to_string(),
            PVSStrategy::Induct { var, scheme } => {
                if let Some(s) = scheme {
                    format!("(induct \"{}\" \"{}\")", var, s)
                } else {
                    format!("(induct \"{}\")", var)
                }
            }
            PVSStrategy::Expand { names, fnum } => {
                let name_str = names.iter()
                    .map(|n| format!("\"{}\"", n))
                    .collect::<Vec<_>>()
                    .join(" ");
                if let Some(f) = fnum {
                    format!("(expand {} :fnum {})", name_str, f)
                } else {
                    format!("(expand {})", name_str)
                }
            }
            PVSStrategy::Lemma(name) => format!("(lemma \"{}\")", name),
            PVSStrategy::TypePred { exprs } => {
                if let Some(es) = exprs {
                    let expr_strs: Vec<String> = es.iter()
                        .map(|e| format!("\"{}\"", Self::format_expr(e)))
                        .collect();
                    format!("(typepred {})", expr_strs.join(" "))
                } else {
                    "(typepred)".to_string()
                }
            }
            PVSStrategy::Rewrite { names, fnum, target_fnum } => {
                let name_str = names.iter()
                    .map(|n| format!("\"{}\"", n))
                    .collect::<Vec<_>>()
                    .join(" ");
                let mut result = format!("(rewrite {})", name_str);
                if let Some(f) = fnum {
                    result = format!("(rewrite {} :fnum {})", name_str, f);
                }
                if let Some(tf) = target_fnum {
                    result = format!("(rewrite {} :target-fnum {})", name_str, tf);
                }
                result
            }
            PVSStrategy::Replace { fnum, direction } => {
                match direction {
                    Some(PVSReplaceDirection::RightToLeft) => format!("(replace {} rl)", fnum),
                    _ => format!("(replace {})", fnum),
                }
            }
            PVSStrategy::Assert => "(assert)".to_string(),
            PVSStrategy::Simplify => "(simplify)".to_string(),
            PVSStrategy::Beta => "(beta)".to_string(),
            PVSStrategy::Try(strategies) => {
                let strs: Vec<String> = strategies.iter()
                    .map(|s| Self::format_strategy(s))
                    .collect();
                format!("(try {})", strs.join(" "))
            }
            PVSStrategy::Branch(main, branches) => {
                let branch_strs: Vec<String> = branches.iter()
                    .map(|s| Self::format_strategy(s))
                    .collect();
                format!("(branch {} ({}))", Self::format_strategy(main), branch_strs.join(" "))
            }
            PVSStrategy::Then(strategies) => {
                let strs: Vec<String> = strategies.iter()
                    .map(|s| Self::format_strategy(s))
                    .collect();
                format!("(then {})", strs.join(" "))
            }
            PVSStrategy::Repeat(inner) => {
                format!("(repeat {})", Self::format_strategy(inner))
            }
            PVSStrategy::FormulaApply { fnum, strategy } => {
                format!("({} {})", fnum, Self::format_strategy(strategy))
            }
            PVSStrategy::Hide(fnum) => format!("(hide {})", fnum),
            PVSStrategy::Reveal(fnum) => format!("(reveal {})", fnum),
            PVSStrategy::Copy(fnum) => format!("(copy {})", fnum),
            PVSStrategy::Name { name, expr } => {
                format!("(name \"{}\" \"{}\")", name, Self::format_expr(expr))
            }
            PVSStrategy::Postpone => "(postpone)".to_string(),
            PVSStrategy::Undo => "(undo)".to_string(),
            PVSStrategy::Custom { name, args } => {
                if args.is_empty() {
                    format!("({})", name)
                } else {
                    let arg_strs: Vec<String> = args.iter()
                        .map(|a| Self::format_expr(a))
                        .collect();
                    format!("({} {})", name, arg_strs.join(" "))
                }
            }
        }
    }
}

#[async_trait]
impl ProverBackend for PVSBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::PVS
    }

    async fn version(&self) -> Result<String> {
        let pvs_path = self.config.executable.clone();

        let output = Command::new(&pvs_path)
            .arg("-version")
            .output()
            .await
            .context("Failed to get PVS version")?;

        let version_output = String::from_utf8_lossy(&output.stdout);

        // Extract version from output
        if let Some(line) = version_output.lines().next() {
            Ok(line.to_string())
        } else {
            Ok("PVS (unknown version)".to_string())
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read PVS file")?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut parser = PVSParser::new(content);
        let theory = parser.parse_theory()
            .context("Failed to parse PVS theory")?;

        let mut goals = Vec::new();
        let mut hypotheses = Vec::new();

        for decl in &theory.declarations {
            match decl {
                PVSDeclaration::FormulaDecl { name, kind, formula } => {
                    match kind {
                        PVSFormulaKind::Axiom | PVSFormulaKind::Assumption => {
                            hypotheses.push(Hypothesis {
                                name: name.clone(),
                                ty: Self::expr_to_term(formula),
                                body: None,
                            });
                        }
                        PVSFormulaKind::Lemma | PVSFormulaKind::Theorem |
                        PVSFormulaKind::Corollary | PVSFormulaKind::Proposition |
                        PVSFormulaKind::Obligation | PVSFormulaKind::Challenge |
                        PVSFormulaKind::Claim => {
                            goals.push(Goal {
                                id: name.clone(),
                                target: Self::expr_to_term(formula),
                                hypotheses: hypotheses.clone(),
                            });
                        }
                    }
                }
                PVSDeclaration::ConstDecl { name, declared_type, definition } => {
                    if let Some(def) = definition {
                        let def_term = Term::App {
                            func: Box::new(Term::Const("=".to_string())),
                            args: vec![
                                Term::Var(name.clone()),
                                Self::expr_to_term(def),
                            ],
                        };
                        hypotheses.push(Hypothesis {
                            name: format!("{}_def", name),
                            ty: def_term,
                            body: Some(Self::expr_to_term(def)),
                        });
                    }
                }
                PVSDeclaration::TCC { name, formula, .. } => {
                    goals.push(Goal {
                        id: name.clone(),
                        target: Self::expr_to_term(formula),
                        hypotheses: hypotheses.clone(),
                    });
                }
                _ => {}
            }
        }

        Ok(ProofState {
            goals,
            context: CoreContext::default(),
            proof_script: vec![],
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("theory".to_string(), serde_json::Value::String(theory.name.clone()));
                meta.insert("prover".to_string(), serde_json::Value::String("PVS".to_string()));
                meta
            },
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        let strategy = Self::tactic_to_strategy(tactic);
        let strategy_str = Self::format_strategy(&strategy);

        let mut session_guard = self.session.lock().await;

        let session = if session_guard.is_some() {
            session_guard.as_mut().unwrap()
        } else {
            *session_guard = Some(self.start_session().await?);
            session_guard.as_mut().unwrap()
        };

        let response = Self::send_command(session, &strategy_str).await?;

        // Parse response to determine success
        let success = response.contains("Q.E.D.") ||
                      response.contains("proved") ||
                      !response.contains("No change");

        if success {
            let mut new_state = state.clone();
            new_state.proof_script.push(tactic.clone());

            if response.contains("Q.E.D.") {
                new_state.goals.clear();
                return Ok(TacticResult::QED);
            }

            Ok(TacticResult::Success(new_state))
        } else {
            Ok(TacticResult::Error(response))
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        Ok(state.goals.is_empty())
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let theory_name = state.metadata.get("theory")
            .and_then(|v| v.as_str())
            .unwrap_or("exported")
            .to_string();

        let mut output = String::new();
        output.push_str(&format!("{}: THEORY\nBEGIN\n\n", theory_name));

        // Export hypotheses as axioms
        for goal in state.goals.iter() {
            for hyp in &goal.hypotheses {
                let expr = Self::term_to_expr(&hyp.ty);
                output.push_str(&format!("  {}: AXIOM {}\n\n", hyp.name, Self::format_expr(&expr)));
            }

            // Export goal as lemma/theorem
            let expr = Self::term_to_expr(&goal.target);
            output.push_str(&format!("  {}: LEMMA {}\n\n", goal.id, Self::format_expr(&expr)));
        }

        // Export proof if tactics were applied
        if !state.proof_script.is_empty() {
            output.push_str("% Proof:\n");
            for tactic in &state.proof_script {
                let strategy = Self::tactic_to_strategy(tactic);
                output.push_str(&format!("%   {}\n", Self::format_strategy(&strategy)));
            }
        }

        output.push_str(&format!("\nEND {}\n", theory_name));

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        if let Some(goal) = state.goals.first() {
            let goal_str = format!("{:?}", goal.target);

            // Analyse goal structure for suggestions
            if goal_str.contains("Forall") || goal_str.contains("FORALL") || goal_str.contains("Pi") {
                suggestions.push(Tactic::Intro(None));
            }

            if goal_str.contains("AND") || goal_str.contains("/\\") {
                suggestions.push(Tactic::Custom {
                    prover: "PVS".to_string(),
                    command: "split".to_string(),
                    args: vec![],
                });
            }

            if goal_str.contains("OR") || goal_str.contains("\\/") {
                suggestions.push(Tactic::Cases(goal.target.clone()));
            }

            if goal_str.contains("=") {
                suggestions.push(Tactic::Reflexivity);
                suggestions.push(Tactic::Simplify);
            }

            // Always suggest grind as a fallback
            suggestions.push(Tactic::Custom {
                prover: "PVS".to_string(),
                command: "grind".to_string(),
                args: vec![],
            });

            // Suggest ground for arithmetic
            if goal_str.contains('+') || goal_str.contains('-') ||
               goal_str.contains('*') || goal_str.contains('<') || goal_str.contains('>') {
                suggestions.push(Tactic::Custom {
                    prover: "PVS".to_string(),
                    command: "ground".to_string(),
                    args: vec![],
                });
            }
        }

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // PVS doesn't have a direct theorem search, but we can suggest library lemmas
        let common_lemmas = vec![
            "nat_induction",
            "strong_induction",
            "well_founded_induction",
            "list_induction",
            "set_induction",
            "real_props.add_commutative",
            "real_props.mul_commutative",
            "real_props.add_associative",
            "real_props.mul_associative",
            "real_props.distributive",
            "booleans.iff_def",
            "booleans.implies_def",
            "sets.member_add",
            "sets.union_def",
            "sets.intersection_def",
            "sequences.nth_add",
            "sequences.length_append",
        ];

        let pattern_lower = pattern.to_lowercase();
        let matches: Vec<String> = common_lemmas.iter()
            .filter(|l| l.to_lowercase().contains(&pattern_lower))
            .map(|s| s.to_string())
            .collect();

        Ok(matches)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_expr() {
        let mut parser = PVSParser::new("x + y");
        let expr = parser.parse_expr().unwrap();

        match expr {
            PVSExpr::Application { function, arguments } => {
                assert_eq!(arguments.len(), 2);
            }
            _ => panic!("Expected application"),
        }
    }

    #[test]
    fn test_parse_forall() {
        let mut parser = PVSParser::new("FORALL (x: nat): x >= 0");
        let expr = parser.parse_expr().unwrap();

        match expr {
            PVSExpr::Forall { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].name, "x");
            }
            _ => panic!("Expected forall"),
        }
    }

    #[test]
    fn test_parse_if_then_else() {
        let mut parser = PVSParser::new("IF x > 0 THEN 1 ELSE 0 ENDIF");
        let expr = parser.parse_expr().unwrap();

        match expr {
            PVSExpr::IfThenElse { .. } => {}
            _ => panic!("Expected if-then-else"),
        }
    }

    #[test]
    fn test_parse_lambda() {
        let mut parser = PVSParser::new("LAMBDA (x: int): x * x");
        let expr = parser.parse_expr().unwrap();

        match expr {
            PVSExpr::Lambda { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
            }
            _ => panic!("Expected lambda"),
        }
    }

    #[test]
    fn test_parse_record() {
        let mut parser = PVSParser::new("(# x := 1, y := 2 #)");
        let expr = parser.parse_expr().unwrap();

        match expr {
            PVSExpr::Record(fields) => {
                assert_eq!(fields.len(), 2);
            }
            _ => panic!("Expected record"),
        }
    }

    #[test]
    fn test_parse_function_type() {
        let mut parser = PVSParser::new("[int -> bool]");
        let t = parser.parse_type().unwrap();

        match t {
            PVSType::Function { .. } => {}
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_parse_subtype() {
        let mut parser = PVSParser::new("{x: int | x > 0}");
        let t = parser.parse_type().unwrap();

        match t {
            PVSType::Subtype { .. } => {}
            _ => panic!("Expected subtype"),
        }
    }

    #[test]
    fn test_parse_strategy_grind() {
        let mut parser = PVSParser::new("(grind)");
        let strategy = parser.parse_strategy().unwrap();

        match strategy {
            PVSStrategy::Grind { .. } => {}
            _ => panic!("Expected grind strategy"),
        }
    }

    #[test]
    fn test_parse_strategy_induct() {
        let mut parser = PVSParser::new("(induct \"n\")");
        let strategy = parser.parse_strategy().unwrap();

        match strategy {
            PVSStrategy::Induct { var, .. } => {
                assert_eq!(var, "n");
            }
            _ => panic!("Expected induct strategy"),
        }
    }

    #[test]
    fn test_format_expr() {
        let expr = PVSExpr::Forall {
            bindings: vec![PVSBinding {
                name: "x".to_string(),
                var_type: Box::new(PVSType::Name("nat".to_string())),
            }],
            body: Box::new(PVSExpr::Application {
                function: Box::new(PVSExpr::Name(">=".to_string())),
                arguments: vec![
                    PVSExpr::Name("x".to_string()),
                    PVSExpr::Number(0),
                ],
            }),
        };

        let formatted = PVSBackend::format_expr(&expr);
        assert!(formatted.contains("FORALL"));
        assert!(formatted.contains("nat"));
    }

    #[test]
    fn test_expr_to_term_roundtrip() {
        let expr = PVSExpr::Application {
            function: Box::new(PVSExpr::Name("+".to_string())),
            arguments: vec![
                PVSExpr::Name("x".to_string()),
                PVSExpr::Number(1),
            ],
        };

        let term = PVSBackend::expr_to_term(&expr);
        let expr2 = PVSBackend::term_to_expr(&term);

        // Should preserve structure
        match expr2 {
            PVSExpr::Application { arguments, .. } => {
                assert_eq!(arguments.len(), 2);
            }
            _ => panic!("Expected application"),
        }
    }
}
