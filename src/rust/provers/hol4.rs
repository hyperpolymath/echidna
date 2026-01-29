// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

#![allow(dead_code)]

//! HOL4 (Higher Order Logic 4) backend implementation.
//!
//! HOL4 is a proof assistant for higher-order logic based on the LCF approach.
//! It features:
//! - Classical higher-order logic
//! - SML-based implementation and metalanguage
//! - Rich tactic library with automation
//! - Large formalized mathematics library
//! - Backward-style proof construction

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
// HOL4 AST Types
// ============================================================================

/// HOL4 term representation
#[derive(Debug, Clone, PartialEq)]
pub enum HOL4Term {
    /// Variable: x
    Var {
        name: String,
        ty: Option<HOL4Type>,
    },
    /// Constant: c
    Const {
        name: String,
        ty: Option<HOL4Type>,
    },
    /// Application: f x
    App {
        func: Box<HOL4Term>,
        arg: Box<HOL4Term>,
    },
    /// Lambda abstraction: \x. body
    Abs {
        var: String,
        var_type: Option<HOL4Type>,
        body: Box<HOL4Term>,
    },
    /// Combination/binary operation: x op y
    Comb {
        operator: String,
        left: Box<HOL4Term>,
        right: Box<HOL4Term>,
    },
    /// Conditional: if p then t else f
    Cond {
        cond: Box<HOL4Term>,
        then_branch: Box<HOL4Term>,
        else_branch: Box<HOL4Term>,
    },
    /// Let binding: let x = e in body
    Let {
        bindings: Vec<(String, HOL4Term)>,
        body: Box<HOL4Term>,
    },
    /// Quantification: !x. P or ?x. P
    Quant {
        quantifier: HOL4Quantifier,
        var: String,
        var_type: Option<HOL4Type>,
        body: Box<HOL4Term>,
    },
    /// Numeric literal
    Numeral(i64),
    /// String literal
    String(String),
    /// List literal: [a; b; c]
    List(Vec<HOL4Term>),
    /// Pair: (a, b)
    Pair(Box<HOL4Term>, Box<HOL4Term>),
    /// Type annotation: t : ty
    TypeAnnot {
        term: Box<HOL4Term>,
        ty: HOL4Type,
    },
}

/// HOL4 quantifier
#[derive(Debug, Clone, PartialEq)]
pub enum HOL4Quantifier {
    /// Universal: !
    Forall,
    /// Existential: ?
    Exists,
    /// Unique existential: ?!
    ExistsUnique,
    /// Choice operator: @
    Choose,
}

/// HOL4 type representation
#[derive(Debug, Clone, PartialEq)]
pub enum HOL4Type {
    /// Type variable: 'a
    TyVar(String),
    /// Type constructor: bool, num, etc.
    TyCon(String),
    /// Type application: ('a, 'b) map
    TyApp {
        constructor: String,
        args: Vec<HOL4Type>,
    },
    /// Function type: ty1 -> ty2
    TyFun {
        domain: Box<HOL4Type>,
        range: Box<HOL4Type>,
    },
    /// Product type: ty1 # ty2
    TyProd(Vec<HOL4Type>),
    /// Sum type: ty1 + ty2
    TySum {
        left: Box<HOL4Type>,
        right: Box<HOL4Type>,
    },
}

// ============================================================================
// HOL4 Tactic Types
// ============================================================================

/// HOL4 tactic representation
#[derive(Debug, Clone)]
pub enum HOL4Tactic {
    /// Rewrite with theorems: rw[thm1, thm2]
    Rewrite(Vec<String>),
    /// Simplify: simp[]
    Simp(Vec<String>),
    /// Full simplify: fs[]
    FS(Vec<String>),
    /// Reverse full simplify: rfs[]
    RFS(Vec<String>),
    /// Global simplify: gs[]
    GS(Vec<String>),
    /// Decide: DECIDE_TAC
    Decide,
    /// Arithmetic: ARITH_TAC
    Arith,
    /// Cases: Cases_on `expr`
    Cases(HOL4Term),
    /// Induction: Induct_on `var`
    Induct(String),
    /// Complete induction: completeInduct_on `var`
    CompleteInduct(String),
    /// Strip goal: STRIP_TAC
    Strip,
    /// Generalize: gen_tac
    Gen,
    /// Conjunction split: conj_tac
    ConjTac,
    /// Disjunction: disj1_tac, disj2_tac
    DisjTac(u8),
    /// Existential: EXISTS_TAC `witness`
    Exists(HOL4Term),
    /// Apply theorem: irule thm
    IRule(String),
    /// Match against pattern: MATCH_MP_TAC thm
    MatchMP(String),
    /// Assume: assume_tac thm
    Assume(String),
    /// Reverse assumption: first_x_assum
    FirstXAssum(Box<HOL4Tactic>),
    /// Meta-implication: metis_tac[thms]
    Metis(Vec<String>),
    /// Decision procedure: blastLib.BBLAST_TAC
    BBlast,
    /// Word reasoning: wordsLib.WORD_TAC
    Word,
    /// Finite map: fmapLib.FM_TAC
    FMap,
    /// String theory: stringLib.STRING_TAC
    StringTac,
    /// No-op: ALL_TAC
    AllTac,
    /// Fail: NO_TAC
    NoTac,
    /// Sequence: tac1 >> tac2
    Then(Box<HOL4Tactic>, Box<HOL4Tactic>),
    /// Alternative: tac1 ORELSE tac2
    OrElse(Box<HOL4Tactic>, Box<HOL4Tactic>),
    /// Repeat: REPEAT tac
    Repeat(Box<HOL4Tactic>),
    /// Try: TRY tac
    Try(Box<HOL4Tactic>),
    /// Reverse: REVERSE
    Reverse,
    /// Pop assumption: pop_assum
    PopAssum(Box<HOL4Tactic>),
    /// Quantifier instantiation: qspec_then `tm` (ttac thm)
    QSpecThen(HOL4Term, Box<HOL4Tactic>),
    /// Use definition: once_rewrite_tac[def]
    OnceRewrite(Vec<String>),
    /// Compute: EVAL_TAC
    Eval,
    /// Custom SML code
    Custom(String),
}

// ============================================================================
// HOL4 Declaration Types
// ============================================================================

/// HOL4 theory declaration
#[derive(Debug, Clone)]
pub enum HOL4Declaration {
    /// Definition: val def = Define `...`
    Definition {
        name: String,
        body: HOL4Term,
        is_recursive: bool,
    },
    /// Datatype: Datatype `...`
    Datatype {
        name: String,
        type_vars: Vec<String>,
        constructors: Vec<HOL4Constructor>,
    },
    /// Theorem: val thm = store_thm(...) or Theorem name: ...
    Theorem {
        name: String,
        statement: HOL4Term,
        proof: Option<Vec<HOL4Tactic>>,
    },
    /// Type abbreviation: Type `name = ...`
    TypeAbbrev {
        name: String,
        type_vars: Vec<String>,
        expansion: HOL4Type,
    },
    /// Overload: overload_on(...)
    Overload {
        name: String,
        term: HOL4Term,
    },
    /// Infix declaration: set_fixity "op" (Infix(prec, side))
    Infix {
        name: String,
        precedence: u32,
        associativity: Associativity,
    },
    /// Open theory: open theoryLib
    Open(String),
    /// Export theorem: val _ = export_theory()
    Export,
}

/// HOL4 datatype constructor
#[derive(Debug, Clone)]
pub struct HOL4Constructor {
    pub name: String,
    pub args: Vec<HOL4Type>,
}

/// Operator associativity
#[derive(Debug, Clone)]
pub enum Associativity {
    Left,
    Right,
    NonAssoc,
}

// ============================================================================
// HOL4 Theory Structure
// ============================================================================

/// A HOL4 theory (Script.sml file)
#[derive(Debug, Clone)]
pub struct HOL4Theory {
    pub name: String,
    pub parents: Vec<String>,
    pub declarations: Vec<HOL4Declaration>,
}

// ============================================================================
// HOL4 Session Management
// ============================================================================

/// HOL4 interactive session
pub struct HOL4Session {
    process: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    theory_loaded: Option<String>,
}

impl HOL4Session {
    /// Send a command to HOL4 and get the response
    async fn send_command(&mut self, command: &str) -> Result<String> {
        // Send command
        self.stdin.write_all(command.as_bytes()).await?;
        self.stdin.write_all(b"\n").await?;
        self.stdin.flush().await?;

        // Read response until prompt
        let mut response = String::new();
        let mut line = String::new();

        loop {
            line.clear();
            let bytes_read = self.stdout.read_line(&mut line).await?;
            if bytes_read == 0 {
                break;
            }

            // HOL4 prompt is typically ">"
            if line.trim() == ">" || line.starts_with("- ") || line.starts_with("# ") {
                break;
            }

            response.push_str(&line);
        }

        Ok(response)
    }
}

// ============================================================================
// HOL4 Parser
// ============================================================================

/// Parser for HOL4 terms, types, and declarations
pub struct HOL4Parser {
    input: Vec<char>,
    pos: usize,
}

impl HOL4Parser {
    pub fn new(input: &str) -> Self {
        HOL4Parser {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else if c == '(' && self.input.get(self.pos + 1) == Some(&'*') {
                // Skip ML comments
                self.pos += 2;
                while self.pos + 1 < self.input.len() {
                    if self.input[self.pos] == '*' && self.input[self.pos + 1] == ')' {
                        self.pos += 2;
                        break;
                    }
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn expect_char(&mut self, expected: char) -> Result<()> {
        self.skip_whitespace();
        match self.advance() {
            Some(c) if c == expected => Ok(()),
            Some(c) => bail!("Expected '{}', found '{}'", expected, c),
            None => bail!("Expected '{}', found end of input", expected),
        }
    }

    fn try_consume(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        let start = self.pos;
        for c in s.chars() {
            if self.peek() == Some(c) {
                self.advance();
            } else {
                self.pos = start;
                return false;
            }
        }
        true
    }

    fn parse_identifier(&mut self) -> Result<String> {
        self.skip_whitespace();
        let mut name = String::new();

        // First character must be letter or underscore
        match self.peek() {
            Some(c) if c.is_alphabetic() || c == '_' || c == '\'' => {
                name.push(c);
                self.advance();
            }
            _ => bail!("Expected identifier"),
        }

        // Rest can include digits
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        Ok(name)
    }

    fn parse_number(&mut self) -> Result<i64> {
        self.skip_whitespace();
        let mut num_str = String::new();

        if self.peek() == Some('-') {
            num_str.push('-');
            self.advance();
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        num_str.parse().map_err(|_| anyhow::anyhow!("Invalid number: {}", num_str))
    }

    /// Parse a HOL4 term
    pub fn parse_term(&mut self) -> Result<HOL4Term> {
        self.parse_term_or()
    }

    fn parse_term_or(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_and()?;

        while self.try_consume("\\/") || self.try_consume("∨") {
            let right = self.parse_term_and()?;
            left = HOL4Term::Comb {
                operator: "\\/".to_string(),
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_term_and(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_impl()?;

        while self.try_consume("/\\") || self.try_consume("∧") {
            let right = self.parse_term_impl()?;
            left = HOL4Term::Comb {
                operator: "/\\".to_string(),
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_term_impl(&mut self) -> Result<HOL4Term> {
        let left = self.parse_term_eq()?;

        if self.try_consume("==>") || self.try_consume("⇒") {
            let right = self.parse_term_impl()?; // Right associative
            return Ok(HOL4Term::Comb {
                operator: "==>".to_string(),
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    fn parse_term_eq(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_rel()?;

        while self.try_consume("=") {
            let right = self.parse_term_rel()?;
            left = HOL4Term::Comb {
                operator: "=".to_string(),
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_term_rel(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_add()?;

        loop {
            let op = if self.try_consume("<=") { Some("<=") }
                else if self.try_consume(">=") { Some(">=") }
                else if self.try_consume("<") { Some("<") }
                else if self.try_consume(">") { Some(">") }
                else { None };

            if let Some(op) = op {
                let right = self.parse_term_add()?;
                left = HOL4Term::Comb {
                    operator: op.to_string(),
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_term_add(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_mul()?;

        loop {
            let op = if self.try_consume("+") { Some("+") }
                else if self.try_consume("-") && !self.peek().map(|c| c.is_ascii_digit()).unwrap_or(false) { Some("-") }
                else { None };

            if let Some(op) = op {
                let right = self.parse_term_mul()?;
                left = HOL4Term::Comb {
                    operator: op.to_string(),
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_term_mul(&mut self) -> Result<HOL4Term> {
        let mut left = self.parse_term_unary()?;

        loop {
            let op = if self.try_consume("*") { Some("*") }
                else if self.try_consume("DIV") { Some("DIV") }
                else if self.try_consume("MOD") { Some("MOD") }
                else { None };

            if let Some(op) = op {
                let right = self.parse_term_unary()?;
                left = HOL4Term::Comb {
                    operator: op.to_string(),
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_term_unary(&mut self) -> Result<HOL4Term> {
        self.skip_whitespace();

        // Negation
        if self.try_consume("~") || self.try_consume("¬") {
            let inner = self.parse_term_unary()?;
            return Ok(HOL4Term::App {
                func: Box::new(HOL4Term::Const { name: "~".to_string(), ty: None }),
                arg: Box::new(inner),
            });
        }

        self.parse_term_app()
    }

    fn parse_term_app(&mut self) -> Result<HOL4Term> {
        let mut term = self.parse_term_atom()?;

        loop {
            self.skip_whitespace();
            // Check if next token could be an argument
            match self.peek() {
                Some('(') | Some('[') | Some('"') => {}
                Some(c) if c.is_alphabetic() || c == '_' || c == '\'' || c.is_ascii_digit() => {}
                _ => break,
            }

            // Try to parse an argument
            let start = self.pos;
            if let Ok(arg) = self.parse_term_atom() {
                term = HOL4Term::App {
                    func: Box::new(term),
                    arg: Box::new(arg),
                };
            } else {
                self.pos = start;
                break;
            }
        }

        Ok(term)
    }

    fn parse_term_atom(&mut self) -> Result<HOL4Term> {
        self.skip_whitespace();

        // Quantifiers
        if self.try_consume("!") || self.try_consume("∀") {
            return self.parse_quantified(HOL4Quantifier::Forall);
        }
        if self.try_consume("?!") || self.try_consume("∃!") {
            return self.parse_quantified(HOL4Quantifier::ExistsUnique);
        }
        if self.try_consume("?") || self.try_consume("∃") {
            return self.parse_quantified(HOL4Quantifier::Exists);
        }
        if self.try_consume("@") {
            return self.parse_quantified(HOL4Quantifier::Choose);
        }

        // Lambda
        if self.try_consume("\\") || self.try_consume("λ") {
            return self.parse_lambda();
        }

        // Let
        if self.try_consume("let") {
            return self.parse_let();
        }

        // Conditional
        if self.try_consume("if") {
            return self.parse_conditional();
        }

        // Parenthesized expression or tuple
        if self.peek() == Some('(') {
            self.advance();
            let term = self.parse_term()?;

            // Check for tuple
            if self.try_consume(",") {
                let second = self.parse_term()?;
                self.expect_char(')')?;
                return Ok(HOL4Term::Pair(Box::new(term), Box::new(second)));
            }

            self.expect_char(')')?;
            return Ok(term);
        }

        // List
        if self.peek() == Some('[') {
            return self.parse_list();
        }

        // String literal
        if self.peek() == Some('"') {
            return self.parse_string();
        }

        // Number
        if self.peek().map(|c| c.is_ascii_digit() || c == '-').unwrap_or(false) {
            let num = self.parse_number()?;
            return Ok(HOL4Term::Numeral(num));
        }

        // Type variable (in term position - rare but possible)
        if self.peek() == Some('\'') {
            let name = self.parse_identifier()?;
            return Ok(HOL4Term::Var { name, ty: None });
        }

        // Identifier (variable or constant)
        let name = self.parse_identifier()?;

        // Check for type annotation
        if self.try_consume(":") {
            let ty = self.parse_type()?;
            return Ok(HOL4Term::TypeAnnot {
                term: Box::new(HOL4Term::Var { name, ty: None }),
                ty,
            });
        }

        // Determine if it's a constant or variable based on name conventions
        let is_const = name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false)
            || ["T", "F", "SUC", "PRE", "HD", "TL", "CONS", "NIL", "FST", "SND", "SOME", "NONE"]
                .contains(&name.as_str());

        if is_const {
            Ok(HOL4Term::Const { name, ty: None })
        } else {
            Ok(HOL4Term::Var { name, ty: None })
        }
    }

    fn parse_quantified(&mut self, quantifier: HOL4Quantifier) -> Result<HOL4Term> {
        self.skip_whitespace();
        let var = self.parse_identifier()?;

        let var_type = if self.try_consume(":") {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect_char('.')?;
        let body = self.parse_term()?;

        Ok(HOL4Term::Quant {
            quantifier,
            var,
            var_type,
            body: Box::new(body),
        })
    }

    fn parse_lambda(&mut self) -> Result<HOL4Term> {
        self.skip_whitespace();
        let var = self.parse_identifier()?;

        let var_type = if self.try_consume(":") {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect_char('.')?;
        let body = self.parse_term()?;

        Ok(HOL4Term::Abs {
            var,
            var_type,
            body: Box::new(body),
        })
    }

    fn parse_let(&mut self) -> Result<HOL4Term> {
        self.skip_whitespace();
        let mut bindings = Vec::new();

        loop {
            let name = self.parse_identifier()?;
            self.expect_char('=')?;
            let value = self.parse_term()?;
            bindings.push((name, value));

            if !self.try_consume("and") {
                break;
            }
        }

        self.skip_whitespace();
        if !self.try_consume("in") {
            bail!("Expected 'in' in let expression");
        }

        let body = self.parse_term()?;

        Ok(HOL4Term::Let {
            bindings,
            body: Box::new(body),
        })
    }

    fn parse_conditional(&mut self) -> Result<HOL4Term> {
        let cond = self.parse_term()?;

        self.skip_whitespace();
        if !self.try_consume("then") {
            bail!("Expected 'then' in conditional");
        }

        let then_branch = self.parse_term()?;

        self.skip_whitespace();
        if !self.try_consume("else") {
            bail!("Expected 'else' in conditional");
        }

        let else_branch = self.parse_term()?;

        Ok(HOL4Term::Cond {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    fn parse_list(&mut self) -> Result<HOL4Term> {
        self.expect_char('[')?;
        let mut elements = Vec::new();

        self.skip_whitespace();
        if self.peek() != Some(']') {
            elements.push(self.parse_term()?);

            while self.try_consume(";") {
                elements.push(self.parse_term()?);
            }
        }

        self.expect_char(']')?;
        Ok(HOL4Term::List(elements))
    }

    fn parse_string(&mut self) -> Result<HOL4Term> {
        self.expect_char('"')?;
        let mut s = String::new();

        while let Some(c) = self.peek() {
            if c == '"' {
                self.advance();
                break;
            } else if c == '\\' {
                self.advance();
                match self.advance() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('\\') => s.push('\\'),
                    Some('"') => s.push('"'),
                    Some(c) => s.push(c),
                    None => bail!("Unexpected end of string"),
                }
            } else {
                s.push(c);
                self.advance();
            }
        }

        Ok(HOL4Term::String(s))
    }

    /// Parse a HOL4 type
    pub fn parse_type(&mut self) -> Result<HOL4Type> {
        self.parse_type_fun()
    }

    fn parse_type_fun(&mut self) -> Result<HOL4Type> {
        let left = self.parse_type_prod()?;

        if self.try_consume("->") || self.try_consume("→") {
            let right = self.parse_type_fun()?; // Right associative
            return Ok(HOL4Type::TyFun {
                domain: Box::new(left),
                range: Box::new(right),
            });
        }

        Ok(left)
    }

    fn parse_type_prod(&mut self) -> Result<HOL4Type> {
        let mut types = vec![self.parse_type_sum()?];

        while self.try_consume("#") || self.try_consume("×") {
            types.push(self.parse_type_sum()?);
        }

        if types.len() == 1 {
            Ok(types.pop().unwrap())
        } else {
            Ok(HOL4Type::TyProd(types))
        }
    }

    fn parse_type_sum(&mut self) -> Result<HOL4Type> {
        let left = self.parse_type_app()?;

        if self.try_consume("+") {
            let right = self.parse_type_sum()?;
            return Ok(HOL4Type::TySum {
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    fn parse_type_app(&mut self) -> Result<HOL4Type> {
        let base = self.parse_type_atom()?;

        // Check for type application like: ('a, 'b) map
        self.skip_whitespace();
        if let Some(c) = self.peek() {
            if c.is_alphabetic() {
                let constructor = self.parse_identifier()?;
                match base {
                    HOL4Type::TyVar(_) | HOL4Type::TyCon(_) => {
                        return Ok(HOL4Type::TyApp {
                            constructor,
                            args: vec![base],
                        });
                    }
                    HOL4Type::TyProd(args) => {
                        return Ok(HOL4Type::TyApp {
                            constructor,
                            args,
                        });
                    }
                    _ => {}
                }
            }
        }

        Ok(base)
    }

    fn parse_type_atom(&mut self) -> Result<HOL4Type> {
        self.skip_whitespace();

        // Parenthesized type or tuple
        if self.peek() == Some('(') {
            self.advance();
            let mut types = vec![self.parse_type()?];

            while self.try_consume(",") {
                types.push(self.parse_type()?);
            }

            self.expect_char(')')?;

            if types.len() == 1 {
                return Ok(types.pop().unwrap());
            } else {
                return Ok(HOL4Type::TyProd(types));
            }
        }

        // Type variable
        if self.peek() == Some('\'') {
            self.advance();
            let name = self.parse_identifier()?;
            return Ok(HOL4Type::TyVar(format!("'{}", name)));
        }

        // Type name
        if self.try_consume(":") {
            let name = self.parse_identifier()?;
            return Ok(HOL4Type::TyCon(format!(":{}", name)));
        }

        let name = self.parse_identifier()?;
        Ok(HOL4Type::TyCon(name))
    }

    /// Parse a HOL4 theory file
    pub fn parse_theory(&mut self) -> Result<HOL4Theory> {
        let mut name = String::new();
        let mut parents = Vec::new();
        let mut declarations = Vec::new();

        self.skip_whitespace();

        // Parse theory header
        while self.pos < self.input.len() {
            self.skip_whitespace();

            if self.try_consume("open") {
                let lib = self.parse_identifier()?;
                declarations.push(HOL4Declaration::Open(lib.clone()));
                if lib.ends_with("Theory") {
                    parents.push(lib.trim_end_matches("Theory").to_string());
                }
            } else if self.try_consume("val") {
                // Parse val declaration
                self.skip_whitespace();

                if self.try_consume("_") {
                    // val _ = ... (typically export_theory())
                    self.expect_char('=')?;
                    self.skip_whitespace();
                    if self.try_consume("export_theory") {
                        declarations.push(HOL4Declaration::Export);
                    }
                    // Skip to end of declaration
                    while let Some(c) = self.peek() {
                        if c == ';' {
                            self.advance();
                            break;
                        }
                        self.advance();
                    }
                } else {
                    let decl_name = self.parse_identifier()?;
                    self.expect_char('=')?;
                    self.skip_whitespace();

                    if self.try_consume("Define") {
                        // Parse definition
                        if let Ok(decl) = self.parse_define_decl(&decl_name) {
                            declarations.push(decl);
                        }
                    } else if self.try_consume("store_thm") {
                        // Parse theorem
                        if let Ok(decl) = self.parse_store_thm(&decl_name) {
                            declarations.push(decl);
                        }
                    }
                }
            } else if self.try_consume("Definition") {
                // New-style definition
                let decl_name = self.parse_identifier()?;
                if let Ok(decl) = self.parse_new_definition(&decl_name) {
                    declarations.push(decl);
                }
            } else if self.try_consume("Theorem") {
                // New-style theorem
                let decl_name = self.parse_identifier()?;
                if let Ok(decl) = self.parse_new_theorem(&decl_name) {
                    declarations.push(decl);
                }
            } else if self.try_consume("Datatype") {
                // Parse datatype
                if let Ok(decl) = self.parse_datatype() {
                    declarations.push(decl);
                }
            } else {
                // Skip unknown content
                self.advance();
            }
        }

        // Infer theory name from filename or use default
        if name.is_empty() {
            name = "Anonymous".to_string();
        }

        Ok(HOL4Theory {
            name,
            parents,
            declarations,
        })
    }

    fn parse_define_decl(&mut self, name: &str) -> Result<HOL4Declaration> {
        // Skip to the quoted term
        self.skip_whitespace();
        if !self.try_consume("`") {
            bail!("Expected backtick in Define");
        }

        let body = self.parse_term()?;

        if !self.try_consume("`") {
            bail!("Expected closing backtick");
        }

        Ok(HOL4Declaration::Definition {
            name: name.to_string(),
            body,
            is_recursive: false,
        })
    }

    fn parse_store_thm(&mut self, name: &str) -> Result<HOL4Declaration> {
        self.expect_char('(')?;

        // Skip the string name
        self.skip_whitespace();
        if self.peek() == Some('"') {
            self.parse_string()?;
            self.try_consume(",");
        }

        // Parse the statement
        if !self.try_consume("``") && !self.try_consume("`") {
            bail!("Expected term quotes in store_thm");
        }

        let statement = self.parse_term()?;

        self.skip_whitespace();
        self.try_consume("``");
        self.try_consume("`");

        Ok(HOL4Declaration::Theorem {
            name: name.to_string(),
            statement,
            proof: None,
        })
    }

    fn parse_new_definition(&mut self, name: &str) -> Result<HOL4Declaration> {
        self.skip_whitespace();

        // Skip to the term
        while let Some(c) = self.peek() {
            if c == '`' {
                break;
            }
            self.advance();
        }

        self.try_consume("`");
        let body = self.parse_term()?;
        self.try_consume("`");

        Ok(HOL4Declaration::Definition {
            name: name.to_string(),
            body,
            is_recursive: false,
        })
    }

    fn parse_new_theorem(&mut self, name: &str) -> Result<HOL4Declaration> {
        self.skip_whitespace();

        // Skip to the term
        while let Some(c) = self.peek() {
            if c == '`' {
                break;
            }
            self.advance();
        }

        self.try_consume("`");
        let statement = self.parse_term()?;
        self.try_consume("`");

        Ok(HOL4Declaration::Theorem {
            name: name.to_string(),
            statement,
            proof: None,
        })
    }

    fn parse_datatype(&mut self) -> Result<HOL4Declaration> {
        self.skip_whitespace();

        // Find the backtick
        while let Some(c) = self.peek() {
            if c == '`' {
                self.advance();
                break;
            }
            self.advance();
        }

        // Parse name and type vars
        let name = self.parse_identifier()?;
        let mut type_vars = Vec::new();
        let mut constructors = Vec::new();

        self.expect_char('=')?;

        // Parse constructors
        loop {
            self.skip_whitespace();
            let ctor_name = self.parse_identifier()?;
            let mut args = Vec::new();

            // Parse constructor arguments
            while self.try_consume("of") || self.try_consume("=>") {
                args.push(self.parse_type()?);
            }

            constructors.push(HOL4Constructor {
                name: ctor_name,
                args,
            });

            if !self.try_consume("|") {
                break;
            }
        }

        self.try_consume("`");

        Ok(HOL4Declaration::Datatype {
            name,
            type_vars,
            constructors,
        })
    }
}

// ============================================================================
// HOL4 Backend Implementation
// ============================================================================

pub struct Hol4Backend {
    config: ProverConfig,
    session: Mutex<Option<HOL4Session>>,
}

impl Hol4Backend {
    pub fn new(config: ProverConfig) -> Self {
        Hol4Backend {
            config,
            session: Mutex::new(None),
        }
    }

    /// Start HOL4 session
    async fn start_session(&self) -> Result<HOL4Session> {
        let hol4_path = self.config.executable.clone();

        let mut process = Command::new(&hol4_path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .context("Failed to start HOL4")?;

        let stdin = process.stdin.take()
            .ok_or_else(|| anyhow::anyhow!("Failed to get HOL4 stdin"))?;
        let stdout = process.stdout.take()
            .ok_or_else(|| anyhow::anyhow!("Failed to get HOL4 stdout"))?;

        let session = HOL4Session {
            process,
            stdin,
            stdout: BufReader::new(stdout),
            theory_loaded: None,
        };

        Ok(session)
    }

    /// Send command to HOL4 session
    async fn send_command(session: &mut HOL4Session, command: &str) -> Result<String> {
        session.send_command(command).await
    }

    // ========================================================================
    // Term Conversion
    // ========================================================================

    /// Convert universal Term to HOL4 term
    fn term_to_hol4(term: &Term) -> HOL4Term {
        match term {
            Term::Var(name) => HOL4Term::Var { name: name.clone(), ty: None },
            Term::Const(name) => HOL4Term::Const { name: name.clone(), ty: None },
            Term::Universe(_) | Term::Type(_) | Term::Sort(_) => {
                HOL4Term::Const { name: "univ".to_string(), ty: None }
            }
            Term::App { func, args } => {
                let mut result = Self::term_to_hol4(func);
                for arg in args {
                    result = HOL4Term::App {
                        func: Box::new(result),
                        arg: Box::new(Self::term_to_hol4(arg)),
                    };
                }
                result
            }
            Term::Lambda { param, param_type, body } => {
                HOL4Term::Abs {
                    var: param.clone(),
                    var_type: param_type.as_ref().map(|t| Self::term_to_type(t)),
                    body: Box::new(Self::term_to_hol4(body)),
                }
            }
            Term::Pi { param, param_type, body } => {
                HOL4Term::Quant {
                    quantifier: HOL4Quantifier::Forall,
                    var: param.clone(),
                    var_type: Some(Self::term_to_type(param_type)),
                    body: Box::new(Self::term_to_hol4(body)),
                }
            }
            Term::Let { name, value, body, .. } => {
                HOL4Term::Let {
                    bindings: vec![(name.clone(), Self::term_to_hol4(value))],
                    body: Box::new(Self::term_to_hol4(body)),
                }
            }
            Term::Match { scrutinee, branches, .. } => {
                // HOL4 doesn't have native pattern matching in terms
                // Approximate with nested conditionals
                if branches.is_empty() {
                    return Self::term_to_hol4(scrutinee);
                }

                let mut result: Option<HOL4Term> = None;
                for (pattern, body) in branches.iter().rev() {
                    let cond = HOL4Term::Comb {
                        operator: "=".to_string(),
                        left: Box::new(Self::term_to_hol4(scrutinee)),
                        right: Box::new(Self::pattern_to_hol4(pattern)),
                    };
                    let then_branch = Self::term_to_hol4(body);

                    if let Some(else_branch) = result {
                        result = Some(HOL4Term::Cond {
                            cond: Box::new(cond),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        });
                    } else {
                        result = Some(then_branch);
                    }
                }

                result.unwrap_or_else(|| HOL4Term::Const { name: "ARB".to_string(), ty: None })
            }
            Term::Hole(name) => {
                HOL4Term::Var { name: format!("?{}", name), ty: None }
            }
            Term::Fix { name, body, .. } => {
                // Approximate fixpoint with application
                HOL4Term::App {
                    func: Box::new(HOL4Term::Const { name: "FIX".to_string(), ty: None }),
                    arg: Box::new(HOL4Term::Abs {
                        var: name.clone(),
                        var_type: None,
                        body: Box::new(Self::term_to_hol4(body)),
                    }),
                }
            }
            Term::Meta(id) => {
                HOL4Term::Var { name: format!("?{}", id), ty: None }
            }
            Term::ProverSpecific { data, .. } => {
                HOL4Term::Const { name: data.to_string(), ty: None }
            }
        }
    }

    /// Convert Pattern to HOL4 term
    fn pattern_to_hol4(pattern: &crate::core::Pattern) -> HOL4Term {
        match pattern {
            crate::core::Pattern::Wildcard => HOL4Term::Var { name: "_".to_string(), ty: None },
            crate::core::Pattern::Var(name) => HOL4Term::Var { name: name.clone(), ty: None },
            crate::core::Pattern::Constructor { name, args } => {
                let mut result = HOL4Term::Const { name: name.clone(), ty: None };
                for arg in args {
                    result = HOL4Term::App {
                        func: Box::new(result),
                        arg: Box::new(Self::pattern_to_hol4(arg)),
                    };
                }
                result
            }
        }
    }

    /// Convert Term to HOL4 type
    fn term_to_type(term: &Term) -> HOL4Type {
        match term {
            Term::Var(name) | Term::Const(name) => HOL4Type::TyCon(name.clone()),
            Term::App { func, args } => {
                let constructor = match func.as_ref() {
                    Term::Const(name) | Term::Var(name) => name.clone(),
                    _ => "app".to_string(),
                };
                HOL4Type::TyApp {
                    constructor,
                    args: args.iter().map(|a| Self::term_to_type(a)).collect(),
                }
            }
            Term::Pi { param_type, body, .. } => {
                HOL4Type::TyFun {
                    domain: Box::new(Self::term_to_type(param_type)),
                    range: Box::new(Self::term_to_type(body)),
                }
            }
            _ => HOL4Type::TyCon("'a".to_string()),
        }
    }

    /// Convert HOL4 term to universal Term
    fn hol4_to_term(term: &HOL4Term) -> Term {
        match term {
            HOL4Term::Var { name, .. } => Term::Var(name.clone()),
            HOL4Term::Const { name, .. } => Term::Const(name.clone()),
            HOL4Term::App { func, arg } => {
                Term::App {
                    func: Box::new(Self::hol4_to_term(func)),
                    args: vec![Self::hol4_to_term(arg)],
                }
            }
            HOL4Term::Abs { var, var_type, body } => {
                Term::Lambda {
                    param: var.clone(),
                    param_type: var_type.as_ref().map(|t| Box::new(Self::type_to_term(t))),
                    body: Box::new(Self::hol4_to_term(body)),
                }
            }
            HOL4Term::Comb { operator, left, right } => {
                Term::App {
                    func: Box::new(Term::Const(operator.clone())),
                    args: vec![Self::hol4_to_term(left), Self::hol4_to_term(right)],
                }
            }
            HOL4Term::Cond { cond, then_branch, else_branch } => {
                Term::App {
                    func: Box::new(Term::Const("if".to_string())),
                    args: vec![
                        Self::hol4_to_term(cond),
                        Self::hol4_to_term(then_branch),
                        Self::hol4_to_term(else_branch),
                    ],
                }
            }
            HOL4Term::Let { bindings, body } => {
                let mut result = Self::hol4_to_term(body);
                for (name, value) in bindings.iter().rev() {
                    result = Term::Let {
                        name: name.clone(),
                        ty: None,
                        value: Box::new(Self::hol4_to_term(value)),
                        body: Box::new(result),
                    };
                }
                result
            }
            HOL4Term::Quant { quantifier, var, var_type, body } => {
                match quantifier {
                    HOL4Quantifier::Forall => Term::Pi {
                        param: var.clone(),
                        param_type: Box::new(var_type.as_ref()
                            .map(|t| Self::type_to_term(t))
                            .unwrap_or_else(|| Term::Const("'a".to_string()))),
                        body: Box::new(Self::hol4_to_term(body)),
                    },
                    _ => {
                        // Encode other quantifiers as applications
                        Term::App {
                            func: Box::new(Term::Const(match quantifier {
                                HOL4Quantifier::Exists => "?".to_string(),
                                HOL4Quantifier::ExistsUnique => "?!".to_string(),
                                HOL4Quantifier::Choose => "@".to_string(),
                                HOL4Quantifier::Forall => unreachable!(),
                            })),
                            args: vec![Term::Lambda {
                                param: var.clone(),
                                param_type: var_type.as_ref().map(|t| Box::new(Self::type_to_term(t))),
                                body: Box::new(Self::hol4_to_term(body)),
                            }],
                        }
                    }
                }
            }
            HOL4Term::Numeral(n) => Term::Const(n.to_string()),
            HOL4Term::String(s) => Term::Const(format!("\"{}\"", s)),
            HOL4Term::List(elements) => {
                let mut result = Term::Const("NIL".to_string());
                for elem in elements.iter().rev() {
                    result = Term::App {
                        func: Box::new(Term::Const("CONS".to_string())),
                        args: vec![Self::hol4_to_term(elem), result],
                    };
                }
                result
            }
            HOL4Term::Pair(fst, snd) => {
                Term::App {
                    func: Box::new(Term::Const(",".to_string())),
                    args: vec![Self::hol4_to_term(fst), Self::hol4_to_term(snd)],
                }
            }
            HOL4Term::TypeAnnot { term, .. } => Self::hol4_to_term(term),
        }
    }

    /// Convert HOL4 type to Term
    fn type_to_term(ty: &HOL4Type) -> Term {
        match ty {
            HOL4Type::TyVar(name) | HOL4Type::TyCon(name) => Term::Const(name.clone()),
            HOL4Type::TyApp { constructor, args } => {
                Term::App {
                    func: Box::new(Term::Const(constructor.clone())),
                    args: args.iter().map(|a| Self::type_to_term(a)).collect(),
                }
            }
            HOL4Type::TyFun { domain, range } => {
                Term::Pi {
                    param: "_".to_string(),
                    param_type: Box::new(Self::type_to_term(domain)),
                    body: Box::new(Self::type_to_term(range)),
                }
            }
            HOL4Type::TyProd(types) => {
                if types.is_empty() {
                    Term::Const("unit".to_string())
                } else {
                    let mut args: Vec<Term> = types.iter().map(|t| Self::type_to_term(t)).collect();
                    let last = args.pop().unwrap();
                    args.into_iter().rev().fold(last, |acc, t| {
                        Term::App {
                            func: Box::new(Term::Const("#".to_string())),
                            args: vec![t, acc],
                        }
                    })
                }
            }
            HOL4Type::TySum { left, right } => {
                Term::App {
                    func: Box::new(Term::Const("+".to_string())),
                    args: vec![Self::type_to_term(left), Self::type_to_term(right)],
                }
            }
        }
    }

    // ========================================================================
    // Tactic Conversion
    // ========================================================================

    /// Convert universal Tactic to HOL4 tactic
    fn tactic_to_hol4(tactic: &Tactic) -> HOL4Tactic {
        match tactic {
            Tactic::Apply(name) => HOL4Tactic::IRule(name.clone()),
            Tactic::Intro(_) => HOL4Tactic::Strip,
            Tactic::Cases(term) => HOL4Tactic::Cases(Self::term_to_hol4(term)),
            Tactic::Induction(term) => {
                if let Term::Var(name) = term {
                    HOL4Tactic::Induct(name.clone())
                } else {
                    HOL4Tactic::Induct("x".to_string())
                }
            }
            Tactic::Rewrite(name) => HOL4Tactic::Rewrite(vec![name.clone()]),
            Tactic::Simplify => HOL4Tactic::Simp(vec![]),
            Tactic::Reflexivity => HOL4Tactic::Rewrite(vec!["REFL_CLAUSE".to_string()]),
            Tactic::Assumption => HOL4Tactic::FirstXAssum(Box::new(HOL4Tactic::Assume("_".to_string()))),
            Tactic::Exact(term) => {
                let hol4_term = Self::term_to_hol4(term);
                HOL4Tactic::Custom(Self::format_term(&hol4_term))
            }
            Tactic::Custom { prover, command, args } => {
                if prover == "HOL4" || prover == "hol4" {
                    HOL4Tactic::Custom(if args.is_empty() {
                        command.clone()
                    } else {
                        format!("{} {}", command, args.join(" "))
                    })
                } else {
                    // Map common tactics from other provers
                    match command.as_str() {
                        "auto" => HOL4Tactic::Metis(vec![]),
                        "blast" => HOL4Tactic::BBlast,
                        "simp" => HOL4Tactic::Simp(args.clone()),
                        "decide" => HOL4Tactic::Decide,
                        "arith" => HOL4Tactic::Arith,
                        _ => HOL4Tactic::Custom(command.clone()),
                    }
                }
            }
        }
    }

    /// Convert HOL4 tactic to universal Tactic
    fn hol4_to_tactic(tactic: &HOL4Tactic) -> Tactic {
        match tactic {
            HOL4Tactic::Rewrite(thms) => {
                if thms.len() == 1 {
                    Tactic::Rewrite(thms[0].clone())
                } else {
                    Tactic::Custom {
                        prover: "HOL4".to_string(),
                        command: "rw".to_string(),
                        args: thms.clone(),
                    }
                }
            }
            HOL4Tactic::Simp(_) => Tactic::Simplify,
            HOL4Tactic::FS(_) | HOL4Tactic::RFS(_) | HOL4Tactic::GS(_) => Tactic::Simplify,
            HOL4Tactic::Decide => Tactic::Custom {
                prover: "HOL4".to_string(),
                command: "DECIDE_TAC".to_string(),
                args: vec![],
            },
            HOL4Tactic::Arith => Tactic::Custom {
                prover: "HOL4".to_string(),
                command: "ARITH_TAC".to_string(),
                args: vec![],
            },
            HOL4Tactic::Cases(term) => Tactic::Cases(Self::hol4_to_term(term)),
            HOL4Tactic::Induct(var) => Tactic::Induction(Term::Var(var.clone())),
            HOL4Tactic::Strip | HOL4Tactic::Gen => Tactic::Intro(None),
            HOL4Tactic::IRule(thm) | HOL4Tactic::MatchMP(thm) => Tactic::Apply(thm.clone()),
            HOL4Tactic::Metis(_) => Tactic::Custom {
                prover: "HOL4".to_string(),
                command: "metis_tac".to_string(),
                args: vec![],
            },
            HOL4Tactic::Custom(cmd) => Tactic::Custom {
                prover: "HOL4".to_string(),
                command: cmd.clone(),
                args: vec![],
            },
            _ => Tactic::Custom {
                prover: "HOL4".to_string(),
                command: Self::format_tactic(tactic),
                args: vec![],
            },
        }
    }

    // ========================================================================
    // Formatting
    // ========================================================================

    /// Format HOL4 term as string
    fn format_term(term: &HOL4Term) -> String {
        match term {
            HOL4Term::Var { name, ty } | HOL4Term::Const { name, ty } => {
                if let Some(ty) = ty {
                    format!("({} : {})", name, Self::format_type(ty))
                } else {
                    name.clone()
                }
            }
            HOL4Term::App { func, arg } => {
                format!("({} {})", Self::format_term(func), Self::format_term(arg))
            }
            HOL4Term::Abs { var, var_type, body } => {
                let var_str = if let Some(ty) = var_type {
                    format!("({} : {})", var, Self::format_type(ty))
                } else {
                    var.clone()
                };
                format!("(\\{}. {})", var_str, Self::format_term(body))
            }
            HOL4Term::Comb { operator, left, right } => {
                format!("({} {} {})", Self::format_term(left), operator, Self::format_term(right))
            }
            HOL4Term::Cond { cond, then_branch, else_branch } => {
                format!("(if {} then {} else {})",
                    Self::format_term(cond),
                    Self::format_term(then_branch),
                    Self::format_term(else_branch))
            }
            HOL4Term::Let { bindings, body } => {
                let bindings_str: Vec<String> = bindings.iter()
                    .map(|(n, v)| format!("{} = {}", n, Self::format_term(v)))
                    .collect();
                format!("let {} in {}", bindings_str.join(" and "), Self::format_term(body))
            }
            HOL4Term::Quant { quantifier, var, var_type, body } => {
                let q = match quantifier {
                    HOL4Quantifier::Forall => "!",
                    HOL4Quantifier::Exists => "?",
                    HOL4Quantifier::ExistsUnique => "?!",
                    HOL4Quantifier::Choose => "@",
                };
                let var_str = if let Some(ty) = var_type {
                    format!("({} : {})", var, Self::format_type(ty))
                } else {
                    var.clone()
                };
                format!("({}{}. {})", q, var_str, Self::format_term(body))
            }
            HOL4Term::Numeral(n) => n.to_string(),
            HOL4Term::String(s) => format!("\"{}\"", s),
            HOL4Term::List(elements) => {
                let elems: Vec<String> = elements.iter()
                    .map(|e| Self::format_term(e))
                    .collect();
                format!("[{}]", elems.join("; "))
            }
            HOL4Term::Pair(fst, snd) => {
                format!("({}, {})", Self::format_term(fst), Self::format_term(snd))
            }
            HOL4Term::TypeAnnot { term, ty } => {
                format!("({} : {})", Self::format_term(term), Self::format_type(ty))
            }
        }
    }

    /// Format HOL4 type as string
    fn format_type(ty: &HOL4Type) -> String {
        match ty {
            HOL4Type::TyVar(name) | HOL4Type::TyCon(name) => name.clone(),
            HOL4Type::TyApp { constructor, args } => {
                if args.is_empty() {
                    constructor.clone()
                } else if args.len() == 1 {
                    format!("{} {}", Self::format_type(&args[0]), constructor)
                } else {
                    let args_str: Vec<String> = args.iter()
                        .map(|a| Self::format_type(a))
                        .collect();
                    format!("({}) {}", args_str.join(", "), constructor)
                }
            }
            HOL4Type::TyFun { domain, range } => {
                format!("({} -> {})", Self::format_type(domain), Self::format_type(range))
            }
            HOL4Type::TyProd(types) => {
                let types_str: Vec<String> = types.iter()
                    .map(|t| Self::format_type(t))
                    .collect();
                format!("({})", types_str.join(" # "))
            }
            HOL4Type::TySum { left, right } => {
                format!("({} + {})", Self::format_type(left), Self::format_type(right))
            }
        }
    }

    /// Format HOL4 tactic as SML code
    fn format_tactic(tactic: &HOL4Tactic) -> String {
        match tactic {
            HOL4Tactic::Rewrite(thms) => {
                if thms.is_empty() {
                    "rw[]".to_string()
                } else {
                    format!("rw[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::Simp(thms) => {
                if thms.is_empty() {
                    "simp[]".to_string()
                } else {
                    format!("simp[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::FS(thms) => {
                if thms.is_empty() {
                    "fs[]".to_string()
                } else {
                    format!("fs[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::RFS(thms) => {
                if thms.is_empty() {
                    "rfs[]".to_string()
                } else {
                    format!("rfs[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::GS(thms) => {
                if thms.is_empty() {
                    "gs[]".to_string()
                } else {
                    format!("gs[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::Decide => "DECIDE_TAC".to_string(),
            HOL4Tactic::Arith => "ARITH_TAC".to_string(),
            HOL4Tactic::Cases(term) => format!("Cases_on `{}`", Self::format_term(term)),
            HOL4Tactic::Induct(var) => format!("Induct_on `{}`", var),
            HOL4Tactic::CompleteInduct(var) => format!("completeInduct_on `{}`", var),
            HOL4Tactic::Strip => "STRIP_TAC".to_string(),
            HOL4Tactic::Gen => "gen_tac".to_string(),
            HOL4Tactic::ConjTac => "conj_tac".to_string(),
            HOL4Tactic::DisjTac(n) => format!("disj{}_tac", n),
            HOL4Tactic::Exists(term) => format!("EXISTS_TAC ``{}``", Self::format_term(term)),
            HOL4Tactic::IRule(thm) => format!("irule {}", thm),
            HOL4Tactic::MatchMP(thm) => format!("MATCH_MP_TAC {}", thm),
            HOL4Tactic::Assume(thm) => format!("assume_tac {}", thm),
            HOL4Tactic::FirstXAssum(inner) => {
                format!("first_x_assum ({})", Self::format_tactic(inner))
            }
            HOL4Tactic::Metis(thms) => {
                if thms.is_empty() {
                    "metis_tac[]".to_string()
                } else {
                    format!("metis_tac[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::BBlast => "blastLib.BBLAST_TAC".to_string(),
            HOL4Tactic::Word => "wordsLib.WORD_TAC".to_string(),
            HOL4Tactic::FMap => "fmapLib.FM_TAC".to_string(),
            HOL4Tactic::StringTac => "stringLib.STRING_TAC".to_string(),
            HOL4Tactic::AllTac => "ALL_TAC".to_string(),
            HOL4Tactic::NoTac => "NO_TAC".to_string(),
            HOL4Tactic::Then(t1, t2) => {
                format!("({} >> {})", Self::format_tactic(t1), Self::format_tactic(t2))
            }
            HOL4Tactic::OrElse(t1, t2) => {
                format!("({} ORELSE {})", Self::format_tactic(t1), Self::format_tactic(t2))
            }
            HOL4Tactic::Repeat(inner) => format!("REPEAT ({})", Self::format_tactic(inner)),
            HOL4Tactic::Try(inner) => format!("TRY ({})", Self::format_tactic(inner)),
            HOL4Tactic::Reverse => "REVERSE".to_string(),
            HOL4Tactic::PopAssum(inner) => {
                format!("pop_assum ({})", Self::format_tactic(inner))
            }
            HOL4Tactic::QSpecThen(term, inner) => {
                format!("qspec_then `{}` ({})", Self::format_term(term), Self::format_tactic(inner))
            }
            HOL4Tactic::OnceRewrite(thms) => {
                if thms.is_empty() {
                    "once_rewrite_tac[]".to_string()
                } else {
                    format!("once_rewrite_tac[{}]", thms.join(", "))
                }
            }
            HOL4Tactic::Eval => "EVAL_TAC".to_string(),
            HOL4Tactic::Custom(code) => code.clone(),
        }
    }
}

#[async_trait]
impl ProverBackend for Hol4Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::HOL4
    }

    async fn version(&self) -> Result<String> {
        let hol4_path = self.config.executable.clone();

        let output = Command::new(&hol4_path)
            .arg("--version")
            .output()
            .await
            .context("Failed to get HOL4 version")?;

        let version_output = String::from_utf8_lossy(&output.stdout);

        // Parse version from output
        let version = version_output
            .lines()
            .next()
            .unwrap_or("HOL4 (unknown version)")
            .trim()
            .to_string();

        Ok(version)
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await
            .context("Failed to read HOL4 file")?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut parser = HOL4Parser::new(content);
        let theory = parser.parse_theory()?;

        // Convert to universal ProofState
        let mut goals = Vec::new();
        let mut hypotheses = Vec::new();

        for decl in &theory.declarations {
            match decl {
                HOL4Declaration::Theorem { name, statement, .. } => {
                    goals.push(Goal {
                        id: name.clone(),
                        target: Self::hol4_to_term(statement),
                        hypotheses: hypotheses.clone(),
                    });
                }
                HOL4Declaration::Definition { name, body, .. } => {
                    hypotheses.push(Hypothesis {
                        name: name.clone(),
                        ty: Self::hol4_to_term(body),
                        body: None,
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
                meta.insert("prover".to_string(), serde_json::Value::String("HOL4".to_string()));
                meta
            },
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        let hol4_tactic = Self::tactic_to_hol4(tactic);
        let tactic_str = Self::format_tactic(&hol4_tactic);

        let mut session_guard = self.session.lock().await;

        let session = if session_guard.is_some() {
            session_guard.as_mut().unwrap()
        } else {
            *session_guard = Some(self.start_session().await?);
            session_guard.as_mut().unwrap()
        };

        // Apply the tactic
        let command = format!("e ({});", tactic_str);
        let response = Self::send_command(session, &command).await?;

        // Check for success
        let success = !response.contains("Exception") &&
                      !response.contains("error") &&
                      !response.contains("FAIL");

        if success {
            let mut new_state = state.clone();
            new_state.proof_script.push(tactic.clone());

            // Check if proof is complete
            if response.contains("Initial goal proved") || response.contains("Goal proved") {
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
        let mut output = String::new();

        // Get theory name from metadata
        let theory_name = state.metadata.get("theory")
            .and_then(|v| v.as_str())
            .unwrap_or("Exported");

        output.push_str(&format!("(* HOL4 Theory: {} *)\n\n", theory_name));
        output.push_str("open HolKernel boolLib bossLib;\n\n");
        output.push_str(&format!("val _ = new_theory \"{}\";\n\n", theory_name));

        // Export hypotheses as definitions
        for (i, goal) in state.goals.iter().enumerate() {
            for hyp in &goal.hypotheses {
                output.push_str(&format!("(* Hypothesis: {} *)\n", hyp.name));
                let hol4_ty = Self::term_to_hol4(&hyp.ty);
                output.push_str(&format!("val {}_def = Define `{} = {}`;\n\n",
                    hyp.name,
                    hyp.name,
                    Self::format_term(&hol4_ty)));
            }

            // Export goal as theorem
            let hol4_target = Self::term_to_hol4(&goal.target);
            output.push_str(&format!("(* Theorem {} *)\n", goal.id));
            output.push_str(&format!("Theorem {}:\n", goal.id));
            output.push_str(&format!("  ``{}``\n", Self::format_term(&hol4_target)));
            output.push_str("Proof\n");

            // Export proof script
            for tactic in &state.proof_script {
                let hol4_tactic = Self::tactic_to_hol4(tactic);
                output.push_str(&format!("  {} >>\n", Self::format_tactic(&hol4_tactic)));
            }
            output.push_str("  ALL_TAC\n");
            output.push_str("QED\n\n");
        }

        output.push_str("val _ = export_theory();\n");

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        // Analyze current goal
        if let Some(goal) = state.goals.first() {
            let target = &goal.target;

            // Simple heuristics based on goal structure
            match target {
                Term::Pi { .. } => {
                    // Universal quantification - suggest introduction
                    suggestions.push(Tactic::Intro(None));
                    suggestions.push(Tactic::Custom {
                        prover: "HOL4".to_string(),
                        command: "STRIP_TAC".to_string(),
                        args: vec![],
                    });
                    suggestions.push(Tactic::Custom {
                        prover: "HOL4".to_string(),
                        command: "gen_tac".to_string(),
                        args: vec![],
                    });
                }
                Term::App { func, .. } => {
                    if let Term::Const(name) = func.as_ref() {
                        match name.as_str() {
                            "/\\" | "∧" => {
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "conj_tac".to_string(),
                                    args: vec![],
                                });
                            }
                            "=" => {
                                suggestions.push(Tactic::Simplify);
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "rw[]".to_string(),
                                    args: vec![],
                                });
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "EVAL_TAC".to_string(),
                                    args: vec![],
                                });
                            }
                            "==>" | "⇒" => {
                                suggestions.push(Tactic::Intro(None));
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "STRIP_TAC".to_string(),
                                    args: vec![],
                                });
                            }
                            "<" | "<=" | ">" | ">=" => {
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "ARITH_TAC".to_string(),
                                    args: vec![],
                                });
                                suggestions.push(Tactic::Custom {
                                    prover: "HOL4".to_string(),
                                    command: "DECIDE_TAC".to_string(),
                                    args: vec![],
                                });
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }

        // Generic tactics that often work
        suggestions.push(Tactic::Simplify);
        suggestions.push(Tactic::Custom {
            prover: "HOL4".to_string(),
            command: "fs[]".to_string(),
            args: vec![],
        });
        suggestions.push(Tactic::Custom {
            prover: "HOL4".to_string(),
            command: "metis_tac[]".to_string(),
            args: vec![],
        });
        suggestions.push(Tactic::Custom {
            prover: "HOL4".to_string(),
            command: "EVAL_TAC".to_string(),
            args: vec![],
        });

        suggestions.dedup();
        suggestions.truncate(limit);

        Ok(suggestions)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        let mut session_guard = self.session.lock().await;

        let session = if session_guard.is_some() {
            session_guard.as_mut().unwrap()
        } else {
            *session_guard = Some(self.start_session().await?);
            session_guard.as_mut().unwrap()
        };

        // Use DB.match_string to search for theorems
        let command = format!("DB.match_string \"{}\";", pattern);
        let response = Self::send_command(session, &command).await?;

        // Parse results
        let mut results = Vec::new();
        for line in response.lines() {
            let line = line.trim();
            if line.starts_with("|-") || line.contains("_def") || line.contains("_thm") {
                // Extract theorem name from result
                if let Some(name) = line.split_whitespace().last() {
                    results.push(name.to_string());
                }
            }
        }

        Ok(results)
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
    fn test_parse_simple_term() {
        let mut parser = HOL4Parser::new("x");
        let term = parser.parse_term().unwrap();
        match term {
            HOL4Term::Var { name, .. } => assert_eq!(name, "x"),
            _ => panic!("Expected variable"),
        }
    }

    #[test]
    fn test_parse_numeral() {
        let mut parser = HOL4Parser::new("42");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, HOL4Term::Numeral(42));
    }

    #[test]
    fn test_parse_application() {
        let mut parser = HOL4Parser::new("f x");
        let term = parser.parse_term().unwrap();
        match term {
            HOL4Term::App { func, arg } => {
                match *func {
                    HOL4Term::Var { name, .. } => assert_eq!(name, "f"),
                    _ => panic!("Expected function variable"),
                }
                match *arg {
                    HOL4Term::Var { name, .. } => assert_eq!(name, "x"),
                    _ => panic!("Expected argument variable"),
                }
            }
            _ => panic!("Expected application"),
        }
    }

    #[test]
    fn test_parse_lambda() {
        let mut parser = HOL4Parser::new("\\x. x");
        let term = parser.parse_term().unwrap();
        match term {
            HOL4Term::Abs { var, body, .. } => {
                assert_eq!(var, "x");
                match *body {
                    HOL4Term::Var { name, .. } => assert_eq!(name, "x"),
                    _ => panic!("Expected variable in body"),
                }
            }
            _ => panic!("Expected lambda abstraction"),
        }
    }

    #[test]
    fn test_parse_forall() {
        let mut parser = HOL4Parser::new("!x. P x");
        let term = parser.parse_term().unwrap();
        match term {
            HOL4Term::Quant { quantifier, var, .. } => {
                assert_eq!(quantifier, HOL4Quantifier::Forall);
                assert_eq!(var, "x");
            }
            _ => panic!("Expected forall quantification"),
        }
    }

    #[test]
    fn test_parse_exists() {
        let mut parser = HOL4Parser::new("?x. P x");
        let term = parser.parse_term().unwrap();
        match term {
            HOL4Term::Quant { quantifier, var, .. } => {
                assert_eq!(quantifier, HOL4Quantifier::Exists);
                assert_eq!(var, "x");
            }
            _ => panic!("Expected exists quantification"),
        }
    }

    #[test]
    fn test_parse_type_bool() {
        let mut parser = HOL4Parser::new("bool");
        let ty = parser.parse_type().unwrap();
        assert_eq!(ty, HOL4Type::TyCon("bool".to_string()));
    }

    #[test]
    fn test_parse_type_num() {
        let mut parser = HOL4Parser::new("num");
        let ty = parser.parse_type().unwrap();
        assert_eq!(ty, HOL4Type::TyCon("num".to_string()));
    }

    #[test]
    fn test_parse_type_arrow() {
        let mut parser = HOL4Parser::new("num -> bool");
        let ty = parser.parse_type().unwrap();
        match ty {
            HOL4Type::TyFun { domain, range } => {
                assert_eq!(*domain, HOL4Type::TyCon("num".to_string()));
                assert_eq!(*range, HOL4Type::TyCon("bool".to_string()));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_term_to_universal() {
        let term = HOL4Term::Numeral(42);
        let universal = Hol4Backend::hol4_to_term(&term);
        match universal {
            Term::Const(name) => assert_eq!(name, "42"),
            _ => panic!("Expected constant"),
        }
    }

    #[test]
    fn test_hol4_backend_creation() {
        let backend = Hol4Backend::new(ProverConfig::default());
        assert_eq!(backend.kind(), ProverKind::HOL4);
    }

    #[test]
    fn test_hol4_config() {
        let config = ProverConfig {
            executable: PathBuf::from("/usr/bin/hol4"),
            ..Default::default()
        };
        let backend = Hol4Backend::new(config);
        assert_eq!(backend.config().executable, PathBuf::from("/usr/bin/hol4"));
    }
}
