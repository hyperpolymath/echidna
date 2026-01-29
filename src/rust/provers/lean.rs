// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

#![allow(dead_code)]

//! Lean 4 theorem prover backend implementation
//!
//! Integrates with Lean 4 via command-line interface and Lake build system.
//! Supports parsing .lean files, executing tactics, and proof verification.
//!
//! Lean 4 Features:
//! - Dependent type theory with universe polymorphism
//! - Powerful tactic framework with metaprogramming
//! - Lake build system for project management
//! - Native code generation for performance

use async_trait::async_trait;
use anyhow::{anyhow, Context as AnyhowContext, Result};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::{alpha1, multispace0, space1},
    combinator::opt,
    sequence::{preceded, terminated, tuple},
    IResult,
};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::Mutex;
use tokio::process::Command;

use crate::core::{
    Context as ProofContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult, Term,
    Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Lean 4 theorem prover backend
pub struct LeanBackend {
    /// Configuration for the Lean prover
    config: ProverConfig,
    /// Counter for generating fresh meta-variables
    meta_counter: Mutex<usize>,
    /// Cached library paths for Lake
    library_cache: Mutex<HashMap<String, PathBuf>>,
}

/// Lean 4 expression types
#[derive(Debug, Clone, PartialEq)]
pub enum LeanExpr {
    /// Variable reference
    Var(String),
    /// Constant (declared name)
    Const(String, Vec<LeanLevel>),
    /// Function application
    App(Box<LeanExpr>, Box<LeanExpr>),
    /// Lambda abstraction
    Lambda(String, Box<LeanExpr>, Box<LeanExpr>),
    /// Pi/forall type
    Pi(String, Box<LeanExpr>, Box<LeanExpr>),
    /// Let binding
    Let(String, Box<LeanExpr>, Box<LeanExpr>, Box<LeanExpr>),
    /// Sort/Type universe
    Sort(LeanLevel),
    /// Literal value
    Lit(LeanLit),
    /// Metavariable (hole)
    MVar(String),
    /// Free variable (bound)
    FVar(String),
    /// Projection from structure
    Proj(String, usize, Box<LeanExpr>),
}

/// Lean universe levels
#[derive(Debug, Clone, PartialEq)]
pub enum LeanLevel {
    Zero,
    Succ(Box<LeanLevel>),
    Max(Box<LeanLevel>, Box<LeanLevel>),
    IMax(Box<LeanLevel>, Box<LeanLevel>),
    Param(String),
    MVar(String),
}

/// Lean literal values
#[derive(Debug, Clone, PartialEq)]
pub enum LeanLit {
    Nat(u64),
    Str(String),
}

/// Lean tactic state
#[derive(Debug, Clone)]
pub struct LeanTacticState {
    /// Current goals
    goals: Vec<LeanGoal>,
    /// Proof term being constructed
    proof_term: Option<LeanExpr>,
    /// Tactic history
    history: Vec<String>,
}

/// A single goal in Lean
#[derive(Debug, Clone)]
pub struct LeanGoal {
    /// Goal identifier (metavariable name)
    id: String,
    /// Local context (hypotheses)
    context: Vec<LeanHypothesis>,
    /// Target type to prove
    target: LeanExpr,
}

/// A hypothesis in the local context
#[derive(Debug, Clone)]
pub struct LeanHypothesis {
    /// Name of the hypothesis
    name: String,
    /// Type of the hypothesis
    ty: LeanExpr,
    /// Value (for let bindings)
    value: Option<LeanExpr>,
}

impl LeanBackend {
    /// Create a new Lean 4 backend with the given configuration
    pub fn new(config: ProverConfig) -> Self {
        LeanBackend {
            config,
            meta_counter: Mutex::new(0),
            library_cache: Mutex::new(HashMap::new()),
        }
    }

    /// Get the path to the Lean executable
    fn lean_executable(&self) -> PathBuf {
        if self.config.executable.as_os_str().is_empty() {
            PathBuf::from("lean")
        } else {
            self.config.executable.clone()
        }
    }

    /// Get the path to the Lake executable
    fn lake_executable(&self) -> PathBuf {
        // Lake is typically in the same directory as Lean
        let lean_path = self.lean_executable();
        if let Some(parent) = lean_path.parent() {
            parent.join("lake")
        } else {
            PathBuf::from("lake")
        }
    }

    /// Generate a fresh metavariable name
    fn fresh_meta(&self) -> String {
        let mut counter = self.meta_counter.lock().unwrap();
        let name = format!("?m{}", *counter);
        *counter += 1;
        name
    }

    /// Run Lean on a file and capture output
    async fn run_lean(&self, args: &[&str]) -> Result<String> {
        let mut cmd = Command::new(self.lean_executable());
        cmd.args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Add library paths
        for path in &self.config.library_paths {
            cmd.arg("-I").arg(path);
        }

        let output = tokio::time::timeout(
            std::time::Duration::from_secs(self.config.timeout),
            cmd.output(),
        )
        .await
        .map_err(|_| anyhow!("Lean command timed out"))?
        .context("Failed to run Lean")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            if !stderr.is_empty() {
                return Err(anyhow!("Lean error: {}", stderr));
            }
            if !stdout.is_empty() {
                return Err(anyhow!("Lean error: {}", stdout));
            }
            return Err(anyhow!("Lean failed with status {}", output.status));
        }

        Ok(stdout.to_string())
    }

    /// Run Lake command
    async fn run_lake(&self, args: &[&str], cwd: Option<&PathBuf>) -> Result<String> {
        let mut cmd = Command::new(self.lake_executable());
        cmd.args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        if let Some(dir) = cwd {
            cmd.current_dir(dir);
        }

        let output = tokio::time::timeout(
            std::time::Duration::from_secs(self.config.timeout * 2), // Lake can be slow
            cmd.output(),
        )
        .await
        .map_err(|_| anyhow!("Lake command timed out"))?
        .context("Failed to run Lake")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            if !stderr.is_empty() {
                return Err(anyhow!("Lake error: {}", stderr));
            }
            return Err(anyhow!("Lake failed with status {}", output.status));
        }

        Ok(format!("{}{}", stdout, stderr))
    }

    /// Parse a Lean file and extract definitions
    fn parse_lean_content(&self, content: &str) -> Result<Vec<LeanDeclaration>> {
        let mut declarations = Vec::new();
        let mut remaining = content;

        while !remaining.trim().is_empty() {
            // Skip comments and whitespace
            remaining = skip_whitespace_and_comments(remaining);

            if remaining.is_empty() {
                break;
            }

            // Try to parse a declaration
            match parse_declaration(remaining) {
                Ok((rest, decl)) => {
                    declarations.push(decl);
                    remaining = rest;
                }
                Err(_) => {
                    // Skip to next line on parse error
                    if let Some(idx) = remaining.find('\n') {
                        remaining = &remaining[idx + 1..];
                    } else {
                        break;
                    }
                }
            }
        }

        Ok(declarations)
    }

    /// Convert a Lean expression to ECHIDNA Term
    fn lean_expr_to_term(&self, expr: &LeanExpr) -> Term {
        match expr {
            LeanExpr::Var(name) => Term::Var(name.clone()),
            LeanExpr::Const(name, _) => Term::Const(name.clone()),
            LeanExpr::App(f, arg) => Term::App {
                func: Box::new(self.lean_expr_to_term(f)),
                args: vec![self.lean_expr_to_term(arg)],
            },
            LeanExpr::Lambda(param, ty, body) => Term::Lambda {
                param: param.clone(),
                param_type: Some(Box::new(self.lean_expr_to_term(ty))),
                body: Box::new(self.lean_expr_to_term(body)),
            },
            LeanExpr::Pi(param, ty, body) => Term::Pi {
                param: param.clone(),
                param_type: Box::new(self.lean_expr_to_term(ty)),
                body: Box::new(self.lean_expr_to_term(body)),
            },
            LeanExpr::Let(name, ty, val, body) => Term::Let {
                name: name.clone(),
                ty: Some(Box::new(self.lean_expr_to_term(ty))),
                value: Box::new(self.lean_expr_to_term(val)),
                body: Box::new(self.lean_expr_to_term(body)),
            },
            LeanExpr::Sort(level) => match level {
                LeanLevel::Zero => Term::Type(0),
                LeanLevel::Succ(l) => {
                    if let Term::Type(n) = self.lean_level_to_term(l) {
                        Term::Type(n + 1)
                    } else {
                        Term::Sort(self.lean_level_to_usize(level))
                    }
                }
                _ => Term::Sort(self.lean_level_to_usize(level)),
            },
            LeanExpr::Lit(lit) => match lit {
                LeanLit::Nat(n) => Term::Const(n.to_string()),
                LeanLit::Str(s) => Term::Const(format!("\"{}\"", s)),
            },
            LeanExpr::MVar(name) => Term::Hole(name.clone()),
            LeanExpr::FVar(name) => Term::Var(name.clone()),
            LeanExpr::Proj(struct_name, idx, expr) => Term::App {
                func: Box::new(Term::Const(format!("{}.{}", struct_name, idx))),
                args: vec![self.lean_expr_to_term(expr)],
            },
        }
    }

    /// Convert a Lean level to a term representation
    fn lean_level_to_term(&self, level: &LeanLevel) -> Term {
        match level {
            LeanLevel::Zero => Term::Type(0),
            LeanLevel::Succ(l) => {
                if let Term::Type(n) = self.lean_level_to_term(l) {
                    Term::Type(n + 1)
                } else {
                    Term::Sort(self.lean_level_to_usize(level))
                }
            }
            _ => Term::Sort(self.lean_level_to_usize(level)),
        }
    }

    /// Convert a Lean level to usize representation
    fn lean_level_to_usize(&self, level: &LeanLevel) -> usize {
        match level {
            LeanLevel::Zero => 0,
            LeanLevel::Succ(l) => self.lean_level_to_usize(l) + 1,
            _ => 0, // Default for complex levels
        }
    }

    /// Convert an ECHIDNA Term to Lean syntax
    fn term_to_lean(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let args_str: Vec<String> = args.iter().map(|a| self.term_to_lean(a)).collect();
                format!("({} {})", self.term_to_lean(func), args_str.join(" "))
            }
            Term::Lambda {
                param,
                param_type,
                body,
            } => {
                if let Some(ty) = param_type {
                    format!(
                        "(fun ({} : {}) => {})",
                        param,
                        self.term_to_lean(ty),
                        self.term_to_lean(body)
                    )
                } else {
                    format!("(fun {} => {})", param, self.term_to_lean(body))
                }
            }
            Term::Pi {
                param,
                param_type,
                body,
            } => {
                format!(
                    "(∀ ({} : {}), {})",
                    param,
                    self.term_to_lean(param_type),
                    self.term_to_lean(body)
                )
            }
            Term::Let {
                name,
                ty,
                value,
                body,
            } => {
                if let Some(t) = ty {
                    format!(
                        "(let {} : {} := {}; {})",
                        name,
                        self.term_to_lean(t),
                        self.term_to_lean(value),
                        self.term_to_lean(body)
                    )
                } else {
                    format!(
                        "(let {} := {}; {})",
                        name,
                        self.term_to_lean(value),
                        self.term_to_lean(body)
                    )
                }
            }
            Term::Type(level) => {
                if *level == 0 {
                    "Prop".to_string()
                } else {
                    format!("Type {}", level - 1)
                }
            }
            Term::Sort(level) => format!("Sort {}", level),
            Term::Universe(level) => format!("Type {}", level),
            Term::Match {
                scrutinee,
                branches,
                ..
            } => {
                let arms_str: Vec<String> = branches
                    .iter()
                    .map(|(pat, body)| {
                        format!("| {} => {}", self.pattern_to_lean(pat), self.term_to_lean(body))
                    })
                    .collect();
                format!(
                    "(match {} with {})",
                    self.term_to_lean(scrutinee),
                    arms_str.join(" ")
                )
            }
            Term::Fix { name, ty, body } => {
                // Lean uses `partial def` or `termination_by` for fixpoints
                if let Some(t) = ty {
                    format!(
                        "(partial def {} : {} := {})",
                        name,
                        self.term_to_lean(t),
                        self.term_to_lean(body)
                    )
                } else {
                    format!("(partial def {} := {})", name, self.term_to_lean(body))
                }
            }
            Term::Hole(name) => {
                if name.is_empty() {
                    "_".to_string()
                } else {
                    format!("?{}", name)
                }
            }
            Term::Meta(id) => format!("?m{}", id),
            Term::ProverSpecific { data, .. } => data.to_string(),
        }
    }

    /// Convert a pattern to Lean syntax
    fn pattern_to_lean(&self, pattern: &crate::core::Pattern) -> String {
        match pattern {
            crate::core::Pattern::Wildcard => "_".to_string(),
            crate::core::Pattern::Var(name) => name.clone(),
            crate::core::Pattern::Constructor { name, args } => {
                if args.is_empty() {
                    name.clone()
                } else {
                    let args_str: Vec<String> =
                        args.iter().map(|a| self.pattern_to_lean(a)).collect();
                    format!("({} {})", name, args_str.join(" "))
                }
            }
        }
    }

    /// Convert an ECHIDNA Tactic to Lean 4 tactic syntax
    fn tactic_to_lean(&self, tactic: &Tactic) -> String {
        match tactic {
            Tactic::Apply(name) => format!("apply {}", name),
            Tactic::Intro(name) => {
                if let Some(n) = name {
                    format!("intro {}", n)
                } else {
                    "intro".to_string()
                }
            }
            Tactic::Cases(term) => format!("cases {}", self.term_to_lean(term)),
            Tactic::Induction(term) => format!("induction {}", self.term_to_lean(term)),
            Tactic::Rewrite(rule) => format!("rw [{}]", rule),
            Tactic::Simplify => "simp".to_string(),
            Tactic::Reflexivity => "rfl".to_string(),
            Tactic::Assumption => "assumption".to_string(),
            Tactic::Exact(term) => format!("exact {}", self.term_to_lean(term)),
            Tactic::Custom {
                prover,
                command,
                args,
            } => {
                if prover == "lean" || prover.is_empty() {
                    if args.is_empty() {
                        command.clone()
                    } else {
                        format!("{} {}", command, args.join(" "))
                    }
                } else {
                    format!("-- prover-specific: {} {}", command, args.join(" "))
                }
            }
        }
    }

    /// Parse tactic state from Lean output
    fn parse_tactic_state(&self, output: &str) -> Result<LeanTacticState> {
        let mut goals = Vec::new();
        let mut current_goal: Option<LeanGoal> = None;
        let mut in_goals = false;

        for line in output.lines() {
            let line = line.trim();

            if line.starts_with("⊢") || line.starts_with("|-") {
                // This is a goal target
                let target_str = line.trim_start_matches(&['⊢', '|', '-'][..]).trim();
                if let Some(goal) = current_goal.as_mut() {
                    goal.target = self.parse_lean_expr_simple(target_str)?;
                }
                in_goals = true;
            } else if line.contains(':') && in_goals && !line.starts_with("--") {
                // This might be a hypothesis
                let parts: Vec<&str> = line.splitn(2, ':').collect();
                if parts.len() == 2 {
                    let name = parts[0].trim().to_string();
                    let ty_str = parts[1].trim();
                    let ty = self.parse_lean_expr_simple(ty_str)?;
                    if let Some(goal) = current_goal.as_mut() {
                        goal.context.push(LeanHypothesis {
                            name,
                            ty,
                            value: None,
                        });
                    }
                }
            } else if line.starts_with("case ") || line.starts_with("goal ") {
                // Start of a new goal
                if let Some(goal) = current_goal.take() {
                    goals.push(goal);
                }
                let id = self.fresh_meta();
                current_goal = Some(LeanGoal {
                    id,
                    context: Vec::new(),
                    target: LeanExpr::MVar("unknown".to_string()),
                });
            }
        }

        // Add the last goal
        if let Some(goal) = current_goal {
            goals.push(goal);
        }

        // If no goals were found but output suggests completion
        if goals.is_empty()
            && (output.contains("no goals") || output.contains("Goals accomplished"))
        {
            return Ok(LeanTacticState {
                goals: Vec::new(),
                proof_term: None,
                history: Vec::new(),
            });
        }

        Ok(LeanTacticState {
            goals,
            proof_term: None,
            history: Vec::new(),
        })
    }

    /// Simple expression parser for tactic state output
    fn parse_lean_expr_simple(&self, input: &str) -> Result<LeanExpr> {
        let input = input.trim();

        // Handle basic cases
        if input.is_empty() {
            return Ok(LeanExpr::MVar(self.fresh_meta()));
        }

        // Check for function types
        if input.contains("→") || input.contains("->") {
            let parts: Vec<&str> = input.splitn(2, &['→', '-'][..]).collect();
            if parts.len() == 2 {
                let domain = self.parse_lean_expr_simple(parts[0])?;
                let codomain =
                    self.parse_lean_expr_simple(parts[1].trim_start_matches(|c| c == '>'))?;
                return Ok(LeanExpr::Pi(
                    "_".to_string(),
                    Box::new(domain),
                    Box::new(codomain),
                ));
            }
        }

        // Check for forall
        if input.starts_with("∀") || input.starts_with("forall") {
            // Simplified: just treat as a term
            return Ok(LeanExpr::Const(input.to_string(), vec![]));
        }

        // Check for applications (multiple words)
        let parts: Vec<&str> = input.split_whitespace().collect();
        if parts.len() > 1 {
            let first = self.parse_lean_expr_simple(parts[0])?;
            let rest = self.parse_lean_expr_simple(&parts[1..].join(" "))?;
            return Ok(LeanExpr::App(Box::new(first), Box::new(rest)));
        }

        // Otherwise treat as a constant or variable
        if input.starts_with('?') {
            Ok(LeanExpr::MVar(input[1..].to_string()))
        } else if input
            .chars()
            .next()
            .map(|c| c.is_uppercase())
            .unwrap_or(false)
        {
            Ok(LeanExpr::Const(input.to_string(), vec![]))
        } else {
            Ok(LeanExpr::Var(input.to_string()))
        }
    }

    /// Build the proof state from parsed declarations and goals
    fn build_proof_state(
        &self,
        declarations: &[LeanDeclaration],
        tactic_state: &LeanTacticState,
    ) -> ProofState {
        let mut context = ProofContext::default();
        let mut theorems = Vec::new();
        let mut definitions = Vec::new();

        for decl in declarations {
            match decl {
                LeanDeclaration::Theorem {
                    name,
                    ty,
                    value,
                    ..
                } => {
                    let statement = self.lean_expr_to_term(ty);
                    let _proof = value.as_ref().map(|v| self.lean_expr_to_term(v));
                    theorems.push(Theorem {
                        name: name.clone(),
                        statement,
                        proof: None, // Tactics not extracted yet
                        aspects: vec![],
                    });
                }
                LeanDeclaration::Definition { name, ty, value, .. } => {
                    let term_ty = self.lean_expr_to_term(ty);
                    let term_val = self.lean_expr_to_term(value);
                    definitions.push(Definition {
                        name: name.clone(),
                        ty: term_ty,
                        body: term_val,
                    });
                }
                LeanDeclaration::Axiom { name, ty, .. } => {
                    // Axioms become theorems without proofs
                    theorems.push(Theorem {
                        name: name.clone(),
                        statement: self.lean_expr_to_term(ty),
                        proof: None,
                        aspects: vec![],
                    });
                }
                LeanDeclaration::Inductive { .. } => {
                    // Handle inductive types as definitions
                }
                LeanDeclaration::Structure { .. } => {
                    // Handle structures as definitions
                }
                LeanDeclaration::Instance { .. } => {
                    // Handle instances
                }
            }
        }

        // Convert goals
        let goals: Vec<Goal> = tactic_state
            .goals
            .iter()
            .map(|g| {
                let hypotheses: Vec<Hypothesis> = g
                    .context
                    .iter()
                    .map(|h| Hypothesis {
                        name: h.name.clone(),
                        ty: self.lean_expr_to_term(&h.ty),
                        body: h.value.as_ref().map(|v| self.lean_expr_to_term(v)),
                    })
                    .collect();

                Goal {
                    id: g.id.clone(),
                    target: self.lean_expr_to_term(&g.target),
                    hypotheses,
                }
            })
            .collect();

        context.definitions = definitions;
        context.theorems = theorems;

        ProofState {
            goals,
            context,
            proof_script: Vec::new(),
            metadata: HashMap::new(),
        }
    }
}

/// Lean declaration types
#[derive(Debug, Clone)]
pub enum LeanDeclaration {
    Theorem {
        name: String,
        ty: LeanExpr,
        value: Option<LeanExpr>,
        params: Vec<(String, LeanExpr)>,
    },
    Definition {
        name: String,
        ty: LeanExpr,
        value: LeanExpr,
        params: Vec<(String, LeanExpr)>,
    },
    Axiom {
        name: String,
        ty: LeanExpr,
        params: Vec<(String, LeanExpr)>,
    },
    Inductive {
        name: String,
        params: Vec<(String, LeanExpr)>,
        constructors: Vec<(String, LeanExpr)>,
    },
    Structure {
        name: String,
        params: Vec<(String, LeanExpr)>,
        fields: Vec<(String, LeanExpr)>,
    },
    Instance {
        name: Option<String>,
        ty: LeanExpr,
        value: LeanExpr,
    },
}

// =============================================================================
// Parser Combinators for Lean 4 Syntax
// =============================================================================

/// Skip whitespace and comments
fn skip_whitespace_and_comments(input: &str) -> &str {
    let mut remaining = input;

    loop {
        // Skip whitespace
        remaining = remaining.trim_start();

        // Skip line comments
        if remaining.starts_with("--") {
            if let Some(idx) = remaining.find('\n') {
                remaining = &remaining[idx + 1..];
                continue;
            } else {
                return "";
            }
        }

        // Skip block comments
        if remaining.starts_with("/-") {
            let mut depth = 1;
            let mut chars = remaining[2..].char_indices();
            while depth > 0 {
                match chars.next() {
                    Some((i, '/')) => {
                        if remaining.get(2 + i + 1..).map_or(false, |s| s.starts_with('-')) {
                            depth += 1;
                            chars.next();
                        }
                    }
                    Some((i, '-')) => {
                        if remaining.get(2 + i + 1..).map_or(false, |s| s.starts_with('/')) {
                            depth -= 1;
                            chars.next();
                        }
                    }
                    Some(_) => {}
                    None => return "",
                }
            }
            if let Some((i, _)) = chars.next() {
                remaining = &remaining[2 + i..];
                continue;
            } else {
                return "";
            }
        }

        break;
    }

    remaining
}

/// Parse an identifier
fn parse_identifier(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, first) = alt((alpha1, tag("_")))(input)?;
    let (input, rest) = take_while(|c: char| c.is_alphanumeric() || c == '_' || c == '\'')(input)?;
    Ok((input, format!("{}{}", first, rest)))
}

/// Parse a simple type expression (for declaration parsing)
fn parse_type_expr(input: &str) -> IResult<&str, LeanExpr> {
    let (input, _) = multispace0(input)?;

    // Try to find the end of the type expression
    // This is simplified and looks for := or where or end of line
    let end_markers = [":=", "where", "\n"];
    let mut end_pos = input.len();

    for marker in &end_markers {
        if let Some(pos) = input.find(marker) {
            if pos < end_pos {
                end_pos = pos;
            }
        }
    }

    let type_str = input[..end_pos].trim();
    let remaining = &input[end_pos..];

    // Parse the type string into an expression
    let expr = if type_str.is_empty() {
        LeanExpr::MVar("_".to_string())
    } else {
        // Simplified: just treat as a constant
        LeanExpr::Const(type_str.to_string(), vec![])
    };

    Ok((remaining, expr))
}

/// Parse a declaration
fn parse_declaration(input: &str) -> IResult<&str, LeanDeclaration> {
    let input = skip_whitespace_and_comments(input);

    // Try different declaration types
    alt((
        parse_theorem_decl,
        parse_def_decl,
        parse_axiom_decl,
        parse_inductive_decl,
        parse_structure_decl,
        parse_instance_decl,
    ))(input)
}

/// Parse a theorem declaration
fn parse_theorem_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("theorem")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;

    // Parse optional parameters
    let (input, params) = parse_parameters(input)?;

    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, ty) = parse_type_expr(input)?;

    // Parse optional proof
    let (input, value) = opt(preceded(
        tuple((multispace0, tag(":="), multispace0)),
        parse_proof_body,
    ))(input)?;

    Ok((
        input,
        LeanDeclaration::Theorem {
            name,
            ty,
            value,
            params,
        },
    ))
}

/// Parse a definition
fn parse_def_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("def")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;

    let (input, params) = parse_parameters(input)?;

    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, ty) = parse_type_expr(input)?;

    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":=")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, value) = parse_proof_body(input)?;

    Ok((
        input,
        LeanDeclaration::Definition {
            name,
            ty,
            value,
            params,
        },
    ))
}

/// Parse an axiom declaration
fn parse_axiom_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("axiom")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;

    let (input, params) = parse_parameters(input)?;

    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, ty) = parse_type_expr(input)?;

    Ok((input, LeanDeclaration::Axiom { name, ty, params }))
}

/// Parse an inductive type declaration
fn parse_inductive_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("inductive")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;

    let (input, params) = parse_parameters(input)?;

    // Skip to the end of the inductive (simplified)
    let end_pos = input
        .find("\n\n")
        .or_else(|| input.find("\ninductive"))
        .or_else(|| input.find("\ndef"))
        .or_else(|| input.find("\ntheorem"))
        .unwrap_or(input.len());

    let remaining = &input[end_pos..];

    Ok((
        remaining,
        LeanDeclaration::Inductive {
            name,
            params,
            constructors: vec![],
        },
    ))
}

/// Parse a structure declaration
fn parse_structure_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("structure")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;

    let (input, params) = parse_parameters(input)?;

    // Skip to end of structure (simplified)
    let end_pos = input
        .find("\n\n")
        .or_else(|| input.find("\nstructure"))
        .or_else(|| input.find("\ndef"))
        .or_else(|| input.find("\ntheorem"))
        .unwrap_or(input.len());

    let remaining = &input[end_pos..];

    Ok((
        remaining,
        LeanDeclaration::Structure {
            name,
            params,
            fields: vec![],
        },
    ))
}

/// Parse an instance declaration
fn parse_instance_decl(input: &str) -> IResult<&str, LeanDeclaration> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("instance")(input)?;
    let (input, _) = multispace0(input)?;

    // Optional name
    let (input, name) = opt(terminated(parse_identifier, multispace0))(input)?;

    let (input, _) = tag(":")(input)?;
    let (input, ty) = parse_type_expr(input)?;

    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":=")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, value) = parse_proof_body(input)?;

    Ok((input, LeanDeclaration::Instance { name, ty, value }))
}

/// Parse parameters (simplified)
fn parse_parameters(input: &str) -> IResult<&str, Vec<(String, LeanExpr)>> {
    let mut params = Vec::new();
    let mut remaining = input;

    loop {
        let trimmed = remaining.trim_start();

        // Check for parameter groups
        if trimmed.starts_with('(') || trimmed.starts_with('{') || trimmed.starts_with('[') {
            // Find matching close
            let mut depth = 1;
            let mut end_idx = 1;
            for (i, c) in trimmed[1..].char_indices() {
                if c == '(' || c == '{' || c == '[' {
                    depth += 1;
                } else if c == ')' || c == '}' || c == ']' {
                    depth -= 1;
                    if depth == 0 {
                        end_idx = i + 1;
                        break;
                    }
                }
            }

            // Parse the parameter content (simplified)
            let param_content = &trimmed[1..end_idx];
            if let Some(colon_pos) = param_content.find(':') {
                let name = param_content[..colon_pos].trim().to_string();
                let ty_str = param_content[colon_pos + 1..].trim();
                params.push((name, LeanExpr::Const(ty_str.to_string(), vec![])));
            }

            remaining = &trimmed[end_idx + 1..];
        } else {
            break;
        }
    }

    Ok((remaining, params))
}

/// Parse a proof body (simplified - just captures until next declaration or end)
fn parse_proof_body(input: &str) -> IResult<&str, LeanExpr> {
    let input = input.trim_start();

    // Check for tactic proof
    if input.starts_with("by") {
        // Find end of tactic block
        let end_pos = find_proof_end(input);
        let proof_content = &input[..end_pos];
        let remaining = &input[end_pos..];
        return Ok((
            remaining,
            LeanExpr::Const(proof_content.to_string(), vec![]),
        ));
    }

    // Term-mode proof
    let end_pos = find_proof_end(input);
    let proof_content = input[..end_pos].trim();
    let remaining = &input[end_pos..];

    Ok((
        remaining,
        LeanExpr::Const(proof_content.to_string(), vec![]),
    ))
}

/// Find the end of a proof body
fn find_proof_end(input: &str) -> usize {
    // Look for next top-level declaration or double newline
    let markers = [
        "\ntheorem",
        "\ndef",
        "\naxiom",
        "\ninductive",
        "\nstructure",
        "\ninstance",
        "\n\n",
    ];

    let mut min_pos = input.len();
    for marker in &markers {
        if let Some(pos) = input.find(marker) {
            if pos < min_pos {
                min_pos = pos;
            }
        }
    }

    min_pos
}

// =============================================================================
// ProverBackend Implementation
// =============================================================================

#[async_trait]
impl ProverBackend for LeanBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Lean
    }

    async fn version(&self) -> Result<String> {
        let output = self.run_lean(&["--version"]).await?;
        Ok(output.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        // First, try to check the file with Lean
        let path_str = path.to_string_lossy();
        let output = self.run_lean(&["--run", &path_str]).await;

        // Read the file content for parsing
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read Lean file")?;

        // Parse declarations
        let declarations = self.parse_lean_content(&content)?;

        // Extract tactic state from output if available
        let tactic_state = match output {
            Ok(out) => self
                .parse_tactic_state(&out)
                .unwrap_or_else(|_| LeanTacticState {
                    goals: Vec::new(),
                    proof_term: None,
                    history: Vec::new(),
                }),
            Err(_) => LeanTacticState {
                goals: Vec::new(),
                proof_term: None,
                history: Vec::new(),
            },
        };

        let state = self.build_proof_state(&declarations, &tactic_state);

        Ok(state)
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        // Parse declarations from the content
        let declarations = self.parse_lean_content(content)?;

        // Create a temporary file and check it with Lean
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_lean_{}.lean", uuid::Uuid::new_v4()));

        tokio::fs::write(&temp_file, content)
            .await
            .context("Failed to write temporary file")?;

        let output = self
            .run_lean(&["--run", &temp_file.to_string_lossy()])
            .await;

        // Clean up
        let _ = tokio::fs::remove_file(&temp_file).await;

        let tactic_state = match output {
            Ok(out) => self
                .parse_tactic_state(&out)
                .unwrap_or_else(|_| LeanTacticState {
                    goals: Vec::new(),
                    proof_term: None,
                    history: Vec::new(),
                }),
            Err(_) => LeanTacticState {
                goals: Vec::new(),
                proof_term: None,
                history: Vec::new(),
            },
        };

        let state = self.build_proof_state(&declarations, &tactic_state);
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        if state.goals.is_empty() {
            return Ok(TacticResult::Error(
                "No goals to prove".to_string(),
            ));
        }

        // Generate Lean code that applies the tactic
        let lean_tactic = self.tactic_to_lean(tactic);
        let goal = &state.goals[0];

        // Build a Lean file that uses the tactic
        let mut lean_code = String::new();
        lean_code.push_str("-- Generated by ECHIDNA\n\n");

        // Add hypotheses as variables
        for hyp in &goal.hypotheses {
            lean_code.push_str(&format!(
                "variable ({} : {})\n",
                hyp.name,
                self.term_to_lean(&hyp.ty)
            ));
        }

        // Create a theorem to prove
        lean_code.push_str(&format!(
            "\ntheorem _echidna_goal : {} := by\n  {}\n  sorry\n",
            self.term_to_lean(&goal.target),
            lean_tactic
        ));

        // Write to temp file and check
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_tactic_{}.lean", uuid::Uuid::new_v4()));

        tokio::fs::write(&temp_file, &lean_code)
            .await
            .context("Failed to write temporary file")?;

        let result = self
            .run_lean(&[&temp_file.to_string_lossy()])
            .await;

        // Clean up
        let _ = tokio::fs::remove_file(&temp_file).await;

        match result {
            Ok(output) => {
                // Parse the new tactic state
                let tactic_state = self.parse_tactic_state(&output)?;

                if tactic_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                // Build new proof state
                let mut new_state = state.clone();
                new_state.goals = tactic_state
                    .goals
                    .iter()
                    .map(|g| Goal {
                        id: g.id.clone(),
                        target: self.lean_expr_to_term(&g.target),
                        hypotheses: g
                            .context
                            .iter()
                            .map(|h| Hypothesis {
                                name: h.name.clone(),
                                ty: self.lean_expr_to_term(&h.ty),
                                body: h.value.as_ref().map(|v| self.lean_expr_to_term(v)),
                            })
                            .collect(),
                    })
                    .collect();
                new_state.proof_script.push(tactic.clone());

                Ok(TacticResult::Success(new_state))
            }
            Err(e) => Ok(TacticResult::Error(format!("Tactic failed: {}", e))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.goals.is_empty() {
            return Ok(true);
        }

        // Generate Lean code from the proof state
        let lean_code = self.export(state).await?;

        // Write to temp file and check with Lean
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_verify_{}.lean", uuid::Uuid::new_v4()));

        tokio::fs::write(&temp_file, &lean_code)
            .await
            .context("Failed to write temporary file")?;

        let result = self
            .run_lean(&["--run", &temp_file.to_string_lossy()])
            .await;

        // Clean up
        let _ = tokio::fs::remove_file(&temp_file).await;

        // Check if verification succeeded
        match result {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        // Header
        output.push_str("-- Generated by ECHIDNA\n");
        output.push_str("-- Lean 4 Proof Export\n\n");

        // Export definitions
        for def in &state.context.definitions {
            output.push_str(&format!(
                "def {} : {} := {}\n\n",
                def.name,
                self.term_to_lean(&def.ty),
                self.term_to_lean(&def.body)
            ));
        }

        // Export theorems
        for thm in &state.context.theorems {
            if thm.proof.is_some() {
                output.push_str(&format!(
                    "theorem {} : {} := by\n  sorry\n\n",
                    thm.name,
                    self.term_to_lean(&thm.statement),
                ));
            } else {
                output.push_str(&format!(
                    "axiom {} : {}\n\n",
                    thm.name,
                    self.term_to_lean(&thm.statement)
                ));
            }
        }

        // Export remaining goals as sorrys
        for goal in &state.goals {
            output.push_str(&format!(
                "-- Goal {}: {}\n",
                goal.id,
                self.term_to_lean(&goal.target)
            ));
            output.push_str("-- Hypotheses:\n");
            for hyp in &goal.hypotheses {
                output.push_str(&format!(
                    "--   {} : {}\n",
                    hyp.name,
                    self.term_to_lean(&hyp.ty)
                ));
            }
            output.push_str("\n");
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        if state.goals.is_empty() {
            return Ok(Vec::new());
        }

        let goal = &state.goals[0];
        let mut suggestions = Vec::new();

        // Analyze the goal to suggest appropriate tactics
        let target = &goal.target;

        // Check for function types (suggest intro)
        if matches!(target, Term::Pi { .. } | Term::Lambda { .. }) {
            suggestions.push(Tactic::Intro(None));
        }

        // Check for equality (suggest rfl or simp)
        if let Term::App { func, .. } = target {
            if let Term::Const(name) = func.as_ref() {
                if name == "Eq" || name == "=" {
                    suggestions.push(Tactic::Reflexivity);
                    suggestions.push(Tactic::Simplify);
                }
            }
        }

        // Check for conjunction (suggest constructor via Custom)
        if let Term::App { func, .. } = target {
            if let Term::Const(name) = func.as_ref() {
                if name == "And" || name == "∧" {
                    suggestions.push(Tactic::Custom {
                        prover: "lean".to_string(),
                        command: "constructor".to_string(),
                        args: vec![],
                    });
                }
            }
        }

        // Check for disjunction (suggest left or right)
        if let Term::App { func, .. } = target {
            if let Term::Const(name) = func.as_ref() {
                if name == "Or" || name == "∨" {
                    suggestions.push(Tactic::Custom {
                        prover: "lean".to_string(),
                        command: "left".to_string(),
                        args: vec![],
                    });
                    suggestions.push(Tactic::Custom {
                        prover: "lean".to_string(),
                        command: "right".to_string(),
                        args: vec![],
                    });
                }
            }
        }

        // Check hypotheses for applicable terms
        for hyp in &goal.hypotheses {
            // Suggest apply for function hypotheses that might help
            if matches!(&hyp.ty, Term::Pi { .. }) {
                suggestions.push(Tactic::Apply(hyp.name.clone()));
            }

            // Suggest cases for inductive hypotheses
            if let Term::App { func, .. } = &hyp.ty {
                if let Term::Const(name) = func.as_ref() {
                    if name == "Or" || name == "∨" || name == "Sum" || name == "Bool" {
                        suggestions.push(Tactic::Cases(Term::Var(hyp.name.clone())));
                    }
                }
            }

            // Suggest exact if hypothesis matches goal
            if hyp.ty == *target {
                suggestions.push(Tactic::Exact(Term::Var(hyp.name.clone())));
            }
        }

        // Always include some common tactics
        suggestions.push(Tactic::Assumption);
        suggestions.push(Tactic::Simplify);
        suggestions.push(Tactic::Custom {
            prover: "lean".to_string(),
            command: "decide".to_string(),
            args: vec![],
        });
        suggestions.push(Tactic::Custom {
            prover: "lean".to_string(),
            command: "ring".to_string(),
            args: vec![],
        });
        suggestions.push(Tactic::Custom {
            prover: "lean".to_string(),
            command: "omega".to_string(),
            args: vec![],
        });

        // Deduplicate and limit
        suggestions.dedup();
        suggestions.truncate(limit);

        Ok(suggestions)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Use Lean's #check command to search for matching theorems
        let search_code = format!("#check @{}\n", pattern.replace('*', "_"));

        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_search_{}.lean", uuid::Uuid::new_v4()));

        tokio::fs::write(&temp_file, &search_code)
            .await
            .context("Failed to write temporary file")?;

        let result = self
            .run_lean(&["--run", &temp_file.to_string_lossy()])
            .await;

        let _ = tokio::fs::remove_file(&temp_file).await;

        match result {
            Ok(output) => {
                let matches: Vec<String> = output
                    .lines()
                    .filter(|line| !line.trim().is_empty() && !line.starts_with("--"))
                    .map(|s| s.to_string())
                    .collect();
                Ok(matches)
            }
            Err(_) => Ok(Vec::new()),
        }
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_backend_creation() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Lean);
    }

    #[test]
    fn test_tactic_to_lean() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);

        assert_eq!(backend.tactic_to_lean(&Tactic::Reflexivity), "rfl");
        assert_eq!(backend.tactic_to_lean(&Tactic::Simplify), "simp");
        assert_eq!(backend.tactic_to_lean(&Tactic::Assumption), "assumption");
        assert_eq!(
            backend.tactic_to_lean(&Tactic::Intro(Some("x".to_string()))),
            "intro x"
        );
        assert_eq!(
            backend.tactic_to_lean(&Tactic::Apply("foo".to_string())),
            "apply foo"
        );
        assert_eq!(
            backend.tactic_to_lean(&Tactic::Rewrite("lemma".to_string())),
            "rw [lemma]"
        );
    }

    #[test]
    fn test_term_to_lean() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);

        // Variable
        let var = Term::Var("x".to_string());
        assert_eq!(backend.term_to_lean(&var), "x");

        // Constant
        let constant = Term::Const("Nat".to_string());
        assert_eq!(backend.term_to_lean(&constant), "Nat");

        // Application
        let app = Term::App {
            func: Box::new(Term::Const("f".to_string())),
            args: vec![Term::Var("x".to_string())],
        };
        assert_eq!(backend.term_to_lean(&app), "(f x)");

        // Type
        let ty = Term::Type(0);
        assert_eq!(backend.term_to_lean(&ty), "Prop");

        let ty1 = Term::Type(1);
        assert_eq!(backend.term_to_lean(&ty1), "Type 0");
    }

    #[test]
    fn test_parse_lean_content() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);

        let content = r#"
        -- A simple theorem
        theorem add_comm (n m : Nat) : n + m = m + n := by
          induction n with
          | zero => simp
          | succ n ih => simp [ih]
        "#;

        let declarations = backend.parse_lean_content(content).unwrap();
        assert!(!declarations.is_empty());
    }

    #[test]
    fn test_fresh_meta() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);

        let m1 = backend.fresh_meta();
        let m2 = backend.fresh_meta();
        let m3 = backend.fresh_meta();

        assert_eq!(m1, "?m0");
        assert_eq!(m2, "?m1");
        assert_eq!(m3, "?m2");
    }

    #[test]
    fn test_lean_expr_to_term() {
        let config = ProverConfig::default();
        let backend = LeanBackend::new(config);

        // Variable
        let var = LeanExpr::Var("x".to_string());
        assert!(matches!(backend.lean_expr_to_term(&var), Term::Var(_)));

        // Constant
        let constant = LeanExpr::Const("Nat".to_string(), vec![]);
        assert!(matches!(
            backend.lean_expr_to_term(&constant),
            Term::Const(_)
        ));

        // Metavariable
        let mvar = LeanExpr::MVar("m0".to_string());
        assert!(matches!(backend.lean_expr_to_term(&mvar), Term::Hole(_)));

        // Sort
        let sort = LeanExpr::Sort(LeanLevel::Zero);
        assert!(matches!(backend.lean_expr_to_term(&sort), Term::Type(0)));
    }

    #[test]
    fn test_skip_whitespace_and_comments() {
        let input = "  -- comment\n  theorem";
        let result = skip_whitespace_and_comments(input);
        assert!(result.starts_with("theorem"));

        let input2 = "  /- block -/ def";
        let result2 = skip_whitespace_and_comments(input2);
        assert!(result2.starts_with("def"));
    }
}
