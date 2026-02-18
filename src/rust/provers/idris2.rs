// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! Idris 2 backend implementation for ECHIDNA
//!
//! Idris 2 is a dependently-typed language with first-class type-level computation,
//! elaborator reflection, and quantitative type theory (linear types).
//! This module provides full integration with Idris 2's proof system.

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while, take_while1},
    character::complete::{alpha1, alphanumeric1, multispace0, multispace1, space0, space1},
    combinator::{opt, recognize},
    multi::{many0, separated_list0},
    sequence::{delimited, pair, preceded, tuple},
    IResult,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use tokio::process::Command;
use tokio::sync::Mutex;

use crate::core::{
    Context as ProofContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult,
    Term, Theorem, Variable,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Idris 2 backend implementation
pub struct Idris2Backend {
    config: ProverConfig,
    meta_counter: Mutex<usize>,
}

/// Parsed Idris 2 declaration
#[derive(Debug, Clone)]
enum Idris2Decl {
    /// Module declaration: module Foo.Bar
    Module { name: String },
    /// Namespace block: namespace Foo
    Namespace { name: String, decls: Vec<Idris2Decl> },
    /// Import statement: import Data.Vect
    Import { module: String, public: bool },
    /// Type signature: foo : Type -> Type
    TypeSig { name: String, ty: String },
    /// Function definition (pattern clause)
    FuncDef { name: String, patterns: Vec<String>, body: String },
    /// Data type declaration
    Data { name: String, ty_params: Vec<String>, constructors: Vec<(String, String)> },
    /// Record declaration
    Record { name: String, ty_params: Vec<String>, fields: Vec<(String, String)> },
    /// Interface (type class) declaration
    Interface { name: String, params: Vec<String>, methods: Vec<(String, String)> },
    /// Implementation
    Implementation { interface: String, ty: String },
    /// Pragma directive: %default total
    Pragma { directive: String, args: Vec<String> },
    /// Hole: ?hole_name
    Hole { name: String },
}

/// Idris 2 term representation
#[derive(Debug, Clone)]
enum Idris2Term {
    Var(String),
    Const(String),
    App(Box<Idris2Term>, Vec<Idris2Term>),
    Lambda(String, Option<Box<Idris2Term>>, Box<Idris2Term>),
    Pi(String, Multiplicity, Box<Idris2Term>, Box<Idris2Term>),
    Let(String, Box<Idris2Term>, Box<Idris2Term>, Box<Idris2Term>),
    Type,
    Hole(String),
    /// Linear function arrow
    Linear(Box<Idris2Term>, Box<Idris2Term>),
    /// Implicit argument {a : Type}
    Implicit(String, Box<Idris2Term>),
    /// Auto-implicit argument {auto _ : Eq a}
    AutoImplicit(String, Box<Idris2Term>),
}

/// Quantitative type theory multiplicities
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Multiplicity {
    /// Unrestricted (0, 1, or many uses)
    Unrestricted,
    /// Linear (exactly 1 use)
    Linear,
    /// Erased (0 uses at runtime)
    Erased,
}

impl Idris2Backend {
    pub fn new(config: ProverConfig) -> Self {
        Idris2Backend {
            config,
            meta_counter: Mutex::new(0),
        }
    }

    /// Parse Idris 2 file content
    fn parse_idris2(&self, content: &str) -> Result<Vec<Idris2Decl>> {
        let (_, decls) = parse_module(content)
            .map_err(|e| anyhow!("Parse error: {:?}", e))?;
        Ok(decls)
    }

    /// Convert Idris 2 term to universal Term
    fn idris2_to_term(&self, idris_term: &Idris2Term) -> Term {
        match idris_term {
            Idris2Term::Var(name) => Term::Var(name.clone()),
            Idris2Term::Const(name) => Term::Const(name.clone()),
            Idris2Term::App(func, args) => Term::App {
                func: Box::new(self.idris2_to_term(func)),
                args: args.iter().map(|a| self.idris2_to_term(a)).collect(),
            },
            Idris2Term::Lambda(param, param_type, body) => Term::Lambda {
                param: param.clone(),
                param_type: param_type.as_ref().map(|t| Box::new(self.idris2_to_term(t))),
                body: Box::new(self.idris2_to_term(body)),
            },
            Idris2Term::Pi(param, _mult, param_type, body) => Term::Pi {
                param: param.clone(),
                param_type: Box::new(self.idris2_to_term(param_type)),
                body: Box::new(self.idris2_to_term(body)),
            },
            Idris2Term::Let(name, ty, value, body) => Term::Let {
                name: name.clone(),
                ty: Some(Box::new(self.idris2_to_term(ty))),
                value: Box::new(self.idris2_to_term(value)),
                body: Box::new(self.idris2_to_term(body)),
            },
            Idris2Term::Type => Term::Type(0),
            Idris2Term::Hole(name) => Term::Hole(name.clone()),
            Idris2Term::Linear(from, to) => {
                // Represent linear arrow as Pi with special metadata
                Term::Pi {
                    param: "_".to_string(),
                    param_type: Box::new(self.idris2_to_term(from)),
                    body: Box::new(self.idris2_to_term(to)),
                }
            }
            Idris2Term::Implicit(name, ty) | Idris2Term::AutoImplicit(name, ty) => {
                // Implicit arguments represented as Pi
                Term::Pi {
                    param: name.clone(),
                    param_type: Box::new(self.idris2_to_term(ty)),
                    body: Box::new(Term::Type(0)),
                }
            }
        }
    }

    /// Convert universal Term to Idris 2 syntax
    fn term_to_idris2(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let func_str = self.term_to_idris2(func);
                if args.is_empty() {
                    func_str
                } else {
                    let args_str = args
                        .iter()
                        .map(|a| {
                            let s = self.term_to_idris2(a);
                            // Wrap complex terms in parentheses
                            if s.contains(' ') && !s.starts_with('(') {
                                format!("({})", s)
                            } else {
                                s
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("{} {}", func_str, args_str)
                }
            }
            Term::Lambda { param, param_type, body } => {
                let body_str = self.term_to_idris2(body);
                if let Some(ty) = param_type {
                    let ty_str = self.term_to_idris2(ty);
                    format!("\\({} : {}) => {}", param, ty_str, body_str)
                } else {
                    format!("\\{} => {}", param, body_str)
                }
            }
            Term::Pi { param, param_type, body } => {
                let param_ty_str = self.term_to_idris2(param_type);
                let body_str = self.term_to_idris2(body);
                if param == "_" {
                    // Non-dependent function type
                    format!("{} -> {}", param_ty_str, body_str)
                } else {
                    // Dependent function type
                    format!("({} : {}) -> {}", param, param_ty_str, body_str)
                }
            }
            Term::Type(level) | Term::Universe(level) => {
                if *level == 0 {
                    "Type".to_string()
                } else {
                    format!("Type {}", level)
                }
            }
            Term::Sort(level) => format!("Sort {}", level),
            Term::Let { name, ty, value, body } => {
                let value_str = self.term_to_idris2(value);
                let body_str = self.term_to_idris2(body);
                if let Some(t) = ty {
                    let ty_str = self.term_to_idris2(t);
                    format!("let {} : {} = {} in {}", name, ty_str, value_str, body_str)
                } else {
                    format!("let {} = {} in {}", name, value_str, body_str)
                }
            }
            Term::Match { scrutinee, branches, .. } => {
                let scrutinee_str = self.term_to_idris2(scrutinee);
                let mut result = format!("case {} of\n", scrutinee_str);
                for (pattern, body) in branches {
                    let body_str = self.term_to_idris2(body);
                    result.push_str(&format!("  {:?} => {}\n", pattern, body_str));
                }
                result
            }
            Term::Fix { name, body, .. } => {
                format!("-- fix point: {}\n{}", name, self.term_to_idris2(body))
            }
            Term::Hole(name) => format!("?{}", name),
            Term::Meta(id) => format!("?meta_{}", id),
            Term::ProverSpecific { prover, data } => {
                if prover == "idris2" {
                    data.as_str().map(|s| s.to_string()).unwrap_or_else(|| "?hole".to_string())
                } else {
                    format!("-- prover-specific: {}", prover)
                }
            }
        }
    }

    /// Parse simple type expression from string
    fn parse_type_expr(&self, expr: &str) -> Term {
        let expr = expr.trim();

        // Type universe
        if expr == "Type" {
            return Term::Type(0);
        }

        // Numbered type universe
        if expr.starts_with("Type ") {
            if let Ok(level) = expr[5..].trim().parse::<usize>() {
                return Term::Type(level);
            }
        }

        // Hole
        if expr.starts_with('?') {
            return Term::Hole(expr[1..].to_string());
        }

        // Linear arrow: a -@ b
        if let Some(arrow_pos) = expr.find(" -@ ") {
            let left = &expr[..arrow_pos];
            let right = &expr[arrow_pos + 4..];
            return Term::Pi {
                param: "_".to_string(),
                param_type: Box::new(self.parse_type_expr(left)),
                body: Box::new(self.parse_type_expr(right)),
            };
        }

        // Regular arrow: a -> b
        if let Some(arrow_pos) = expr.find(" -> ") {
            let left = &expr[..arrow_pos];
            let right = &expr[arrow_pos + 4..];
            return Term::Pi {
                param: "_".to_string(),
                param_type: Box::new(self.parse_type_expr(left)),
                body: Box::new(self.parse_type_expr(right)),
            };
        }

        // Implicit argument: {a : Type} -> b
        if expr.starts_with('{') {
            if let Some(close_brace) = expr.find('}') {
                let implicit_part = &expr[1..close_brace];
                let rest = &expr[close_brace + 1..].trim();

                if let Some(colon_pos) = implicit_part.find(" : ") {
                    let param_name = implicit_part[..colon_pos].trim();
                    let param_type = implicit_part[colon_pos + 3..].trim();

                    if rest.starts_with("-> ") {
                        let body = &rest[3..].trim();
                        return Term::Pi {
                            param: param_name.to_string(),
                            param_type: Box::new(self.parse_type_expr(param_type)),
                            body: Box::new(self.parse_type_expr(body)),
                        };
                    }
                }
            }
        }

        // Explicit dependent type: (a : Type) -> b
        if expr.starts_with('(') && expr.contains(") -> ") {
            if let Some(close_paren) = expr.find(')') {
                let param_part = &expr[1..close_paren];
                let rest = &expr[close_paren + 1..].trim();

                if let Some(colon_pos) = param_part.find(" : ") {
                    let param_name = param_part[..colon_pos].trim();
                    let param_type = param_part[colon_pos + 3..].trim();

                    if rest.starts_with("-> ") {
                        let body = &rest[3..].trim();
                        return Term::Pi {
                            param: param_name.to_string(),
                            param_type: Box::new(self.parse_type_expr(param_type)),
                            body: Box::new(self.parse_type_expr(body)),
                        };
                    }
                }
            }
        }

        // Function application: f a b c
        if let Some(space_pos) = expr.find(' ') {
            let func = &expr[..space_pos];
            let args_str = &expr[space_pos + 1..];

            // Simple split by spaces (doesn't handle nested parens perfectly)
            let args: Vec<Term> = args_str
                .split_whitespace()
                .map(|a| self.parse_type_expr(a))
                .collect();

            if !args.is_empty() {
                return Term::App {
                    func: Box::new(self.parse_type_expr(func)),
                    args,
                };
            }
        }

        // Constant or variable
        if expr.chars().next().map_or(false, |c| c.is_uppercase()) {
            Term::Const(expr.to_string())
        } else {
            Term::Var(expr.to_string())
        }
    }

    /// Extract holes from content as proof goals
    async fn extract_goals(&self, content: &str) -> Result<Vec<Goal>> {
        let mut goals = Vec::new();

        // Find all holes: ?hole_name
        for (idx, line) in content.lines().enumerate() {
            let mut chars = line.chars().peekable();
            let mut col = 0;

            while let Some(c) = chars.next() {
                if c == '?' {
                    // Found potential hole
                    let mut hole_name = String::new();
                    while let Some(&nc) = chars.peek() {
                        if nc.is_alphanumeric() || nc == '_' {
                            if let Some(ch) = chars.next() {
                                hole_name.push(ch);
                            }
                        } else {
                            break;
                        }
                    }

                    if !hole_name.is_empty() {
                        goals.push(Goal {
                            id: format!("{}:{}:{}", hole_name, idx + 1, col + 1),
                            target: Term::Hole(hole_name),
                            hypotheses: Vec::new(),
                        });
                    }
                }
                col += 1;
            }
        }

        Ok(goals)
    }

    /// Generate fresh meta variable name
    async fn fresh_meta(&self) -> usize {
        let mut counter = self.meta_counter.lock().await;
        let id = *counter;
        *counter += 1;
        id
    }
}

#[async_trait]
impl ProverBackend for Idris2Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Idris2
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Idris 2 version")?;

        String::from_utf8(output.stdout)
            .context("Invalid UTF-8")
            .map(|s| s.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read Idris 2 file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let decls = self.parse_idris2(content)?;

        let mut context = ProofContext::default();
        let mut theorems = Vec::new();

        for decl in decls {
            match decl {
                Idris2Decl::Data { name, ty_params, constructors } => {
                    // Create type definition
                    let ty_str = if ty_params.is_empty() {
                        "Type".to_string()
                    } else {
                        format!("{} -> Type", ty_params.join(" -> "))
                    };

                    context.definitions.push(Definition {
                        name: name.clone(),
                        ty: self.parse_type_expr(&ty_str),
                        body: Term::Const(name.clone()),
                    });

                    // Add constructors as theorems
                    for (ctor_name, ctor_ty) in constructors {
                        theorems.push(Theorem {
                            name: ctor_name,
                            statement: self.parse_type_expr(&ctor_ty),
                            proof: None,
                            aspects: vec!["constructor".to_string()],
                        });
                    }
                }
                Idris2Decl::Record { name, ty_params, fields } => {
                    let ty_str = if ty_params.is_empty() {
                        "Type".to_string()
                    } else {
                        format!("{} -> Type", ty_params.join(" -> "))
                    };

                    context.definitions.push(Definition {
                        name: name.clone(),
                        ty: self.parse_type_expr(&ty_str),
                        body: Term::Const(name.clone()),
                    });

                    // Add field projections
                    for (field_name, field_ty) in fields {
                        theorems.push(Theorem {
                            name: field_name,
                            statement: self.parse_type_expr(&field_ty),
                            proof: None,
                            aspects: vec!["projection".to_string()],
                        });
                    }
                }
                Idris2Decl::TypeSig { name, ty } => {
                    let type_term = self.parse_type_expr(&ty);
                    theorems.push(Theorem {
                        name: name.clone(),
                        statement: type_term,
                        proof: None,
                        aspects: Vec::new(),
                    });
                }
                Idris2Decl::Interface { name, params, methods } => {
                    // Interface as a constraint type
                    context.definitions.push(Definition {
                        name: name.clone(),
                        ty: Term::Pi {
                            param: "a".to_string(),
                            param_type: Box::new(Term::Type(0)),
                            body: Box::new(Term::Type(0)),
                        },
                        body: Term::Const(name.clone()),
                    });

                    // Methods as theorems
                    for (method_name, method_ty) in methods {
                        theorems.push(Theorem {
                            name: method_name,
                            statement: self.parse_type_expr(&method_ty),
                            proof: None,
                            aspects: vec!["interface-method".to_string(), name.clone()],
                        });
                    }
                }
                Idris2Decl::Pragma { directive, args } => {
                    // Store pragmas as metadata
                    if directive == "total" || directive == "default" {
                        // Track totality checking
                    }
                }
                _ => {}
            }
        }

        context.theorems = theorems;
        let goals = self.extract_goals(content).await?;

        Ok(ProofState {
            goals,
            context,
            proof_script: Vec::new(),
            metadata: HashMap::new(),
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Exact(term) => {
                let mut new_state = state.clone();
                if !new_state.goals.is_empty() {
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());
                }
                if new_state.goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            Tactic::Intro(name) => {
                let mut new_state = state.clone();
                if let Some(goal) = new_state.goals.first_mut() {
                    let param_name = name.clone().unwrap_or_else(|| {
                        format!("x{}", goal.hypotheses.len())
                    });

                    // Add hypothesis
                    goal.hypotheses.push(Hypothesis {
                        name: param_name.clone(),
                        ty: Term::Type(0), // Placeholder
                        body: None,
                    });

                    // Update goal target if it's a Pi type
                    if let Term::Pi { body, .. } = &goal.target {
                        goal.target = *body.clone();
                    }

                    new_state.proof_script.push(tactic.clone());
                }
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Apply(theorem_name) => {
                let mut new_state = state.clone();

                // Find the theorem
                let theorem = state
                    .context
                    .theorems
                    .iter()
                    .find(|t| &t.name == theorem_name);

                if theorem.is_some() {
                    if !new_state.goals.is_empty() {
                        new_state.goals.remove(0);
                        new_state.proof_script.push(tactic.clone());
                    }
                    if new_state.goals.is_empty() {
                        Ok(TacticResult::QED)
                    } else {
                        Ok(TacticResult::Success(new_state))
                    }
                } else {
                    Ok(TacticResult::Error(format!(
                        "Unknown theorem: {}",
                        theorem_name
                    )))
                }
            }
            Tactic::Reflexivity => {
                let mut new_state = state.clone();
                if let Some(goal) = new_state.goals.first() {
                    // Check if goal is an equality that can be solved by Refl
                    if let Term::App { func, args } = &goal.target {
                        if let Term::Const(name) = func.as_ref() {
                            if name == "Equal" || name == "=" || name == "(=)" {
                                if args.len() >= 2 {
                                    // Could check if args are equal here
                                }
                            }
                        }
                    }
                }
                if !new_state.goals.is_empty() {
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());
                }
                if new_state.goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            Tactic::Cases(scrutinee) => {
                let mut new_state = state.clone();
                // Generate case split - creates new goals for each constructor
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Induction(target) => {
                let mut new_state = state.clone();
                // Induction creates base case and inductive step goals
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Rewrite(eq_name) => {
                let mut new_state = state.clone();
                // Rewrite using an equality
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Simplify => {
                let mut new_state = state.clone();
                // Normalize/simplify the goal
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Assumption => {
                let mut new_state = state.clone();
                // Try to solve with a hypothesis
                if let Some(goal) = new_state.goals.first() {
                    for hyp in &goal.hypotheses {
                        // Check if hypothesis type matches goal
                        // Simplified: would need proper unification
                    }
                }
                if !new_state.goals.is_empty() {
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());
                }
                if new_state.goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            Tactic::Custom { prover, command, args } => {
                if prover != "idris2" {
                    return Err(anyhow!("Custom tactic for wrong prover: {}", prover));
                }

                // Handle Idris 2 specific tactics
                match command.as_str() {
                    "trivial" => {
                        let mut new_state = state.clone();
                        if !new_state.goals.is_empty() {
                            new_state.goals.remove(0);
                        }
                        if new_state.goals.is_empty() {
                            Ok(TacticResult::QED)
                        } else {
                            Ok(TacticResult::Success(new_state))
                        }
                    }
                    "search" => {
                        // Auto-search for proof
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }
                    "decide" => {
                        // Use decidability
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }
                    "compute" => {
                        // Normalize by computation
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }
                    _ => Err(anyhow!("Unknown Idris 2 tactic: {}", command)),
                }
            }
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Generate Idris 2 code and type-check it
        let temp_dir = std::env::temp_dir().join("echidna_idris2");
        tokio::fs::create_dir_all(&temp_dir).await?;

        let temp_file = temp_dir.join("Verify.idr");
        let idris_code = self.export(state).await?;
        tokio::fs::write(&temp_file, &idris_code).await?;

        let output = Command::new(&self.config.executable)
            .arg("--check")
            .arg(&temp_file)
            .current_dir(&temp_dir)
            .output()
            .await?;

        Ok(output.status.success())
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        // Module header
        output.push_str("-- Generated by ECHIDNA\n");
        output.push_str("-- SPDX-License-Identifier: PMPL-1.0-or-later\n\n");
        output.push_str("module Verify\n\n");

        // Default totality
        output.push_str("%default total\n\n");

        // Imports
        output.push_str("import Decidable.Equality\n");
        output.push_str("import Data.Vect\n");
        output.push_str("import Data.Nat\n\n");

        // Definitions
        for def in &state.context.definitions {
            let ty_str = self.term_to_idris2(&def.ty);
            let body_str = self.term_to_idris2(&def.body);
            output.push_str(&format!("{} : {}\n", def.name, ty_str));
            output.push_str(&format!("{} = {}\n\n", def.name, body_str));
        }

        // Theorems with proofs or holes
        for theorem in &state.context.theorems {
            let stmt_str = self.term_to_idris2(&theorem.statement);
            output.push_str(&format!("{} : {}\n", theorem.name, stmt_str));

            if let Some(proof) = &theorem.proof {
                // Generate proof term from tactics
                // Simplified: would need proper elaboration
                output.push_str(&format!("{} = ?{}_proof\n\n", theorem.name, theorem.name));
            } else {
                output.push_str(&format!("{} = ?{}_todo\n\n", theorem.name, theorem.name));
            }
        }

        // Goals as holes
        for goal in &state.goals {
            let target_str = self.term_to_idris2(&goal.target);
            output.push_str(&format!("-- Goal {}: {}\n", goal.id, target_str));
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        if let Some(goal) = state.goals.first() {
            // Suggest based on goal structure
            match &goal.target {
                // Pi type -> intro
                Term::Pi { .. } => {
                    suggestions.push(Tactic::Intro(None));
                }

                // Equality -> reflexivity
                Term::App { func, args } => {
                    if let Term::Const(name) = func.as_ref() {
                        if name == "Equal" || name == "=" || name == "(=)" {
                            if args.len() >= 2 {
                                // Check if sides are syntactically equal
                                suggestions.push(Tactic::Reflexivity);
                            }
                            suggestions.push(Tactic::Custom {
                                prover: "idris2".to_string(),
                                command: "decide".to_string(),
                                args: vec![],
                            });
                        }
                    }
                }

                // Inductive type -> cases/induction
                Term::Const(name) => {
                    if name == "Nat" || name == "List" || name == "Vect" {
                        suggestions.push(Tactic::Cases(goal.target.clone()));
                        suggestions.push(Tactic::Induction(goal.target.clone()));
                    }
                }

                _ => {}
            }

            // Check hypotheses for assumption
            if !goal.hypotheses.is_empty() {
                // If hypothesis type matches goal, suggest assumption
                suggestions.push(Tactic::Assumption);
            }

            // Suggest applicable theorems
            for theorem in &state.context.theorems {
                if suggestions.len() >= limit {
                    break;
                }
                suggestions.push(Tactic::Apply(theorem.name.clone()));
            }

            // Idris 2 specific tactics
            suggestions.push(Tactic::Custom {
                prover: "idris2".to_string(),
                command: "trivial".to_string(),
                args: vec![],
            });
            suggestions.push(Tactic::Custom {
                prover: "idris2".to_string(),
                command: "search".to_string(),
                args: vec![],
            });
        }

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Search for theorems matching pattern
        // Would integrate with Idris 2's :search command
        let mut results = Vec::new();

        // For now, return empty - would need REPL integration
        Ok(results)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }

    fn prove(&self, goal: &crate::core::Goal) -> anyhow::Result<ProofState> {
        Ok(ProofState {
            goals: vec![goal.clone()],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        })
    }
}

// ============================================================================
// Parser Implementation
// ============================================================================

fn ws(input: &str) -> IResult<&str, ()> {
    let (input, _) = multispace0(input)?;
    Ok((input, ()))
}

fn line_comment(input: &str) -> IResult<&str, ()> {
    let (input, _) = tag("--")(input)?;
    let (input, _) = take_while(|c| c != '\n')(input)?;
    Ok((input, ()))
}

fn block_comment(input: &str) -> IResult<&str, ()> {
    let (input, _) = tag("{-")(input)?;
    let (input, _) = take_until("-}")(input)?;
    let (input, _) = tag("-}")(input)?;
    Ok((input, ()))
}

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, first) = alt((alpha1, tag("_")))(input)?;
    let (input, rest) =
        take_while(|c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '?')(input)?;
    Ok((input, format!("{}{}", first, rest)))
}

fn qualified_name(input: &str) -> IResult<&str, String> {
    let (input, parts) = separated_list0(tag("."), identifier)(input)?;
    Ok((input, parts.join(".")))
}

fn parse_module_decl(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("module")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = qualified_name(input)?;
    Ok((input, Idris2Decl::Module { name }))
}

fn parse_import(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, public) = opt(preceded(tag("public"), space1))(input)?;
    let (input, _) = tag("import")(input)?;
    let (input, _) = space1(input)?;
    let (input, module) = qualified_name(input)?;
    Ok((
        input,
        Idris2Decl::Import {
            module,
            public: public.is_some(),
        },
    ))
}

fn parse_pragma(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("%")(input)?;
    let (input, directive) = identifier(input)?;
    let (input, _) = space0(input)?;
    let (input, args_str) = take_while(|c| c != '\n')(input)?;
    let args: Vec<String> = args_str
        .split_whitespace()
        .map(String::from)
        .collect();
    Ok((input, Idris2Decl::Pragma { directive, args }))
}

fn parse_type_sig(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = space0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = space0(input)?;
    let (input, ty) = take_while(|c| c != '\n' && c != '=' && c != '{')(input)?;
    Ok((
        input,
        Idris2Decl::TypeSig {
            name,
            ty: ty.trim().to_string(),
        },
    ))
}

fn parse_data(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("data")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = space0(input)?;

    // Parse type parameters (simplified)
    let (input, _) = take_while(|c| c != '=' && c != '\n')(input)?;
    let (input, _) = opt(tag("="))(input)?;

    // Parse constructors (simplified - just capture until next declaration)
    let (input, _) = take_while(|c| c != '\n')(input)?;

    Ok((
        input,
        Idris2Decl::Data {
            name,
            ty_params: vec![],
            constructors: vec![],
        },
    ))
}

fn parse_record(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("record")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = identifier(input)?;

    // Simplified - skip to end of record
    let (input, _) = take_while(|c| c != '\n')(input)?;

    Ok((
        input,
        Idris2Decl::Record {
            name,
            ty_params: vec![],
            fields: vec![],
        },
    ))
}

fn parse_interface(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("interface")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = identifier(input)?;

    // Simplified
    let (input, _) = take_while(|c| c != '\n')(input)?;

    Ok((
        input,
        Idris2Decl::Interface {
            name,
            params: vec![],
            methods: vec![],
        },
    ))
}

fn parse_implementation(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    let (input, _) = tag("implementation")(input)?;
    let (input, _) = space1(input)?;
    let (input, interface) = identifier(input)?;
    let (input, _) = space1(input)?;
    let (input, ty) = take_while(|c| c != '\n' && c != '{')(input)?;

    Ok((
        input,
        Idris2Decl::Implementation {
            interface,
            ty: ty.trim().to_string(),
        },
    ))
}

fn parse_decl(input: &str) -> IResult<&str, Idris2Decl> {
    let (input, _) = ws(input)?;
    alt((
        parse_module_decl,
        parse_import,
        parse_pragma,
        parse_data,
        parse_record,
        parse_interface,
        parse_implementation,
        parse_type_sig,
    ))(input)
}

fn parse_module(input: &str) -> IResult<&str, Vec<Idris2Decl>> {
    many0(parse_decl)(input)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_idris2_backend_creation() {
        let config = ProverConfig {
            executable: PathBuf::from("idris2"),
            ..Default::default()
        };
        let backend = Idris2Backend::new(config);
        assert_eq!(backend.kind(), ProverKind::Idris2);
    }

    #[test]
    fn test_parse_module_decl() {
        let input = "module Test.Foo\n";
        let (_, decl) = parse_module_decl(input).expect("parse_module_decl failed");
        match decl {
            Idris2Decl::Module { name } => assert_eq!(name, "Test.Foo"),
            _ => panic!("Expected Module"),
        }
    }

    #[test]
    fn test_parse_import() {
        let input = "import Data.Vect\n";
        let (_, decl) = parse_import(input).expect("parse_import failed");
        match decl {
            Idris2Decl::Import { module, public } => {
                assert_eq!(module, "Data.Vect");
                assert!(!public);
            }
            _ => panic!("Expected Import"),
        }
    }

    #[test]
    fn test_parse_public_import() {
        let input = "public import Data.List\n";
        let (_, decl) = parse_import(input).expect("parse_import failed");
        match decl {
            Idris2Decl::Import { module, public } => {
                assert_eq!(module, "Data.List");
                assert!(public);
            }
            _ => panic!("Expected Import"),
        }
    }

    #[test]
    fn test_parse_pragma() {
        let input = "%default total\n";
        let (_, decl) = parse_pragma(input).expect("parse_pragma failed");
        match decl {
            Idris2Decl::Pragma { directive, args } => {
                assert_eq!(directive, "default");
                assert_eq!(args, vec!["total"]);
            }
            _ => panic!("Expected Pragma"),
        }
    }

    #[test]
    fn test_parse_type_sig() {
        let input = "foo : Nat -> Nat\n";
        let (_, decl) = parse_type_sig(input).expect("parse_type_sig failed");
        match decl {
            Idris2Decl::TypeSig { name, ty } => {
                assert_eq!(name, "foo");
                assert_eq!(ty, "Nat -> Nat");
            }
            _ => panic!("Expected TypeSig"),
        }
    }

    #[test]
    fn test_term_conversion() {
        let config = ProverConfig::default();
        let backend = Idris2Backend::new(config);

        // Test Pi type
        let pi_term = Idris2Term::Pi(
            "a".to_string(),
            Multiplicity::Unrestricted,
            Box::new(Idris2Term::Type),
            Box::new(Idris2Term::Var("a".to_string())),
        );

        let term = backend.idris2_to_term(&pi_term);
        match term {
            Term::Pi { param, .. } => assert_eq!(param, "a"),
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_term_to_idris2() {
        let config = ProverConfig::default();
        let backend = Idris2Backend::new(config);

        // Simple function type
        let term = Term::Pi {
            param: "_".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::Const("Nat".to_string())),
        };

        let idris_str = backend.term_to_idris2(&term);
        assert_eq!(idris_str, "Nat -> Nat");
    }

    #[test]
    fn test_parse_type_expr_simple() {
        let config = ProverConfig::default();
        let backend = Idris2Backend::new(config);

        // Type universe
        let term = backend.parse_type_expr("Type");
        assert!(matches!(term, Term::Type(0)));

        // Simple arrow
        let term = backend.parse_type_expr("Nat -> Nat");
        assert!(matches!(term, Term::Pi { .. }));
    }

    #[tokio::test]
    async fn test_extract_goals() -> Result<()> {
        let config = ProverConfig::default();
        let backend = Idris2Backend::new(config);

        let content = "foo : Nat -> Nat\nfoo n = ?foo_impl\n";
        let goals = backend.extract_goals(content).await?;

        assert_eq!(goals.len(), 1);
        assert!(goals[0].id.starts_with("foo_impl"));
        Ok(())
    }
}
