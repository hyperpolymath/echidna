// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! ACL2 theorem prover backend implementation
//!
//! ACL2 (A Computational Logic for Applicative Common Lisp) is a theorem prover
//! for a first-order logic based on Common Lisp. It uses a "waterfall" proof
//! strategy with hints rather than explicit tactics.
//!
//! Key features:
//! - S-expression based syntax (Lisp)
//! - Automated proof with hints
//! - Industrial strength (AMD, Intel, etc.)
//! - Executable specifications

use async_trait::async_trait;
use anyhow::{anyhow, Context as AnyhowContext, Result};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, Command};
use tokio::sync::Mutex;

use crate::core::{
    Context, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult, Term, Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// ACL2 theorem prover backend
pub struct ACL2Backend {
    config: ProverConfig,
    session: Mutex<Option<ACL2Session>>,
}

/// Active ACL2 session
struct ACL2Session {
    process: Child,
    ready: bool,
}

/// ACL2 S-expression representation
#[derive(Debug, Clone, PartialEq)]
pub enum SExp {
    /// Atom (symbol or number)
    Atom(String),
    /// String literal
    Str(String),
    /// Number
    Num(i64),
    /// List of S-expressions
    List(Vec<SExp>),
    /// Quoted expression
    Quote(Box<SExp>),
    /// Nil
    Nil,
}

impl SExp {
    /// Create an atom
    pub fn atom(s: &str) -> Self {
        SExp::Atom(s.to_string())
    }

    /// Create a list
    pub fn list(items: Vec<SExp>) -> Self {
        SExp::List(items)
    }

    /// Create a quoted expression
    pub fn quote(inner: SExp) -> Self {
        SExp::Quote(Box::new(inner))
    }

    /// Convert to Lisp string representation
    pub fn to_lisp(&self) -> String {
        match self {
            SExp::Atom(s) => s.clone(),
            SExp::Str(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
            SExp::Num(n) => n.to_string(),
            SExp::List(items) => {
                let inner = items.iter().map(|i| i.to_lisp()).collect::<Vec<_>>().join(" ");
                format!("({})", inner)
            }
            SExp::Quote(inner) => format!("'{}", inner.to_lisp()),
            SExp::Nil => "nil".to_string(),
        }
    }

    /// Parse S-expression from string
    pub fn parse(input: &str) -> Result<Self> {
        let mut chars = input.chars().peekable();
        skip_whitespace(&mut chars);
        parse_sexp_inner(&mut chars)
    }

    /// Check if this is a specific atom
    pub fn is_atom(&self, name: &str) -> bool {
        matches!(self, SExp::Atom(s) if s.eq_ignore_ascii_case(name))
    }

    /// Get as list
    pub fn as_list(&self) -> Option<&Vec<SExp>> {
        match self {
            SExp::List(items) => Some(items),
            _ => None,
        }
    }

    /// Get as atom string
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            SExp::Atom(s) => Some(s),
            _ => None,
        }
    }
}

fn skip_whitespace(chars: &mut std::iter::Peekable<std::str::Chars>) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == ';' {
            // Skip comment to end of line
            while let Some(&c) = chars.peek() {
                chars.next();
                if c == '\n' {
                    break;
                }
            }
        } else {
            break;
        }
    }
}

fn parse_sexp_inner(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<SExp> {
    skip_whitespace(chars);

    match chars.peek() {
        None => Err(anyhow!("Unexpected end of input")),
        Some(&'(') => {
            chars.next();
            let mut items = Vec::new();
            loop {
                skip_whitespace(chars);
                match chars.peek() {
                    None => return Err(anyhow!("Unmatched opening parenthesis")),
                    Some(&')') => {
                        chars.next();
                        break;
                    }
                    Some(&'.') => {
                        // Dotted pair - skip for simplicity
                        chars.next();
                        skip_whitespace(chars);
                        let _tail = parse_sexp_inner(chars)?;
                        skip_whitespace(chars);
                        if chars.next() != Some(')') {
                            return Err(anyhow!("Expected ) after dotted pair"));
                        }
                        break;
                    }
                    _ => {
                        items.push(parse_sexp_inner(chars)?);
                    }
                }
            }
            if items.is_empty() {
                Ok(SExp::Nil)
            } else {
                Ok(SExp::List(items))
            }
        }
        Some(&')') => Err(anyhow!("Unexpected closing parenthesis")),
        Some(&'\'') => {
            chars.next();
            let inner = parse_sexp_inner(chars)?;
            Ok(SExp::Quote(Box::new(inner)))
        }
        Some(&'`') => {
            // Backquote - treat like quote for simplicity
            chars.next();
            let inner = parse_sexp_inner(chars)?;
            Ok(SExp::Quote(Box::new(inner)))
        }
        Some(&'"') => {
            // String literal
            chars.next();
            let mut s = String::new();
            let mut escape = false;
            loop {
                match chars.next() {
                    None => return Err(anyhow!("Unterminated string")),
                    Some('\\') if !escape => escape = true,
                    Some('"') if !escape => break,
                    Some(c) => {
                        escape = false;
                        s.push(c);
                    }
                }
            }
            Ok(SExp::Str(s))
        }
        Some(&c) if c == '-' || c.is_ascii_digit() => {
            // Try to parse as number
            let mut num_str = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_ascii_digit() || c == '-' {
                    num_str.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            if let Ok(n) = num_str.parse::<i64>() {
                Ok(SExp::Num(n))
            } else {
                // It's an atom starting with -
                let mut atom = num_str;
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                Ok(SExp::Atom(atom))
            }
        }
        Some(_) => {
            // Atom
            let mut atom = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_whitespace() || c == '(' || c == ')' || c == '\'' || c == '"' {
                    break;
                }
                atom.push(c);
                chars.next();
            }
            if atom.eq_ignore_ascii_case("nil") {
                Ok(SExp::Nil)
            } else if atom.eq_ignore_ascii_case("t") {
                Ok(SExp::Atom("t".to_string()))
            } else {
                Ok(SExp::Atom(atom))
            }
        }
    }
}

/// ACL2 event types
#[derive(Debug, Clone)]
pub enum ACL2Event {
    /// Function definition (defun)
    Defun {
        name: String,
        params: Vec<String>,
        body: SExp,
        guard: Option<SExp>,
    },
    /// Theorem definition (defthm)
    Defthm {
        name: String,
        formula: SExp,
        hints: Vec<ACL2Hint>,
        rule_classes: Option<SExp>,
    },
    /// Encapsulate block
    Encapsulate {
        signatures: Vec<(String, SExp)>,
        events: Vec<ACL2Event>,
    },
    /// Include book
    IncludeBook {
        name: String,
        dir: Option<String>,
    },
    /// In-theory event
    InTheory(SExp),
    /// Mutual recursion
    MutualRecursion(Vec<ACL2Event>),
    /// Constant definition (defconst)
    Defconst {
        name: String,
        value: SExp,
    },
    /// Macro definition (defmacro)
    Defmacro {
        name: String,
        params: Vec<String>,
        body: SExp,
    },
    /// Other/unknown event
    Other(SExp),
}

/// ACL2 proof hints
#[derive(Debug, Clone)]
pub enum ACL2Hint {
    /// :induct hint
    Induct(SExp),
    /// :use hint
    Use(Vec<SExp>),
    /// :expand hint
    Expand(Vec<SExp>),
    /// :in-theory hint
    InTheory(SExp),
    /// :cases hint
    Cases(Vec<SExp>),
    /// :by hint
    By(SExp),
    /// :hands-off hint
    HandsOff(Vec<String>),
    /// :do-not hint
    DoNot(Vec<String>),
    /// :do-not-induct hint
    DoNotInduct(bool),
    /// Goal-specific hint
    Goal {
        goal_name: String,
        hints: Vec<ACL2Hint>,
    },
    /// Other hint
    Other(String, SExp),
}

impl ACL2Backend {
    /// Create a new ACL2 backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        ACL2Backend {
            config,
            session: Mutex::new(None),
        }
    }

    /// Start a new ACL2 session
    async fn start_session(&self) -> Result<ACL2Session> {
        let exe = if self.config.executable.as_os_str().is_empty() {
            "acl2"
        } else {
            self.config.executable.to_str().unwrap_or("acl2")
        };

        let mut cmd = Command::new(exe);
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        for arg in &self.config.args {
            cmd.arg(arg);
        }

        let process = cmd.spawn().context("Failed to start ACL2 process")?;

        Ok(ACL2Session {
            process,
            ready: false,
        })
    }

    /// Ensure session is running
    async fn ensure_session(&self) -> Result<()> {
        let mut session_lock = self.session.lock().await;
        if session_lock.is_none() {
            let mut session = self.start_session().await?;
            // Wait for ACL2 to be ready
            self.wait_for_prompt(&mut session).await?;
            session.ready = true;
            *session_lock = Some(session);
        }
        Ok(())
    }

    /// Wait for ACL2 prompt
    async fn wait_for_prompt(&self, session: &mut ACL2Session) -> Result<String> {
        let stdout = session
            .process
            .stdout
            .as_mut()
            .ok_or_else(|| anyhow!("No stdout"))?;

        let mut reader = BufReader::new(stdout);
        let mut output = String::new();
        let mut line = String::new();

        loop {
            line.clear();
            let bytes = reader.read_line(&mut line).await?;
            if bytes == 0 {
                break;
            }
            output.push_str(&line);
            // ACL2 prompt is typically "ACL2 !>" or similar
            if line.contains("ACL2") && (line.contains(">") || line.contains("!>")) {
                break;
            }
        }

        Ok(output)
    }

    /// Send command to ACL2 and get response
    async fn send_command(&self, cmd: &str) -> Result<String> {
        self.ensure_session().await?;

        let mut session_lock = self.session.lock().await;
        let session = session_lock
            .as_mut()
            .ok_or_else(|| anyhow!("No active session"))?;

        let stdin = session
            .process
            .stdin
            .as_mut()
            .ok_or_else(|| anyhow!("No stdin"))?;

        // Send command with newline
        let cmd_with_newline = format!("{}\n", cmd);
        stdin
            .write_all(cmd_with_newline.as_bytes())
            .await
            .context("Failed to write command")?;
        stdin.flush().await.context("Failed to flush")?;

        // Read response until next prompt
        self.wait_for_prompt(session).await
    }

    /// Parse ACL2 file content
    fn parse_file_content(&self, content: &str) -> Result<Vec<ACL2Event>> {
        let mut events = Vec::new();
        let mut remaining = content.trim();

        while !remaining.is_empty() {
            // Skip whitespace and comments
            remaining = remaining.trim_start();
            if remaining.starts_with(';') {
                // Skip comment line
                if let Some(pos) = remaining.find('\n') {
                    remaining = &remaining[pos + 1..];
                } else {
                    break;
                }
                continue;
            }

            if remaining.starts_with('(') {
                // Parse S-expression
                match SExp::parse(remaining) {
                    Ok(sexp) => {
                        if let Some(event) = self.parse_event(&sexp)? {
                            events.push(event);
                        }
                        // Find end of this S-expression to advance
                        let sexp_len = find_sexp_end(remaining)?;
                        remaining = &remaining[sexp_len..];
                    }
                    Err(e) => {
                        // Try to skip to next top-level form
                        if let Some(pos) = remaining[1..].find("\n(") {
                            remaining = &remaining[pos + 1..];
                        } else {
                            return Err(e);
                        }
                    }
                }
            } else if remaining.starts_with('#') {
                // Skip reader macros
                if let Some(pos) = remaining.find('\n') {
                    remaining = &remaining[pos + 1..];
                } else {
                    break;
                }
            } else {
                // Skip unknown content
                if let Some(pos) = remaining.find('\n') {
                    remaining = &remaining[pos + 1..];
                } else {
                    break;
                }
            }
        }

        Ok(events)
    }

    /// Parse a single ACL2 event from S-expression
    fn parse_event(&self, sexp: &SExp) -> Result<Option<ACL2Event>> {
        let list = match sexp.as_list() {
            Some(l) if !l.is_empty() => l,
            _ => return Ok(None),
        };

        let head = match list[0].as_atom() {
            Some(s) => s.to_lowercase(),
            None => return Ok(Some(ACL2Event::Other(sexp.clone()))),
        };

        match head.as_str() {
            "defun" | "defund" => self.parse_defun(&list),
            "defthm" | "defthmd" => self.parse_defthm(&list),
            "defconst" => self.parse_defconst(&list),
            "defmacro" => self.parse_defmacro(&list),
            "encapsulate" => self.parse_encapsulate(&list),
            "include-book" => self.parse_include_book(&list),
            "in-theory" => Ok(Some(ACL2Event::InTheory(
                list.get(1).cloned().unwrap_or(SExp::Nil),
            ))),
            "mutual-recursion" => self.parse_mutual_recursion(&list),
            _ => Ok(Some(ACL2Event::Other(sexp.clone()))),
        }
    }

    /// Parse defun event
    fn parse_defun(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 4 {
            return Err(anyhow!("Invalid defun: too few elements"));
        }

        let name = list[1]
            .as_atom()
            .ok_or_else(|| anyhow!("Invalid defun name"))?
            .to_string();

        let params = match &list[2] {
            SExp::List(params) => params
                .iter()
                .filter_map(|p| p.as_atom().map(String::from))
                .collect(),
            SExp::Nil => vec![],
            _ => return Err(anyhow!("Invalid defun params")),
        };

        // Find body and guard
        let mut body = list[3].clone();
        let mut guard = None;

        // Check for declare forms
        for i in 3..list.len() {
            if let SExp::List(decl) = &list[i] {
                if let Some(head) = decl.first().and_then(|h| h.as_atom()) {
                    if head.eq_ignore_ascii_case("declare") {
                        // Look for xargs with guard
                        for item in decl.iter().skip(1) {
                            if let SExp::List(xargs) = item {
                                if xargs
                                    .first()
                                    .and_then(|h| h.as_atom())
                                    .map(|s| s.eq_ignore_ascii_case("xargs"))
                                    .unwrap_or(false)
                                {
                                    // Look for :guard
                                    let mut iter = xargs.iter().skip(1);
                                    while let Some(key) = iter.next() {
                                        if key.is_atom(":guard") {
                                            if let Some(val) = iter.next() {
                                                guard = Some(val.clone());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        continue;
                    }
                }
            }
            body = list[i].clone();
        }

        Ok(Some(ACL2Event::Defun {
            name,
            params,
            body,
            guard,
        }))
    }

    /// Parse defthm event
    fn parse_defthm(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 3 {
            return Err(anyhow!("Invalid defthm: too few elements"));
        }

        let name = list[1]
            .as_atom()
            .ok_or_else(|| anyhow!("Invalid defthm name"))?
            .to_string();

        let formula = list[2].clone();

        // Parse hints and rule-classes
        let mut hints = Vec::new();
        let mut rule_classes = None;

        let mut i = 3;
        while i < list.len() {
            if let Some(key) = list[i].as_atom() {
                match key.to_lowercase().as_str() {
                    ":hints" => {
                        if i + 1 < list.len() {
                            hints = self.parse_hints(&list[i + 1])?;
                            i += 1;
                        }
                    }
                    ":rule-classes" => {
                        if i + 1 < list.len() {
                            rule_classes = Some(list[i + 1].clone());
                            i += 1;
                        }
                    }
                    _ => {}
                }
            }
            i += 1;
        }

        Ok(Some(ACL2Event::Defthm {
            name,
            formula,
            hints,
            rule_classes,
        }))
    }

    /// Parse hints
    fn parse_hints(&self, sexp: &SExp) -> Result<Vec<ACL2Hint>> {
        let list = match sexp.as_list() {
            Some(l) => l,
            None => return Ok(vec![]),
        };

        let mut hints = Vec::new();

        for item in list {
            if let SExp::List(goal_hint) = item {
                if goal_hint.len() >= 2 {
                    if let SExp::Str(goal_name) = &goal_hint[0] {
                        let mut goal_hints = Vec::new();
                        let mut j = 1;
                        while j < goal_hint.len() {
                            if let Some(key) = goal_hint[j].as_atom() {
                                if j + 1 < goal_hint.len() {
                                    let hint = self.parse_single_hint(key, &goal_hint[j + 1])?;
                                    goal_hints.push(hint);
                                    j += 1;
                                }
                            }
                            j += 1;
                        }
                        hints.push(ACL2Hint::Goal {
                            goal_name: goal_name.clone(),
                            hints: goal_hints,
                        });
                    }
                }
            }
        }

        Ok(hints)
    }

    /// Parse a single hint
    fn parse_single_hint(&self, key: &str, value: &SExp) -> Result<ACL2Hint> {
        match key.to_lowercase().as_str() {
            ":induct" => Ok(ACL2Hint::Induct(value.clone())),
            ":use" => {
                let uses = match value.as_list() {
                    Some(l) => l.clone(),
                    None => vec![value.clone()],
                };
                Ok(ACL2Hint::Use(uses))
            }
            ":expand" => {
                let expands = match value.as_list() {
                    Some(l) => l.clone(),
                    None => vec![value.clone()],
                };
                Ok(ACL2Hint::Expand(expands))
            }
            ":in-theory" => Ok(ACL2Hint::InTheory(value.clone())),
            ":cases" => {
                let cases = match value.as_list() {
                    Some(l) => l.clone(),
                    None => vec![value.clone()],
                };
                Ok(ACL2Hint::Cases(cases))
            }
            ":by" => Ok(ACL2Hint::By(value.clone())),
            ":hands-off" => {
                let fns = match value.as_list() {
                    Some(l) => l.iter().filter_map(|s| s.as_atom().map(String::from)).collect(),
                    None => value.as_atom().map(|s| vec![s.to_string()]).unwrap_or_default(),
                };
                Ok(ACL2Hint::HandsOff(fns))
            }
            ":do-not" => {
                let actions = match value.as_list() {
                    Some(l) => l.iter().filter_map(|s| s.as_atom().map(String::from)).collect(),
                    None => vec![],
                };
                Ok(ACL2Hint::DoNot(actions))
            }
            ":do-not-induct" => Ok(ACL2Hint::DoNotInduct(true)),
            _ => Ok(ACL2Hint::Other(key.to_string(), value.clone())),
        }
    }

    /// Parse defconst
    fn parse_defconst(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 3 {
            return Err(anyhow!("Invalid defconst"));
        }

        let name = list[1]
            .as_atom()
            .ok_or_else(|| anyhow!("Invalid defconst name"))?
            .to_string();

        let value = list[2].clone();

        Ok(Some(ACL2Event::Defconst { name, value }))
    }

    /// Parse defmacro
    fn parse_defmacro(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 4 {
            return Err(anyhow!("Invalid defmacro"));
        }

        let name = list[1]
            .as_atom()
            .ok_or_else(|| anyhow!("Invalid defmacro name"))?
            .to_string();

        let params = match &list[2] {
            SExp::List(params) => params
                .iter()
                .filter_map(|p| p.as_atom().map(String::from))
                .collect(),
            SExp::Nil => vec![],
            _ => vec![],
        };

        let body = list.last().cloned().unwrap_or(SExp::Nil);

        Ok(Some(ACL2Event::Defmacro { name, params, body }))
    }

    /// Parse encapsulate
    fn parse_encapsulate(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 2 {
            return Err(anyhow!("Invalid encapsulate"));
        }

        let signatures = match &list[1] {
            SExp::List(sigs) => {
                sigs.iter()
                    .filter_map(|sig| {
                        if let SExp::List(parts) = sig {
                            if parts.len() >= 2 {
                                let name = parts[0].as_atom()?.to_string();
                                return Some((name, parts[1].clone()));
                            }
                        }
                        None
                    })
                    .collect()
            }
            SExp::Nil => vec![],
            _ => vec![],
        };

        let mut events = Vec::new();
        for item in list.iter().skip(2) {
            if let Some(event) = self.parse_event(item)? {
                events.push(event);
            }
        }

        Ok(Some(ACL2Event::Encapsulate { signatures, events }))
    }

    /// Parse include-book
    fn parse_include_book(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        if list.len() < 2 {
            return Err(anyhow!("Invalid include-book"));
        }

        let name = match &list[1] {
            SExp::Str(s) => s.clone(),
            SExp::Atom(s) => s.clone(),
            _ => return Err(anyhow!("Invalid book name")),
        };

        let mut dir = None;
        let mut i = 2;
        while i < list.len() {
            if list[i].is_atom(":dir") && i + 1 < list.len() {
                dir = list[i + 1].as_atom().map(String::from);
                i += 1;
            }
            i += 1;
        }

        Ok(Some(ACL2Event::IncludeBook { name, dir }))
    }

    /// Parse mutual-recursion
    fn parse_mutual_recursion(&self, list: &[SExp]) -> Result<Option<ACL2Event>> {
        let mut events = Vec::new();
        for item in list.iter().skip(1) {
            if let Some(event) = self.parse_event(item)? {
                events.push(event);
            }
        }
        Ok(Some(ACL2Event::MutualRecursion(events)))
    }

    /// Convert ACL2 S-expression to universal Term
    fn sexp_to_term(&self, sexp: &SExp) -> Term {
        match sexp {
            SExp::Atom(s) => {
                if s.starts_with(':') {
                    Term::Const(s.clone())
                } else if s.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                    Term::Const(s.clone())
                } else {
                    Term::Var(s.clone())
                }
            }
            SExp::Str(s) => Term::Const(format!("\"{}\"", s)),
            SExp::Num(n) => Term::Const(n.to_string()),
            SExp::Nil => Term::Const("nil".to_string()),
            SExp::Quote(inner) => Term::App {
                func: Box::new(Term::Const("quote".to_string())),
                args: vec![self.sexp_to_term(inner)],
            },
            SExp::List(items) => {
                if items.is_empty() {
                    Term::Const("nil".to_string())
                } else {
                    let head = &items[0];

                    // Check for special forms
                    if let Some(name) = head.as_atom() {
                        match name.to_lowercase().as_str() {
                            "if" => {
                                if items.len() >= 4 {
                                    return Term::App {
                                        func: Box::new(Term::Const("if".to_string())),
                                        args: items[1..4].iter().map(|i| self.sexp_to_term(i)).collect(),
                                    };
                                }
                            }
                            "let" | "let*" => {
                                if items.len() >= 3 {
                                    // Simplify let to lambda application
                                    let body = self.sexp_to_term(items.last().unwrap());
                                    return body;
                                }
                            }
                            "lambda" => {
                                if items.len() >= 3 {
                                    let params = match &items[1] {
                                        SExp::List(ps) => ps
                                            .iter()
                                            .filter_map(|p| p.as_atom().map(String::from))
                                            .collect::<Vec<_>>(),
                                        _ => vec![],
                                    };
                                    let body = self.sexp_to_term(items.last().unwrap());

                                    // Build nested lambdas
                                    let mut result = body;
                                    for param in params.into_iter().rev() {
                                        result = Term::Lambda {
                                            param,
                                            param_type: None,
                                            body: Box::new(result),
                                        };
                                    }
                                    return result;
                                }
                            }
                            "implies" => {
                                if items.len() >= 3 {
                                    return Term::Pi {
                                        param: "_".to_string(),
                                        param_type: Box::new(self.sexp_to_term(&items[1])),
                                        body: Box::new(self.sexp_to_term(&items[2])),
                                    };
                                }
                            }
                            "and" | "or" | "not" | "equal" | "+" | "-" | "*" | "/" => {
                                return Term::App {
                                    func: Box::new(Term::Const(name.to_string())),
                                    args: items[1..].iter().map(|i| self.sexp_to_term(i)).collect(),
                                };
                            }
                            _ => {}
                        }
                    }

                    // Generic function application
                    Term::App {
                        func: Box::new(self.sexp_to_term(head)),
                        args: items[1..].iter().map(|i| self.sexp_to_term(i)).collect(),
                    }
                }
            }
        }
    }

    /// Convert core Pattern to ACL2 S-expression
    fn pattern_to_sexp(&self, pattern: &crate::core::Pattern) -> SExp {
        match pattern {
            crate::core::Pattern::Wildcard => SExp::Atom("_".to_string()),
            crate::core::Pattern::Var(name) => SExp::Atom(name.clone()),
            crate::core::Pattern::Constructor { name, args } => {
                if args.is_empty() {
                    SExp::Atom(name.clone())
                } else {
                    let mut items = vec![SExp::Atom(name.clone())];
                    items.extend(args.iter().map(|a| self.pattern_to_sexp(a)));
                    SExp::List(items)
                }
            }
        }
    }

    /// Convert universal Term to ACL2 S-expression
    fn term_to_sexp(&self, term: &Term) -> SExp {
        match term {
            Term::Var(name) => SExp::Atom(name.clone()),
            Term::Const(name) => SExp::Atom(name.clone()),
            Term::Universe(_) => SExp::Atom("T".to_string()),
            Term::App { func, args } => {
                let mut items = vec![self.term_to_sexp(func)];
                items.extend(args.iter().map(|a| self.term_to_sexp(a)));
                SExp::List(items)
            }
            Term::Lambda { param, body, .. } => {
                SExp::List(vec![
                    SExp::Atom("lambda".to_string()),
                    SExp::List(vec![SExp::Atom(param.clone())]),
                    self.term_to_sexp(body),
                ])
            }
            Term::Pi { param, param_type, body } => {
                if param == "_" {
                    // Non-dependent: implies
                    SExp::List(vec![
                        SExp::Atom("implies".to_string()),
                        self.term_to_sexp(param_type),
                        self.term_to_sexp(body),
                    ])
                } else {
                    // Dependent: forall (not directly supported, approximate)
                    SExp::List(vec![
                        SExp::Atom("implies".to_string()),
                        self.term_to_sexp(param_type),
                        self.term_to_sexp(body),
                    ])
                }
            }
            Term::Let { name, value, body, .. } => {
                SExp::List(vec![
                    SExp::Atom("let".to_string()),
                    SExp::List(vec![SExp::List(vec![
                        SExp::Atom(name.clone()),
                        self.term_to_sexp(value),
                    ])]),
                    self.term_to_sexp(body),
                ])
            }
            Term::Match { scrutinee, branches, .. } => {
                // ACL2 doesn't have pattern matching, approximate with cond
                let mut cond_clauses = Vec::new();
                for (pattern, body) in branches {
                    let pattern_sexp = self.pattern_to_sexp(pattern);
                    cond_clauses.push(SExp::List(vec![
                        SExp::List(vec![
                            SExp::Atom("equal".to_string()),
                            self.term_to_sexp(scrutinee),
                            pattern_sexp,
                        ]),
                        self.term_to_sexp(body),
                    ]));
                }
                let mut items = vec![SExp::Atom("cond".to_string())];
                items.extend(cond_clauses);
                SExp::List(items)
            }
            Term::Hole(name) => {
                SExp::List(vec![
                    SExp::Atom("error".to_string()),
                    SExp::Str(format!("hole: {}", if name.is_empty() { "_" } else { name })),
                ])
            }
            Term::Type(level) => {
                SExp::List(vec![
                    SExp::Atom("quote".to_string()),
                    SExp::Atom(format!("TYPE-{}", level)),
                ])
            }
            Term::Sort(level) => {
                SExp::List(vec![
                    SExp::Atom("quote".to_string()),
                    SExp::Atom(format!("SORT-{}", level)),
                ])
            }
            Term::Fix { name, body, .. } => {
                // ACL2 doesn't have fix, approximate with a recursive label
                SExp::List(vec![
                    SExp::Atom("labels".to_string()),
                    SExp::List(vec![
                        SExp::List(vec![
                            SExp::Atom(name.clone()),
                            SExp::List(vec![]),
                            self.term_to_sexp(body),
                        ]),
                    ]),
                    SExp::Atom(name.clone()),
                ])
            }
            Term::Meta(id) => {
                SExp::List(vec![
                    SExp::Atom("error".to_string()),
                    SExp::Str(format!("meta-{}", id)),
                ])
            }
            Term::ProverSpecific { data, .. } => {
                // Try to represent prover-specific data
                SExp::List(vec![
                    SExp::Atom("quote".to_string()),
                    SExp::Atom(data.to_string()),
                ])
            }
        }
    }

    /// Convert universal Tactic to ACL2 hint
    fn tactic_to_hint(&self, tactic: &Tactic) -> Option<ACL2Hint> {
        match tactic {
            Tactic::Induction(term) => {
                Some(ACL2Hint::Induct(self.term_to_sexp(term)))
            }
            Tactic::Apply(thm) => {
                Some(ACL2Hint::Use(vec![SExp::Atom(thm.clone())]))
            }
            Tactic::Rewrite(thm) => {
                Some(ACL2Hint::Use(vec![SExp::Atom(thm.clone())]))
            }
            Tactic::Cases(term) => {
                Some(ACL2Hint::Cases(vec![self.term_to_sexp(term)]))
            }
            Tactic::Simplify => {
                Some(ACL2Hint::InTheory(SExp::List(vec![
                    SExp::Atom("enable".to_string()),
                ])))
            }
            Tactic::Custom { command, args, .. } => {
                match command.as_str() {
                    "induct" => {
                        let sexp = if args.is_empty() {
                            SExp::Atom("t".to_string())
                        } else {
                            SExp::parse(&args.join(" ")).unwrap_or(SExp::Nil)
                        };
                        Some(ACL2Hint::Induct(sexp))
                    }
                    "use" => {
                        let uses = args.iter().map(|a| SExp::Atom(a.clone())).collect();
                        Some(ACL2Hint::Use(uses))
                    }
                    "expand" => {
                        let expands = args.iter().map(|a| SExp::Atom(a.clone())).collect();
                        Some(ACL2Hint::Expand(expands))
                    }
                    "enable" | "disable" => {
                        let fns: Vec<SExp> = args.iter().map(|a| SExp::Atom(a.clone())).collect();
                        let theory = SExp::List(vec![
                            SExp::Atom(command.clone()),
                            SExp::List(fns),
                        ]);
                        Some(ACL2Hint::InTheory(theory))
                    }
                    "hands-off" => {
                        Some(ACL2Hint::HandsOff(args.clone()))
                    }
                    "do-not-induct" => {
                        Some(ACL2Hint::DoNotInduct(true))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Convert ACL2 hint to Lisp string for goal
    fn hint_to_lisp(&self, hint: &ACL2Hint, goal_name: &str) -> String {
        let hint_str = match hint {
            ACL2Hint::Induct(sexp) => format!(":induct {}", sexp.to_lisp()),
            ACL2Hint::Use(uses) => {
                let uses_str = uses.iter().map(|u| u.to_lisp()).collect::<Vec<_>>().join(" ");
                format!(":use ({})", uses_str)
            }
            ACL2Hint::Expand(expands) => {
                let exp_str = expands.iter().map(|e| e.to_lisp()).collect::<Vec<_>>().join(" ");
                format!(":expand ({})", exp_str)
            }
            ACL2Hint::InTheory(theory) => format!(":in-theory {}", theory.to_lisp()),
            ACL2Hint::Cases(cases) => {
                let cases_str = cases.iter().map(|c| c.to_lisp()).collect::<Vec<_>>().join(" ");
                format!(":cases ({})", cases_str)
            }
            ACL2Hint::By(lemma) => format!(":by {}", lemma.to_lisp()),
            ACL2Hint::HandsOff(fns) => {
                format!(":hands-off ({})", fns.join(" "))
            }
            ACL2Hint::DoNot(actions) => {
                format!(":do-not '({})", actions.join(" "))
            }
            ACL2Hint::DoNotInduct(_) => ":do-not-induct t".to_string(),
            ACL2Hint::Goal { hints, .. } => {
                hints.iter().map(|h| self.hint_to_lisp(h, goal_name)).collect::<Vec<_>>().join(" ")
            }
            ACL2Hint::Other(key, value) => format!("{} {}", key, value.to_lisp()),
        };

        format!("(\"{}\" {})", goal_name, hint_str)
    }

    /// Generate ACL2 defthm with hints
    fn generate_defthm(&self, name: &str, formula: &Term, hints: &[ACL2Hint]) -> String {
        let formula_sexp = self.term_to_sexp(formula);

        if hints.is_empty() {
            format!("(defthm {} {})", name, formula_sexp.to_lisp())
        } else {
            let hints_str = hints
                .iter()
                .map(|h| self.hint_to_lisp(h, "Goal"))
                .collect::<Vec<_>>()
                .join("\n    ");
            format!(
                "(defthm {}\n  {}\n  :hints ({}))",
                name,
                formula_sexp.to_lisp(),
                hints_str
            )
        }
    }
}

/// Find the end position of an S-expression in the string
fn find_sexp_end(s: &str) -> Result<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut escape = false;

    for (i, c) in s.char_indices() {
        if escape {
            escape = false;
            continue;
        }

        match c {
            '\\' if in_string => escape = true,
            '"' => in_string = !in_string,
            '(' if !in_string => depth += 1,
            ')' if !in_string => {
                depth -= 1;
                if depth == 0 {
                    return Ok(i + 1);
                }
            }
            _ => {}
        }
    }

    Err(anyhow!("Unmatched parentheses"))
}

#[async_trait]
impl ProverBackend for ACL2Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::ACL2
    }

    async fn version(&self) -> Result<String> {
        // ACL2 outputs version on startup
        let output = Command::new(
            self.config
                .executable
                .to_str()
                .filter(|s| !s.is_empty())
                .unwrap_or("acl2"),
        )
        .arg("--help")
        .output()
        .await
        .context("Failed to get ACL2 version")?;

        let version_str = String::from_utf8_lossy(&output.stdout);
        // Parse version from output
        for line in version_str.lines() {
            if line.contains("ACL2") && line.contains("Version") {
                return Ok(line.to_string());
            }
        }

        Ok("ACL2 (version unknown)".to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read ACL2 file")?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let events = self.parse_file_content(content)?;

        let mut context = Context::default();
        let mut goals = Vec::new();

        for event in events {
            match event {
                ACL2Event::Defun {
                    name,
                    params: _,
                    body,
                    guard: _,
                } => {
                    let body_term = self.sexp_to_term(&body);
                    context.definitions.push(Definition {
                        name,
                        ty: Term::Universe(0), // ACL2 doesn't have explicit types
                        body: body_term,
                    });
                }
                ACL2Event::Defthm {
                    name,
                    formula,
                    hints,
                    rule_classes: _,
                } => {
                    let formula_term = self.sexp_to_term(&formula);

                    // Convert hints to tactics
                    let proof: Vec<Tactic> = hints
                        .iter()
                        .flat_map(|h| match h {
                            ACL2Hint::Goal { hints, .. } => hints
                                .iter()
                                .filter_map(|gh| self.hint_to_tactic(gh))
                                .collect::<Vec<_>>(),
                            _ => self.hint_to_tactic(h).into_iter().collect(),
                        })
                        .collect();

                    context.theorems.push(Theorem {
                        name: name.clone(),
                        statement: formula_term.clone(),
                        proof: if proof.is_empty() { None } else { Some(proof) },
                        aspects: vec![],
                    });

                    goals.push(Goal {
                        id: format!("goal_{}", name),
                        target: formula_term,
                        hypotheses: vec![],
                    });
                }
                ACL2Event::Defconst { name, value } => {
                    let value_term = self.sexp_to_term(&value);
                    context.definitions.push(Definition {
                        name,
                        ty: Term::Universe(0),
                        body: value_term,
                    });
                }
                _ => {}
            }
        }

        Ok(ProofState {
            goals,
            context,
            proof_script: vec![],
            metadata: HashMap::new(),
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // Convert tactic to ACL2 hint
        let hint = match self.tactic_to_hint(tactic) {
            Some(h) => h,
            None => {
                return Ok(TacticResult::Error(format!(
                    "Tactic {:?} not supported in ACL2",
                    tactic
                )));
            }
        };

        // If we have goals, try to prove with the hint
        if state.goals.is_empty() {
            return Ok(TacticResult::QED);
        }

        let goal = &state.goals[0];

        // Generate defthm with hint
        let defthm = self.generate_defthm(
            &format!("echidna_goal_{}", uuid::Uuid::new_v4().to_string().replace('-', "")),
            &goal.target,
            &[hint],
        );

        // Try to prove in ACL2
        match self.send_command(&defthm).await {
            Ok(output) => {
                if output.contains("Q.E.D.") || output.contains("Summary") && output.contains("proved") {
                    // Goal proved
                    let mut new_state = state.clone();
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());

                    if new_state.goals.is_empty() {
                        Ok(TacticResult::QED)
                    } else {
                        Ok(TacticResult::Success(new_state))
                    }
                } else if output.contains("FAILED") || output.contains("Error") {
                    Ok(TacticResult::Error(format!("ACL2 proof failed: {}", output)))
                } else {
                    // Proof in progress
                    let mut new_state = state.clone();
                    new_state.proof_script.push(tactic.clone());
                    Ok(TacticResult::Success(new_state))
                }
            }
            Err(e) => Ok(TacticResult::Error(e.to_string())),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.goals.is_empty() {
            return Ok(true);
        }
        // Export and check
        let content = self.export(state).await?;

        // Write to temp file
        let temp_file = std::env::temp_dir().join(format!(
            "echidna_acl2_verify_{}.lisp",
            uuid::Uuid::new_v4()
        ));

        tokio::fs::write(&temp_file, &content)
            .await
            .context("Failed to write temp file")?;

        // Run ACL2 in batch mode
        let exec = self
            .config
            .executable
            .to_str()
            .filter(|s| !s.is_empty())
            .unwrap_or("acl2");

        let stdin_file = std::fs::File::open(&temp_file)
            .context("Failed to open temp file for ACL2 stdin")?;

        let output = Command::new(exec)
            .stdin(std::process::Stdio::from(stdin_file))
            .output()
            .await
            .context("Failed to run ACL2")?;

        // Clean up
        let _ = tokio::fs::remove_file(&temp_file).await;

        let output_str = String::from_utf8_lossy(&output.stdout);
        let err_str = String::from_utf8_lossy(&output.stderr);
        let combined = format!("{}{}", output_str, err_str);
        Ok(combined.contains("Q.E.D.") || (combined.contains("Summary") && !combined.contains("FAILED")))
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        // Header comment
        output.push_str("; Generated by ECHIDNA\n");
        output.push_str("; ACL2 proof script\n\n");

        // Export definitions
        for def in &state.context.definitions {
            let body_sexp = self.term_to_sexp(&def.body);
            output.push_str(&format!(
                "(defun {} ()\n  {})\n\n",
                def.name,
                body_sexp.to_lisp()
            ));
        }

        // Export theorems
        for thm in &state.context.theorems {
            let formula_sexp = self.term_to_sexp(&thm.statement);

            if let Some(proof) = &thm.proof {
                let hints: Vec<ACL2Hint> = proof
                    .iter()
                    .filter_map(|t| self.tactic_to_hint(t))
                    .collect();

                output.push_str(&self.generate_defthm(&thm.name, &thm.statement, &hints));
            } else {
                output.push_str(&format!(
                    "(defthm {}\n  {})\n",
                    thm.name,
                    formula_sexp.to_lisp()
                ));
            }
            output.push_str("\n\n");
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        if state.goals.is_empty() {
            return Ok(suggestions);
        }

        let goal = &state.goals[0];

        // Analyze goal structure for hints
        match &goal.target {
            Term::Pi { .. } => {
                // Implication - try proving directly or by induction
                suggestions.push(Tactic::Custom {
                    prover: "acl2".to_string(),
                    command: "do-not-induct".to_string(),
                    args: vec![],
                });
            }
            Term::App { func, args } => {
                if let Term::Const(name) = func.as_ref() {
                    match name.as_str() {
                        "equal" if args.len() == 2 => {
                            // Equality - try simplification or expansion
                            suggestions.push(Tactic::Simplify);
                            suggestions.push(Tactic::Custom {
                                prover: "acl2".to_string(),
                                command: "expand".to_string(),
                                args: vec![],
                            });
                        }
                        "and" => {
                            suggestions.push(Tactic::Custom {
                                prover: "acl2".to_string(),
                                command: "do-not-induct".to_string(),
                                args: vec![],
                            });
                        }
                        _ => {
                            // Try induction on first argument
                            if let Some(arg) = args.first() {
                                suggestions.push(Tactic::Induction(arg.clone()));
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        // Generic suggestions
        suggestions.push(Tactic::Custom {
            prover: "acl2".to_string(),
            command: "enable".to_string(),
            args: vec![],
        });

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Use ACL2's :pl command to print lemmas
        let cmd = format!("(pe '{})", pattern);
        let output = self.send_command(&cmd).await?;

        // Parse output for theorem names
        let theorems: Vec<String> = output
            .lines()
            .filter(|line| line.contains("DEFTHM") || line.contains("defthm"))
            .map(|line| {
                line.split_whitespace()
                    .nth(1)
                    .unwrap_or("")
                    .trim_matches(|c| c == '(' || c == ')')
                    .to_string()
            })
            .filter(|s| !s.is_empty())
            .collect();

        Ok(theorems)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

impl ACL2Backend {
    /// Convert ACL2 hint to universal Tactic
    fn hint_to_tactic(&self, hint: &ACL2Hint) -> Option<Tactic> {
        match hint {
            ACL2Hint::Induct(sexp) => {
                let term = self.sexp_to_term(sexp);
                Some(Tactic::Induction(term))
            }
            ACL2Hint::Use(uses) => {
                if let Some(first) = uses.first() {
                    if let Some(name) = first.as_atom() {
                        return Some(Tactic::Apply(name.to_string()));
                    }
                }
                None
            }
            ACL2Hint::Expand(_) => Some(Tactic::Custom {
                prover: "acl2".to_string(),
                command: "expand".to_string(),
                args: vec![],
            }),
            ACL2Hint::InTheory(_) => Some(Tactic::Simplify),
            ACL2Hint::Cases(cases) => {
                if let Some(first) = cases.first() {
                    let term = self.sexp_to_term(first);
                    return Some(Tactic::Cases(term));
                }
                None
            }
            ACL2Hint::By(lemma) => {
                if let Some(name) = lemma.as_atom() {
                    return Some(Tactic::Apply(name.to_string()));
                }
                None
            }
            ACL2Hint::HandsOff(fns) => Some(Tactic::Custom {
                prover: "acl2".to_string(),
                command: "hands-off".to_string(),
                args: fns.clone(),
            }),
            ACL2Hint::DoNot(actions) => Some(Tactic::Custom {
                prover: "acl2".to_string(),
                command: "do-not".to_string(),
                args: actions.clone(),
            }),
            ACL2Hint::DoNotInduct(_) => Some(Tactic::Custom {
                prover: "acl2".to_string(),
                command: "do-not-induct".to_string(),
                args: vec![],
            }),
            ACL2Hint::Goal { hints, .. } => {
                // Return first non-None tactic from hints
                for h in hints {
                    if let Some(t) = self.hint_to_tactic(h) {
                        return Some(t);
                    }
                }
                None
            }
            ACL2Hint::Other(key, _) => Some(Tactic::Custom {
                prover: "acl2".to_string(),
                command: key.clone(),
                args: vec![],
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sexp_parse_atom() {
        let sexp = SExp::parse("foo").unwrap();
        assert!(matches!(sexp, SExp::Atom(s) if s == "foo"));
    }

    #[test]
    fn test_sexp_parse_number() {
        let sexp = SExp::parse("42").unwrap();
        assert!(matches!(sexp, SExp::Num(42)));
    }

    #[test]
    fn test_sexp_parse_list() {
        let sexp = SExp::parse("(a b c)").unwrap();
        if let SExp::List(items) = sexp {
            assert_eq!(items.len(), 3);
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_sexp_parse_nested() {
        let sexp = SExp::parse("(defun foo (x) (+ x 1))").unwrap();
        if let SExp::List(items) = sexp {
            assert_eq!(items.len(), 4);
            assert!(items[0].is_atom("defun"));
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_sexp_parse_quote() {
        let sexp = SExp::parse("'foo").unwrap();
        assert!(matches!(sexp, SExp::Quote(_)));
    }

    #[test]
    fn test_sexp_to_lisp() {
        let sexp = SExp::List(vec![
            SExp::Atom("defun".to_string()),
            SExp::Atom("foo".to_string()),
            SExp::List(vec![SExp::Atom("x".to_string())]),
            SExp::List(vec![
                SExp::Atom("+".to_string()),
                SExp::Atom("x".to_string()),
                SExp::Num(1),
            ]),
        ]);
        let lisp = sexp.to_lisp();
        assert_eq!(lisp, "(defun foo (x) (+ x 1))");
    }

    #[test]
    fn test_parse_defun() {
        let backend = ACL2Backend::new(ProverConfig::default());
        let content = "(defun square (x) (* x x))";
        let events = backend.parse_file_content(content).unwrap();

        assert_eq!(events.len(), 1);
        if let ACL2Event::Defun { name, params, .. } = &events[0] {
            assert_eq!(name, "square");
            assert_eq!(params, &vec!["x".to_string()]);
        } else {
            panic!("Expected Defun");
        }
    }

    #[test]
    fn test_parse_defthm() {
        let backend = ACL2Backend::new(ProverConfig::default());
        let content = r#"
            (defthm square-positive
              (implies (rationalp x)
                       (<= 0 (square x)))
              :hints (("Goal" :induct t)))
        "#;
        let events = backend.parse_file_content(content).unwrap();

        assert_eq!(events.len(), 1);
        if let ACL2Event::Defthm { name, hints, .. } = &events[0] {
            assert_eq!(name, "square-positive");
            assert!(!hints.is_empty());
        } else {
            panic!("Expected Defthm");
        }
    }

    #[test]
    fn test_sexp_to_term() {
        let backend = ACL2Backend::new(ProverConfig::default());

        let sexp = SExp::parse("(implies a b)").unwrap();
        let term = backend.sexp_to_term(&sexp);
        assert!(matches!(term, Term::Pi { .. }));

        let sexp = SExp::parse("(+ x y)").unwrap();
        let term = backend.sexp_to_term(&sexp);
        assert!(matches!(term, Term::App { .. }));
    }

    #[test]
    fn test_term_to_sexp() {
        let backend = ACL2Backend::new(ProverConfig::default());

        let term = Term::App {
            func: Box::new(Term::Const("+".to_string())),
            args: vec![Term::Var("x".to_string()), Term::Var("y".to_string())],
        };

        let sexp = backend.term_to_sexp(&term);
        let lisp = sexp.to_lisp();
        assert_eq!(lisp, "(+ x y)");
    }

    #[tokio::test]
    async fn test_parse_string() {
        let backend = ACL2Backend::new(ProverConfig::default());

        let content = r#"
            (defun double (x) (+ x x))
            (defthm double-even
              (implies (integerp x)
                       (integerp (double x))))
        "#;

        let state = backend.parse_string(content).await.unwrap();

        assert_eq!(state.context.definitions.len(), 1);
        assert_eq!(state.context.definitions[0].name, "double");

        assert_eq!(state.context.theorems.len(), 1);
        assert_eq!(state.context.theorems[0].name, "double-even");
    }
}
