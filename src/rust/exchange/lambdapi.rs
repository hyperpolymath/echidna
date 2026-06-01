// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Lambdapi proof exchange format.
//!
//! Lambdapi (https://github.com/Deducteam/lambdapi) is Dedukti's
//! successor — a logical framework based on the lambda-Pi calculus
//! modulo rewriting, upward-compatible with Dedukti syntax but with
//! inferable types and a tactic language. This module ships an
//! independent structured representation plus syntactic translators
//! to and from Dedukti so existing `dedukti.rs` consumers can upgrade
//! without losing fidelity.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

/// Error type for Lambdapi exchange.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExchangeError {
    UnsupportedDialect(String),
    ParseError(String),
    TranslationError(String),
    EmptyProblem,
}

impl std::fmt::Display for ExchangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExchangeError::UnsupportedDialect(d) => write!(f, "unsupported dialect: {}", d),
            ExchangeError::ParseError(m) => write!(f, "parse error: {}", m),
            ExchangeError::TranslationError(m) => write!(f, "translation error: {}", m),
            ExchangeError::EmptyProblem => write!(f, "empty module"),
        }
    }
}

impl std::error::Error for ExchangeError {}

/// The kind / modifier of a Lambdapi symbol declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolKind {
    Constant,
    Definition,
    Theorem,
    Symbol,
    Injective,
    Sequential,
    Private,
    Protected,
}

impl SymbolKind {
    fn modifier(&self) -> &'static str {
        match self {
            SymbolKind::Constant => "constant ",
            SymbolKind::Definition => "",
            SymbolKind::Theorem => "opaque ",
            SymbolKind::Symbol => "",
            SymbolKind::Injective => "injective ",
            SymbolKind::Sequential => "sequential ",
            SymbolKind::Private => "private ",
            SymbolKind::Protected => "protected ",
        }
    }

    fn parse_modifier(token: &str) -> Option<Self> {
        match token {
            "constant" => Some(SymbolKind::Constant),
            "opaque" => Some(SymbolKind::Theorem),
            "injective" => Some(SymbolKind::Injective),
            "sequential" => Some(SymbolKind::Sequential),
            "private" => Some(SymbolKind::Private),
            "protected" => Some(SymbolKind::Protected),
            _ => None,
        }
    }
}

/// A Lambdapi symbol declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LambdapiSymbol {
    pub name: String,
    pub kind: SymbolKind,
    pub type_expr: String,
    pub body: Option<String>,
}

/// A Lambdapi rewrite rule: `rule lhs ↪ rhs;`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LambdapiRule {
    pub lhs: String,
    pub rhs: String,
}

/// A Lambdapi module.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LambdapiModule {
    pub name: String,
    pub requires: Vec<String>,
    pub opens: Vec<String>,
    pub symbols: Vec<LambdapiSymbol>,
    pub rules: Vec<LambdapiRule>,
}

/// Lambdapi exchange driver.
#[derive(Debug, Clone, Default)]
pub struct LambdapiExchange;

impl LambdapiExchange {
    pub fn new() -> Self {
        Self
    }

    /// Import a Lambdapi module from source text.
    pub fn import(content: &str) -> Result<LambdapiModule, ExchangeError> {
        let mut module = LambdapiModule {
            name: String::new(),
            requires: vec![],
            opens: vec![],
            symbols: vec![],
            rules: vec![],
        };

        for raw_stmt in split_statements(content) {
            let stmt = raw_stmt.trim();
            if stmt.is_empty() {
                continue;
            }
            if let Some(rest) = stmt.strip_prefix("require open ") {
                module.requires.push(rest.trim().to_string());
                module.opens.push(rest.trim().to_string());
            } else if let Some(rest) = stmt.strip_prefix("require ") {
                module.requires.push(rest.trim().to_string());
            } else if let Some(rest) = stmt.strip_prefix("open ") {
                module.opens.push(rest.trim().to_string());
            } else if let Some(rest) = stmt.strip_prefix("rule ") {
                let rule = parse_rule(rest)?;
                module.rules.push(rule);
            } else if stmt.starts_with("symbol ")
                || SymbolKind::parse_modifier(
                    stmt.split_whitespace().next().unwrap_or(""),
                )
                .is_some()
            {
                let sym = parse_symbol(stmt)?;
                module.symbols.push(sym);
            } else {
                // Tolerate unknown top-level directives (set, builtin, etc.)
                continue;
            }
        }

        if module.symbols.is_empty() && module.rules.is_empty() && module.requires.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        Ok(module)
    }

    /// Emit a Lambdapi module to source text.
    pub fn export(module: &LambdapiModule) -> Result<String, ExchangeError> {
        let mut out = String::new();
        for r in &module.requires {
            if module.opens.iter().any(|o| o == r) {
                out.push_str(&format!("require open {};\n", r));
            } else {
                out.push_str(&format!("require {};\n", r));
            }
        }
        for o in &module.opens {
            if !module.requires.iter().any(|r| r == o) {
                out.push_str(&format!("open {};\n", o));
            }
        }
        if !module.requires.is_empty() || !module.opens.is_empty() {
            out.push('\n');
        }
        for s in &module.symbols {
            let modifier = s.kind.modifier();
            match &s.body {
                Some(body) => out.push_str(&format!(
                    "{}symbol {} : {} ≔ {};\n",
                    modifier, s.name, s.type_expr, body
                )),
                None => out.push_str(&format!(
                    "{}symbol {} : {};\n",
                    modifier, s.name, s.type_expr
                )),
            }
        }
        for r in &module.rules {
            out.push_str(&format!("rule {} ↪ {};\n", r.lhs, r.rhs));
        }
        if out.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        Ok(out)
    }

    /// Best-effort syntactic migration from Dedukti to Lambdapi.
    /// Major transforms:
    ///   `def name := body.`    →  `symbol name ≔ body;`
    ///   `def name : T := b.`   →  `symbol name : T ≔ b;`
    ///   `[x] lhs --> rhs.`     →  `rule lhs ↪ rhs;`
    ///   trailing `.`           →  trailing `;`
    pub fn translate_from_dedukti(dk: &str) -> Result<String, ExchangeError> {
        let mut out = String::new();
        for line in dk.lines() {
            let l = line.trim_end();
            let l = l.trim_end_matches('.');
            if l.trim().is_empty() {
                out.push('\n');
                continue;
            }
            let trimmed = l.trim();
            if let Some(rest) = trimmed.strip_prefix("def ") {
                out.push_str("symbol ");
                out.push_str(&rest.replace(":=", "≔"));
                out.push_str(";\n");
            } else if trimmed.starts_with('[') {
                // [x] lhs --> rhs
                if let Some(close) = trimmed.find(']') {
                    let body = trimmed[close + 1..].trim();
                    let parts: Vec<&str> = body.splitn(2, "-->").collect();
                    if parts.len() == 2 {
                        out.push_str(&format!(
                            "rule {} ↪ {};\n",
                            parts[0].trim(),
                            parts[1].trim()
                        ));
                        continue;
                    }
                }
                out.push_str(trimmed);
                out.push_str(";\n");
            } else if let Some(rest) = trimmed.strip_prefix("#REQUIRE ") {
                out.push_str(&format!("require {};\n", rest.trim()));
            } else {
                out.push_str(trimmed);
                out.push_str(";\n");
            }
        }
        Ok(out)
    }

    /// Reverse-direction syntactic migration (Lambdapi → Dedukti). Loses
    /// modifiers beyond `constant`; opaque/private/protected become plain
    /// definitions in the output.
    pub fn translate_to_dedukti(lp: &str) -> Result<String, ExchangeError> {
        let mut out = String::new();
        for stmt in split_statements(lp) {
            let trimmed = stmt.trim();
            if trimmed.is_empty() {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("require open ") {
                out.push_str(&format!("#REQUIRE {}.\n", rest.trim()));
            } else if let Some(rest) = trimmed.strip_prefix("require ") {
                out.push_str(&format!("#REQUIRE {}.\n", rest.trim()));
            } else if let Some(rest) = trimmed.strip_prefix("rule ") {
                let parts: Vec<&str> = rest.splitn(2, "↪").collect();
                if parts.len() == 2 {
                    out.push_str(&format!(
                        "[] {} --> {}.\n",
                        parts[0].trim(),
                        parts[1].trim()
                    ));
                } else {
                    out.push_str(rest);
                    out.push_str(".\n");
                }
            } else if trimmed.starts_with("symbol ") || trimmed.starts_with("constant symbol ") {
                let body = trimmed
                    .trim_start_matches("constant ")
                    .trim_start_matches("symbol ")
                    .trim();
                if body.contains('≔') {
                    let mapped = body.replace('≔', ":=");
                    out.push_str(&format!("def {}.\n", mapped));
                } else {
                    out.push_str(&format!("{} : Type.\n", body));
                }
            } else {
                out.push_str(trimmed);
                out.push_str(".\n");
            }
        }
        Ok(out)
    }
}

/// Split a Lambdapi source file on `;` at depth 0.
fn split_statements(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut buf = String::new();
    for c in s.chars() {
        match c {
            '(' | '[' => {
                depth += 1;
                buf.push(c);
            },
            ')' | ']' => {
                depth -= 1;
                buf.push(c);
            },
            ';' if depth == 0 => {
                let t = buf.trim().to_string();
                if !t.is_empty() {
                    out.push(t);
                }
                buf.clear();
            },
            _ => buf.push(c),
        }
    }
    let tail = buf.trim().to_string();
    if !tail.is_empty() {
        out.push(tail);
    }
    out
}

fn parse_symbol(stmt: &str) -> Result<LambdapiSymbol, ExchangeError> {
    // Strip leading modifiers.
    let mut rest = stmt.trim().to_string();
    let mut kind = SymbolKind::Symbol;
    loop {
        let first = rest.split_whitespace().next().unwrap_or("");
        if first == "symbol" {
            rest = rest[first.len()..].trim().to_string();
            break;
        }
        if let Some(k) = SymbolKind::parse_modifier(first) {
            kind = k;
            rest = rest[first.len()..].trim().to_string();
        } else {
            return Err(ExchangeError::ParseError(format!(
                "expected modifier or 'symbol', got: {}",
                first
            )));
        }
    }
    // rest now starts with: name : T [≔ body]
    let (name, after_name) = match rest.find(':') {
        Some(i) => (rest[..i].trim().to_string(), rest[i + 1..].trim().to_string()),
        None => {
            return Err(ExchangeError::ParseError(format!(
                "symbol missing ':' — {}",
                rest
            )));
        },
    };
    let (type_expr, body) = match after_name.find('≔') {
        Some(i) => {
            let t = after_name[..i].trim().to_string();
            // ≔ is 3 bytes in UTF-8.
            let b = after_name[i + '≔'.len_utf8()..].trim().to_string();
            (t, Some(b))
        },
        None => (after_name, None),
    };
    Ok(LambdapiSymbol {
        name,
        kind,
        type_expr,
        body,
    })
}

fn parse_rule(stmt: &str) -> Result<LambdapiRule, ExchangeError> {
    let parts: Vec<&str> = stmt.splitn(2, '↪').collect();
    if parts.len() != 2 {
        return Err(ExchangeError::ParseError(format!(
            "rule missing '↪': {}",
            stmt
        )));
    }
    Ok(LambdapiRule {
        lhs: parts[0].trim().to_string(),
        rhs: parts[1].trim().to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_minimal_symbol() {
        let src = "symbol foo : T;";
        let module = LambdapiExchange::import(src).unwrap();
        assert_eq!(module.symbols.len(), 1);
        assert_eq!(module.symbols[0].name, "foo");
        assert_eq!(module.symbols[0].type_expr, "T");
        assert!(module.symbols[0].body.is_none());
    }

    #[test]
    fn test_roundtrip_symbol_with_body() {
        let src = "symbol id : T → T ≔ λ x, x;";
        let module = LambdapiExchange::import(src).unwrap();
        assert_eq!(module.symbols.len(), 1);
        assert!(module.symbols[0].body.is_some());
        let out = LambdapiExchange::export(&module).unwrap();
        let reparsed = LambdapiExchange::import(&out).unwrap();
        assert_eq!(reparsed.symbols[0].name, "id");
        assert!(reparsed.symbols[0].body.is_some());
    }

    #[test]
    fn test_dedukti_to_lambdapi_migration() {
        let dk = "def f := (x => x).\n[x] plus 0 x --> x.\n";
        let lp = LambdapiExchange::translate_from_dedukti(dk).unwrap();
        assert!(lp.contains("symbol f"));
        assert!(lp.contains("≔"));
        assert!(lp.contains("rule plus 0 x ↪ x;"));
    }

    #[test]
    fn test_constant_symbol_modifier_roundtrip() {
        let src = "constant symbol Nat : TYPE;";
        let module = LambdapiExchange::import(src).unwrap();
        assert_eq!(module.symbols.len(), 1);
        assert_eq!(module.symbols[0].kind, SymbolKind::Constant);
        let out = LambdapiExchange::export(&module).unwrap();
        assert!(out.contains("constant symbol Nat"));
    }

    #[test]
    fn test_require_and_open_directives() {
        let src = "require open mylib.prelude;\nsymbol foo : T;";
        let module = LambdapiExchange::import(src).unwrap();
        assert_eq!(module.requires, vec!["mylib.prelude".to_string()]);
        assert_eq!(module.opens, vec!["mylib.prelude".to_string()]);
        let out = LambdapiExchange::export(&module).unwrap();
        assert!(out.contains("require open mylib.prelude;"));
    }

    #[test]
    fn test_translate_to_dedukti_roundtrip_smoke() {
        let lp = "constant symbol Nat : TYPE;\nsymbol id : Nat → Nat ≔ λ x, x;\n";
        let dk = LambdapiExchange::translate_to_dedukti(lp).unwrap();
        assert!(dk.contains("def id"));
        assert!(dk.contains(":="));
    }

    #[test]
    fn test_empty_input_errors() {
        let result = LambdapiExchange::import("");
        assert_eq!(result, Err(ExchangeError::EmptyProblem));
    }
}
