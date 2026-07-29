// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! TPTP (Thousands of Problems for Theorem Provers) exchange format
//!
//! The universal exchange format for first-order ATP backends
//! (Vampire, E, SPASS, Princess, iProver, Twee, …).
//!
//! Supports importing and exporting CNF and FOF problems, plus
//! best-effort translation to/from SMT-LIB v2 for cross-prover
//! interoperability. TFF/THF dialects are recognised at parse time
//! but rejected for translation to keep this module conservative.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

/// Common error type for proof exchange modules.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExchangeError {
    /// The TPTP dialect (TFF / THF) is not supported for this operation.
    UnsupportedDialect(String),
    /// Parser failed at the given message.
    ParseError(String),
    /// A semantic translation step could not be performed.
    TranslationError(String),
    /// The problem contains neither axioms nor a conjecture.
    EmptyProblem,
}

impl std::fmt::Display for ExchangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExchangeError::UnsupportedDialect(d) => write!(f, "unsupported TPTP dialect: {}", d),
            ExchangeError::ParseError(m) => write!(f, "parse error: {}", m),
            ExchangeError::TranslationError(m) => write!(f, "translation error: {}", m),
            ExchangeError::EmptyProblem => write!(f, "empty problem (no axioms, no conjecture)"),
        }
    }
}

impl std::error::Error for ExchangeError {}

/// Recognised TPTP dialects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TptpDialect {
    Cnf,
    Fof,
    Tff,
    Thf,
    Tcf,
}

impl TptpDialect {
    fn from_keyword(kw: &str) -> Option<Self> {
        match kw {
            "cnf" => Some(TptpDialect::Cnf),
            "fof" => Some(TptpDialect::Fof),
            "tff" => Some(TptpDialect::Tff),
            "thf" => Some(TptpDialect::Thf),
            "tcf" => Some(TptpDialect::Tcf),
            _ => None,
        }
    }

    fn keyword(&self) -> &'static str {
        match self {
            TptpDialect::Cnf => "cnf",
            TptpDialect::Fof => "fof",
            TptpDialect::Tff => "tff",
            TptpDialect::Thf => "thf",
            TptpDialect::Tcf => "tcf",
        }
    }
}

/// Role of a TPTP-annotated formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TptpRole {
    Axiom,
    Hypothesis,
    Definition,
    Conjecture,
    NegatedConjecture,
    Theorem,
    Lemma,
    Type,
    Unknown,
}

impl TptpRole {
    fn from_str(s: &str) -> Self {
        match s.trim() {
            "axiom" => TptpRole::Axiom,
            "hypothesis" => TptpRole::Hypothesis,
            "definition" => TptpRole::Definition,
            "conjecture" => TptpRole::Conjecture,
            "negated_conjecture" => TptpRole::NegatedConjecture,
            "theorem" => TptpRole::Theorem,
            "lemma" => TptpRole::Lemma,
            "type" => TptpRole::Type,
            _ => TptpRole::Unknown,
        }
    }

    fn as_str(&self) -> &'static str {
        match self {
            TptpRole::Axiom => "axiom",
            TptpRole::Hypothesis => "hypothesis",
            TptpRole::Definition => "definition",
            TptpRole::Conjecture => "conjecture",
            TptpRole::NegatedConjecture => "negated_conjecture",
            TptpRole::Theorem => "theorem",
            TptpRole::Lemma => "lemma",
            TptpRole::Type => "type",
            TptpRole::Unknown => "unknown",
        }
    }
}

/// A single TPTP-annotated formula. The `formula` field stores raw text;
/// callers should not assume any further structural parsing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TptpFormula {
    pub name: String,
    pub role: TptpRole,
    pub formula: String,
    pub source: Option<String>,
}

/// A complete TPTP problem.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TptpProblem {
    pub name: Option<String>,
    pub axioms: Vec<TptpFormula>,
    pub conjecture: Option<TptpFormula>,
    pub includes: Vec<String>,
    pub dialect: TptpDialect,
}

/// TPTP exchange driver.
#[derive(Debug, Clone, Default)]
pub struct TptpExchange {
    /// Whether to emit comments on export.
    pub emit_comments: bool,
}

impl TptpExchange {
    pub fn new() -> Self {
        Self {
            emit_comments: true,
        }
    }

    /// Import a TPTP source file into a structured problem.
    pub fn import_problem(content: &str) -> Result<TptpProblem, ExchangeError> {
        let mut axioms: Vec<TptpFormula> = Vec::new();
        let mut conjecture: Option<TptpFormula> = None;
        let mut includes: Vec<String> = Vec::new();
        let mut dialect: Option<TptpDialect> = None;

        // Collapse line continuations and strip line-level comments. TPTP
        // statements end in a period and may span multiple lines.
        let mut cleaned = String::new();
        for raw_line in content.lines() {
            let line = match raw_line.find('%') {
                Some(i) => &raw_line[..i],
                None => raw_line,
            };
            cleaned.push_str(line.trim());
            cleaned.push(' ');
        }

        // Tokenise on statement terminators. We treat `).` at the end of
        // a top-level annotated formula as the terminator and split there.
        for raw_stmt in split_top_level(&cleaned) {
            let stmt = raw_stmt.trim();
            if stmt.is_empty() {
                continue;
            }

            if let Some(rest) = stmt.strip_prefix("include(") {
                let inner = strip_one_trailing_paren(rest)
                    .trim_matches('\'')
                    .trim_matches('"');
                includes.push(inner.to_string());
                continue;
            }

            // Match an annotated formula keyword: cnf|fof|tff|thf|tcf.
            let (kw, body) = match stmt.find('(') {
                Some(i) => (&stmt[..i], &stmt[i + 1..]),
                None => continue,
            };
            let kw = kw.trim();
            let dial = TptpDialect::from_keyword(kw)
                .ok_or_else(|| ExchangeError::ParseError(format!("unknown keyword: {}", kw)))?;
            dialect = Some(match dialect {
                None => dial,
                Some(d) => d, // first dialect wins; mixed inputs allowed
            });

            // body looks like: name, role, formula [, source]. Strip exactly
            // one trailing ')' to balance the keyword's opening '(' without
            // eating any inner parens that close at end of formula.
            let body = strip_one_trailing_paren(body).trim();
            let parts = split_annotated(body);
            if parts.len() < 3 {
                return Err(ExchangeError::ParseError(format!(
                    "malformed annotated formula: {}",
                    stmt
                )));
            }
            let name = parts[0].trim().to_string();
            let role = TptpRole::from_str(parts[1].trim());
            let formula = parts[2].trim().to_string();
            let source = parts.get(3).map(|s| s.trim().to_string());

            let f = TptpFormula {
                name,
                role,
                formula,
                source,
            };

            match role {
                TptpRole::Conjecture => {
                    conjecture = Some(f);
                },
                _ => axioms.push(f),
            }
        }

        let dialect = dialect.unwrap_or(TptpDialect::Fof);

        Ok(TptpProblem {
            name: None,
            axioms,
            conjecture,
            includes,
            dialect,
        })
    }

    /// Emit a TPTP problem back to text.
    pub fn export_problem(problem: &TptpProblem) -> Result<String, ExchangeError> {
        if problem.axioms.is_empty() && problem.conjecture.is_none() && problem.includes.is_empty()
        {
            return Err(ExchangeError::EmptyProblem);
        }
        let mut out = String::new();
        if let Some(name) = &problem.name {
            out.push_str(&format!("%% problem: {}\n", name));
        }
        for inc in &problem.includes {
            out.push_str(&format!("include('{}').\n", inc));
        }
        let kw = problem.dialect.keyword();
        for f in &problem.axioms {
            out.push_str(&format!(
                "{}({}, {}, {}).\n",
                kw,
                f.name,
                f.role.as_str(),
                f.formula
            ));
        }
        if let Some(c) = &problem.conjecture {
            out.push_str(&format!(
                "{}({}, {}, {}).\n",
                kw,
                c.name,
                c.role.as_str(),
                c.formula
            ));
        }
        Ok(out)
    }

    /// Convert a CNF or FOF TPTP problem to SMT-LIB v2 text.
    pub fn translate_to_smtlib(problem: &TptpProblem) -> Result<String, ExchangeError> {
        match problem.dialect {
            TptpDialect::Cnf | TptpDialect::Fof => {},
            d => {
                return Err(ExchangeError::UnsupportedDialect(format!("{:?}", d)));
            },
        }
        if problem.axioms.is_empty() && problem.conjecture.is_none() {
            return Err(ExchangeError::EmptyProblem);
        }
        let mut out = String::new();
        out.push_str("(set-logic UF)\n");
        // Collect predicate / function symbols by a cheap lexical scan.
        let mut symbols: Vec<String> = Vec::new();
        for f in problem.axioms.iter().chain(problem.conjecture.iter()) {
            collect_symbols(&f.formula, &mut symbols);
        }
        symbols.sort();
        symbols.dedup();
        for sym in &symbols {
            out.push_str(&format!("(declare-fun {} () Bool)\n", sym));
        }
        for f in &problem.axioms {
            out.push_str(&format!(
                "(assert {}) ; from {}\n",
                tptp_to_smt(&f.formula),
                f.name
            ));
        }
        if let Some(c) = &problem.conjecture {
            // Conjecture is asserted negated for refutational provers.
            out.push_str(&format!(
                "(assert (not {})) ; conjecture {}\n",
                tptp_to_smt(&c.formula),
                c.name
            ));
        }
        out.push_str("(check-sat)\n");
        Ok(out)
    }

    /// Best-effort reverse translation from SMT-LIB v2 to a TPTP FOF problem.
    pub fn translate_from_smtlib(smt: &str) -> Result<TptpProblem, ExchangeError> {
        let mut axioms = Vec::new();
        let mut conjecture = None;
        let mut counter = 0usize;
        for line in smt.lines() {
            let l = line.trim();
            if let Some(rest) = l.strip_prefix("(assert ") {
                let body = rest.trim_end_matches(')').trim();
                let is_neg_conjecture = body.starts_with("(not ");
                let formula = smt_to_tptp(body);
                let f = TptpFormula {
                    name: format!("smt_{}", counter),
                    role: if is_neg_conjecture {
                        TptpRole::Conjecture
                    } else {
                        TptpRole::Axiom
                    },
                    formula,
                    source: None,
                };
                if is_neg_conjecture && conjecture.is_none() {
                    conjecture = Some(f);
                } else {
                    axioms.push(f);
                }
                counter += 1;
            }
        }
        if axioms.is_empty() && conjecture.is_none() {
            return Err(ExchangeError::EmptyProblem);
        }
        Ok(TptpProblem {
            name: None,
            axioms,
            conjecture,
            includes: vec![],
            dialect: TptpDialect::Fof,
        })
    }
}

/// Strip exactly one trailing `)`, if present.
fn strip_one_trailing_paren(s: &str) -> &str {
    let t = s.trim_end();
    t.strip_suffix(')').unwrap_or(t)
}

/// Split a flat string of TPTP statements terminated by `).`.
fn split_top_level(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut buf = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        buf.push(c);
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '.' if depth == 0 => {
                let trimmed = buf.trim_end_matches('.').trim().to_string();
                if !trimmed.is_empty() {
                    out.push(trimmed);
                }
                buf.clear();
            },
            _ => {},
        }
        i += 1;
    }
    let tail = buf.trim().to_string();
    if !tail.is_empty() {
        out.push(tail);
    }
    out
}

/// Split a TPTP annotated formula body on commas at depth 0.
fn split_annotated(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut buf = String::new();
    for c in body.chars() {
        match c {
            '(' | '[' => {
                depth += 1;
                buf.push(c);
            },
            ')' | ']' => {
                depth -= 1;
                buf.push(c);
            },
            ',' if depth == 0 => {
                out.push(buf.clone());
                buf.clear();
            },
            _ => buf.push(c),
        }
    }
    if !buf.trim().is_empty() {
        out.push(buf);
    }
    out
}

/// Cheap lexical scan for predicate-like identifiers.
fn collect_symbols(formula: &str, into: &mut Vec<String>) {
    let mut current = String::new();
    for c in formula.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            current.push(c);
        } else {
            if !current.is_empty() {
                let token = current.clone();
                if token.chars().next().is_some_and(|c| c.is_ascii_lowercase())
                    && !matches!(
                        token.as_str(),
                        "true" | "false" | "and" | "or" | "not" | "implies"
                    )
                {
                    into.push(token);
                }
                current.clear();
            }
        }
    }
    if !current.is_empty()
        && current
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_lowercase())
    {
        into.push(current);
    }
}

/// Map TPTP connective tokens to SMT-LIB. Conservative — only handles the
/// most common syntactic patterns and otherwise passes through.
fn tptp_to_smt(f: &str) -> String {
    f.replace("&", " and ")
        .replace("|", " or ")
        .replace("=>", " implies ")
        .replace("~", " not ")
}

fn smt_to_tptp(f: &str) -> String {
    f.replace("(and ", "(")
        .replace("(or ", "(")
        .replace("(not ", "~(")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fof_roundtrip() {
        let src = "fof(ax1, axiom, (p | q)).\nfof(g, conjecture, p).\n";
        let problem = TptpExchange::import_problem(src).unwrap();
        assert_eq!(problem.axioms.len(), 1);
        assert!(problem.conjecture.is_some());
        let emitted = TptpExchange::export_problem(&problem).unwrap();
        let reparsed = TptpExchange::import_problem(&emitted).unwrap();
        assert_eq!(reparsed.axioms.len(), 1);
        assert!(reparsed.conjecture.is_some());
        assert_eq!(reparsed.dialect, TptpDialect::Fof);
    }

    #[test]
    fn test_axiom_only_problem_has_no_conjecture() {
        let src = "fof(ax1, axiom, p).\nfof(ax2, axiom, q).\n";
        let problem = TptpExchange::import_problem(src).unwrap();
        assert_eq!(problem.axioms.len(), 2);
        assert!(problem.conjecture.is_none());
    }

    #[test]
    fn test_cnf_to_smtlib() {
        let src = "cnf(c1, axiom, p | ~q).\ncnf(g, conjecture, p).\n";
        let problem = TptpExchange::import_problem(src).unwrap();
        let smt = TptpExchange::translate_to_smtlib(&problem).unwrap();
        assert!(smt.contains("(set-logic UF)"));
        assert!(smt.contains("(check-sat)"));
        assert!(smt.contains("(declare-fun p () Bool)"));
    }

    #[test]
    fn test_export_empty_problem_errors() {
        let p = TptpProblem {
            name: None,
            axioms: vec![],
            conjecture: None,
            includes: vec![],
            dialect: TptpDialect::Fof,
        };
        assert_eq!(
            TptpExchange::export_problem(&p),
            Err(ExchangeError::EmptyProblem)
        );
    }

    #[test]
    fn test_thf_rejected_for_smtlib() {
        let p = TptpProblem {
            name: None,
            axioms: vec![TptpFormula {
                name: "a".into(),
                role: TptpRole::Axiom,
                formula: "p".into(),
                source: None,
            }],
            conjecture: None,
            includes: vec![],
            dialect: TptpDialect::Thf,
        };
        match TptpExchange::translate_to_smtlib(&p) {
            Err(ExchangeError::UnsupportedDialect(_)) => {},
            other => panic!("expected UnsupportedDialect, got {:?}", other),
        }
    }

    #[test]
    fn test_translate_from_smtlib_recovers_conjecture() {
        let smt = "(set-logic UF)\n(assert p)\n(assert (not q))\n(check-sat)\n";
        let problem = TptpExchange::translate_from_smtlib(smt).unwrap();
        assert_eq!(problem.axioms.len(), 1);
        assert!(problem.conjecture.is_some());
    }
}
