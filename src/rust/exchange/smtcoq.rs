// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! SMTCoq bridge — STUB BRIDGE (parse-and-skeleton only).
//!
//! SMTCoq (Armand-Faure-Spitters-Werner, 2011) embeds Z3 / veriT / CVC4
//! unsat proofs into Coq so the kernel re-checks them. This module
//! supplies enough of the Alethe (formerly LFSC) / LFSC / DRAT parser
//! surface to drive downstream consumers, plus an *honest skeleton*
//! emitter — the actual SMTCoq Coq plugin invocation is NOT in-scope
//! and is gated behind the upstream SMTCoq binary.
//!
//! Heavy operations are explicitly labelled `(* TODO: SMTCoq integration
//! not yet wired *)` in the emitted skeleton so downstream callers can
//! detect that a real reconstruction has not happened.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

/// Error type for SMTCoq exchange.
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
            ExchangeError::EmptyProblem => write!(f, "empty proof"),
        }
    }
}

impl std::error::Error for ExchangeError {}

/// One step of an Alethe proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AletheStep {
    /// Step identifier, e.g. "t1.h1".
    pub id: String,
    /// Inference rule, e.g. "th_resolution".
    pub rule: String,
    /// Raw clause text.
    pub clause: String,
    /// Premise step IDs.
    pub premises: Vec<String>,
    /// Rule arguments.
    pub args: Vec<String>,
}

/// An Alethe proof: a sequence of steps plus the input assumptions.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AletheProof {
    pub steps: Vec<AletheStep>,
    pub assumptions: Vec<String>,
}

/// LFSC proof — opaque byte container. CVC4's old LFSC format is dense
/// and side-condition-driven; we don't parse it further here.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LfscProof {
    pub raw: String,
}

/// SAT-level DRAT unsat certificate, as emitted by Z3 portfolios.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DratProof {
    pub clauses_added: usize,
    pub clauses_deleted: usize,
    pub raw: String,
}

/// SMTCoq exchange driver.
#[derive(Debug, Clone, Default)]
pub struct SmtCoqExchange;

impl SmtCoqExchange {
    pub fn new() -> Self {
        Self
    }

    /// Parse an Alethe proof. Alethe steps look like
    /// `(step t1 (cl ...) :rule th_resolution :premises (h1 h2))`.
    /// Assumptions appear as `(assume hN <formula>)`.
    pub fn parse_alethe_proof(content: &str) -> Result<AletheProof, ExchangeError> {
        let mut proof = AletheProof::default();
        for raw_line in content.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with(';') {
                continue;
            }
            // Strip the outer parentheses, if balanced. This is a deliberately
            // lenient line-based parser — real Alethe proofs may have steps
            // that span multiple lines, but the regression corpus uses one
            // step per line. Multi-line steps fall through to ParseError.
            if let Some(rest) = line.strip_prefix("(assume ") {
                let body = strip_one_trailing_paren(rest).trim().to_string();
                let (id, formula) = split_first_token(&body);
                proof.assumptions.push(format!("{}: {}", id, formula));
            } else if let Some(rest) = line.strip_prefix("(step ") {
                let body = strip_one_trailing_paren(rest).trim().to_string();
                let step = parse_alethe_step(&body)?;
                proof.steps.push(step);
            } else if line.starts_with("(anchor")
                || line.starts_with("(define-fun")
                || line.starts_with("(declare-fun")
            {
                // Subproof anchors and helpers are not modelled; we tolerate
                // them so corpus inputs don't error.
                continue;
            } else {
                return Err(ExchangeError::ParseError(format!(
                    "unrecognised Alethe directive: {}",
                    line
                )));
            }
        }
        Ok(proof)
    }

    /// Parse an LFSC proof. CVC4-era LFSC is opaque to us; we just hold
    /// the bytes so downstream tooling (or a future reconstruction pass)
    /// can re-stream them to the SMTCoq plugin.
    pub fn parse_lfsc_proof(content: &str) -> Result<LfscProof, ExchangeError> {
        let trimmed = content.trim();
        if trimmed.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        if !trimmed.contains('(') {
            return Err(ExchangeError::ParseError(
                "LFSC proof must contain at least one s-expression".into(),
            ));
        }
        Ok(LfscProof {
            raw: trimmed.to_string(),
        })
    }

    /// Parse a DRAT unsat certificate. Each non-empty line is a clause;
    /// lines beginning with `d` are deletions, otherwise additions.
    /// Lines end with `0`.
    pub fn parse_drat_unsat(content: &str) -> Result<DratProof, ExchangeError> {
        let mut added = 0usize;
        let mut deleted = 0usize;
        for raw_line in content.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('c') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("d ") {
                if !rest.contains('0') {
                    return Err(ExchangeError::ParseError(format!(
                        "DRAT delete clause missing terminator: {}",
                        line
                    )));
                }
                deleted += 1;
            } else {
                if !line.contains('0') {
                    return Err(ExchangeError::ParseError(format!(
                        "DRAT add clause missing terminator: {}",
                        line
                    )));
                }
                added += 1;
            }
        }
        if added == 0 && deleted == 0 {
            return Err(ExchangeError::EmptyProblem);
        }
        Ok(DratProof {
            clauses_added: added,
            clauses_deleted: deleted,
            raw: content.to_string(),
        })
    }

    /// Emit a Coq skeleton script. This is an *honest stub*: the body is
    /// `admit. Qed.` with the proof bytes embedded as comments. Downstream
    /// callers should grep for the marker comment to detect that the proof
    /// has not actually been re-checked by the Coq kernel.
    pub fn emit_coq_skeleton(proof: &AletheProof) -> Result<String, ExchangeError> {
        if proof.steps.is_empty() && proof.assumptions.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        let mut out = String::new();
        out.push_str("(* Auto-generated by SmtCoqExchange — STUB SKELETON *)\n");
        out.push_str("Require Import SMTCoq.SMTCoq.\n\n");
        for a in &proof.assumptions {
            out.push_str(&format!("(* assume: {} *)\n", a));
        }
        for s in &proof.steps {
            out.push_str(&format!(
                "(* step {} via {} : {} *)\n",
                s.id, s.rule, s.clause
            ));
        }
        out.push_str("\nLemma smtcoq_replayed : True.\n");
        out.push_str("Proof.\n");
        out.push_str("  (* TODO: SMTCoq integration not yet wired *)\n");
        out.push_str("  (* The verit2coq tactic call would go here. *)\n");
        out.push_str("  admit.\n");
        out.push_str("Qed.\n");
        Ok(out)
    }

    /// Structural sanity check: every premise reference resolves to a
    /// preceding step ID or an assumption ID.
    pub fn validate_proof_well_formed(proof: &AletheProof) -> Result<(), ExchangeError> {
        let mut known: Vec<String> = proof
            .assumptions
            .iter()
            .map(|a| a.split(':').next().unwrap_or("").trim().to_string())
            .collect();
        for s in &proof.steps {
            for p in &s.premises {
                if !known.iter().any(|k| k == p) {
                    return Err(ExchangeError::TranslationError(format!(
                        "step {} references unknown premise: {}",
                        s.id, p
                    )));
                }
            }
            known.push(s.id.clone());
        }
        Ok(())
    }
}

fn parse_alethe_step(body: &str) -> Result<AletheStep, ExchangeError> {
    // body looks like: "t1 (cl ...) :rule R :premises (a b) :args (x)"
    let (id, after_id) = split_first_token(body);
    if id.is_empty() {
        return Err(ExchangeError::ParseError("missing step id".into()));
    }
    let (clause, after_clause) = take_parenthesised(after_id.trim());

    let mut rule = String::new();
    let mut premises: Vec<String> = Vec::new();
    let mut args: Vec<String> = Vec::new();

    let mut rest: String = after_clause.trim().to_string();
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix(":rule ") {
            let (val, after) = split_first_token(r);
            rule = val;
            rest = after.trim().to_string();
        } else if let Some(r) = rest.strip_prefix(":premises ") {
            let (block, after) = take_parenthesised(r);
            premises = block.split_whitespace().map(str::to_string).collect();
            rest = after.trim().to_string();
        } else if let Some(r) = rest.strip_prefix(":args ") {
            let (block, after) = take_parenthesised(r);
            args = block.split_whitespace().map(str::to_string).collect();
            rest = after.trim().to_string();
        } else {
            // Unknown annotation — skip a token and continue.
            let (_, after) = split_first_token(&rest);
            if after.is_empty() {
                break;
            }
            rest = after;
        }
    }

    Ok(AletheStep {
        id,
        rule,
        clause,
        premises,
        args,
    })
}

/// Strip exactly one trailing `)` from `s`, if present.
fn strip_one_trailing_paren(s: &str) -> &str {
    let trimmed = s.trim_end();
    if let Some(stripped) = trimmed.strip_suffix(')') {
        stripped
    } else {
        trimmed
    }
}

fn split_first_token(s: &str) -> (String, String) {
    let s = s.trim();
    match s.find(char::is_whitespace) {
        Some(i) => (s[..i].to_string(), s[i..].trim().to_string()),
        None => (s.to_string(), String::new()),
    }
}

fn take_parenthesised(s: &str) -> (String, String) {
    let s = s.trim_start();
    if !s.starts_with('(') {
        // Fallback: take next single token.
        return split_first_token(s);
    }
    let mut depth = 0i32;
    let mut end = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = i;
                    break;
                }
            },
            _ => {},
        }
    }
    let block = s[1..end].to_string();
    let rest = if end + 1 < s.len() {
        s[end + 1..].trim().to_string()
    } else {
        String::new()
    };
    (block, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_two_step_alethe_proof() {
        let src = concat!(
            "(assume h1 (or p q))\n",
            "(assume h2 (not q))\n",
            "(step t1 (cl p) :rule th_resolution :premises (h1 h2))\n",
            "(step t2 (cl) :rule resolution :premises (t1) :args (p))\n"
        );
        let proof = SmtCoqExchange::parse_alethe_proof(src).unwrap();
        assert_eq!(proof.assumptions.len(), 2);
        assert_eq!(proof.steps.len(), 2);
        assert_eq!(proof.steps[0].rule, "th_resolution");
        assert_eq!(proof.steps[0].premises, vec!["h1", "h2"]);
        assert_eq!(proof.steps[1].args, vec!["p"]);
    }

    #[test]
    fn test_emit_coq_skeleton_is_stub() {
        let proof = AletheProof {
            steps: vec![AletheStep {
                id: "t1".into(),
                rule: "resolution".into(),
                clause: "(cl)".into(),
                premises: vec!["h1".into()],
                args: vec![],
            }],
            assumptions: vec!["h1: p".into()],
        };
        let coq = SmtCoqExchange::emit_coq_skeleton(&proof).unwrap();
        assert!(coq.contains("Lemma smtcoq_replayed"));
        assert!(coq.contains("admit."));
        assert!(coq.contains("Qed."));
        assert!(coq.contains("TODO: SMTCoq integration not yet wired"));
    }

    #[test]
    fn test_parse_drat_counts_add_and_delete() {
        let src = "1 2 0\n-1 3 0\nd 1 2 0\nc this is a comment\n";
        let drat = SmtCoqExchange::parse_drat_unsat(src).unwrap();
        assert_eq!(drat.clauses_added, 2);
        assert_eq!(drat.clauses_deleted, 1);
    }

    #[test]
    fn test_validate_well_formed_proof() {
        let src = concat!(
            "(assume h1 p)\n",
            "(step t1 (cl p) :rule axiom :premises (h1))\n"
        );
        let proof = SmtCoqExchange::parse_alethe_proof(src).unwrap();
        SmtCoqExchange::validate_proof_well_formed(&proof).unwrap();
    }

    #[test]
    fn test_validate_rejects_dangling_premise() {
        let proof = AletheProof {
            steps: vec![AletheStep {
                id: "t1".into(),
                rule: "resolution".into(),
                clause: "(cl)".into(),
                premises: vec!["does_not_exist".into()],
                args: vec![],
            }],
            assumptions: vec![],
        };
        assert!(SmtCoqExchange::validate_proof_well_formed(&proof).is_err());
    }

    #[test]
    fn test_parse_lfsc_holds_bytes() {
        let src = "(check (% A (! _ A)))";
        let lfsc = SmtCoqExchange::parse_lfsc_proof(src).unwrap();
        assert!(lfsc.raw.contains("check"));
    }
}
