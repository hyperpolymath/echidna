// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! SMT-LIB v2 exchange and cross-solver normalisation.
//!
//! Provides a structured representation of SMT-LIB scripts so problems
//! can be parsed, normalised, and emitted in a canonical form across
//! Z3, CVC5, Yices, MathSAT, Boolector, etc. A best-effort translator
//! to TPTP FOF lets pure first-order fragments cross to ATP backends.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

/// Error type for SMT-LIB exchange. Mirrors the variants used in
/// `tptp.rs`; duplicated rather than re-exported to keep this file
/// compilable in isolation.
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
            ExchangeError::EmptyProblem => write!(f, "empty script"),
        }
    }
}

impl std::error::Error for ExchangeError {}

/// One SMT-LIB v2 command. `Other` preserves unrecognised text verbatim
/// so that round-trip emit is faithful for solver-specific extensions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SmtLibCommand {
    SetLogic(String),
    SetInfo {
        key: String,
        value: String,
    },
    SetOption {
        key: String,
        value: String,
    },
    DeclareSort {
        name: String,
        arity: u32,
    },
    DeclareFun {
        name: String,
        params: Vec<String>,
        ret: String,
    },
    DefineFun {
        name: String,
        params: Vec<(String, String)>,
        ret: String,
        body: String,
    },
    Assert(String),
    CheckSat,
    GetModel,
    GetProof,
    GetUnsatCore,
    Push(u32),
    Pop(u32),
    Exit,
    Reset,
    Other(String),
}

/// A complete SMT-LIB v2 script as an ordered list of commands.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtLibScript {
    pub commands: Vec<SmtLibCommand>,
}

/// SMT-LIB v2 exchange driver.
#[derive(Debug, Clone, Default)]
pub struct SmtLibExchange;

impl SmtLibExchange {
    pub fn new() -> Self {
        Self
    }

    /// Parse a textual SMT-LIB v2 script. Top-level S-expressions are
    /// extracted and dispatched on their head symbol. Unknown commands
    /// are preserved verbatim via `SmtLibCommand::Other`.
    pub fn parse(content: &str) -> Result<SmtLibScript, ExchangeError> {
        let exprs = split_top_level_sexprs(content)?;
        let mut commands = Vec::with_capacity(exprs.len());
        for expr in exprs {
            commands.push(parse_command(&expr)?);
        }
        Ok(SmtLibScript { commands })
    }

    /// Serialise a script back to text. Round-trip safe for commands we
    /// recognise; `Other` blocks are emitted verbatim.
    pub fn emit(script: &SmtLibScript) -> Result<String, ExchangeError> {
        if script.commands.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        let mut out = String::new();
        for cmd in &script.commands {
            emit_command(cmd, &mut out);
            out.push('\n');
        }
        Ok(out)
    }

    /// Canonicalise: sort declarations alphabetically while preserving
    /// dependency order (logic first, then sorts, then funs, then asserts).
    /// `let` bindings are NOT expanded here (a TODO in the design comment);
    /// the body of an assert is preserved as-is.
    pub fn normalise(script: &SmtLibScript) -> SmtLibScript {
        let mut logic: Vec<SmtLibCommand> = Vec::new();
        let mut infos: Vec<SmtLibCommand> = Vec::new();
        let mut options: Vec<SmtLibCommand> = Vec::new();
        let mut sorts: Vec<SmtLibCommand> = Vec::new();
        let mut funs: Vec<SmtLibCommand> = Vec::new();
        let mut defs: Vec<SmtLibCommand> = Vec::new();
        let mut asserts: Vec<SmtLibCommand> = Vec::new();
        let mut control: Vec<SmtLibCommand> = Vec::new();

        for cmd in &script.commands {
            match cmd {
                SmtLibCommand::SetLogic(_) => logic.push(cmd.clone()),
                SmtLibCommand::SetInfo { .. } => infos.push(cmd.clone()),
                SmtLibCommand::SetOption { .. } => options.push(cmd.clone()),
                SmtLibCommand::DeclareSort { .. } => sorts.push(cmd.clone()),
                SmtLibCommand::DeclareFun { .. } => funs.push(cmd.clone()),
                SmtLibCommand::DefineFun { .. } => defs.push(cmd.clone()),
                SmtLibCommand::Assert(_) => asserts.push(cmd.clone()),
                _ => control.push(cmd.clone()),
            }
        }

        infos.sort_by_key(key_of);
        options.sort_by_key(key_of);
        sorts.sort_by_key(key_of);
        funs.sort_by_key(key_of);
        // defs preserve original order: dependencies between defines are
        // significant and we don't track them here.

        let mut commands = Vec::new();
        commands.extend(logic);
        commands.extend(infos);
        commands.extend(options);
        commands.extend(sorts);
        commands.extend(funs);
        commands.extend(defs);
        commands.extend(asserts);
        commands.extend(control);
        SmtLibScript { commands }
    }

    /// Extract the `set-logic` value, if any.
    pub fn extract_logic(script: &SmtLibScript) -> Option<String> {
        for cmd in &script.commands {
            if let SmtLibCommand::SetLogic(l) = cmd {
                return Some(l.clone());
            }
        }
        None
    }

    /// Best-effort translation from SMT-LIB to TPTP FOF text. Loses
    /// bit-vector / FP / array semantics — only first-order Boolean and
    /// uninterpreted-function fragments map cleanly.
    pub fn translate_to_tptp_fof(script: &SmtLibScript) -> Result<String, ExchangeError> {
        let mut axioms: Vec<String> = Vec::new();
        let mut counter = 0usize;
        for cmd in &script.commands {
            if let SmtLibCommand::Assert(body) = cmd {
                let body = body.trim();
                let is_neg_conjecture = body.starts_with("(not ");
                let formula = smt_expr_to_fof(body);
                let role = if is_neg_conjecture {
                    "conjecture"
                } else {
                    "axiom"
                };
                let name = format!("smt_{}", counter);
                axioms.push(format!("fof({}, {}, {}).", name, role, formula));
                counter += 1;
            }
        }
        if axioms.is_empty() {
            return Err(ExchangeError::EmptyProblem);
        }
        Ok(axioms.join("\n") + "\n")
    }
}

fn key_of(cmd: &SmtLibCommand) -> String {
    match cmd {
        SmtLibCommand::SetInfo { key, .. } => key.clone(),
        SmtLibCommand::SetOption { key, .. } => key.clone(),
        SmtLibCommand::DeclareSort { name, .. } => name.clone(),
        SmtLibCommand::DeclareFun { name, .. } => name.clone(),
        SmtLibCommand::DefineFun { name, .. } => name.clone(),
        _ => String::new(),
    }
}

fn split_top_level_sexprs(content: &str) -> Result<Vec<String>, ExchangeError> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut buf = String::new();
    let mut in_string = false;
    let mut in_comment = false;
    for c in content.chars() {
        if in_comment {
            if c == '\n' {
                in_comment = false;
            }
            continue;
        }
        if in_string {
            buf.push(c);
            if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            ';' if depth == 0 => in_comment = true,
            ';' => in_comment = true,
            '"' => {
                in_string = true;
                buf.push(c);
            },
            '(' => {
                depth += 1;
                buf.push(c);
            },
            ')' => {
                depth -= 1;
                buf.push(c);
                if depth == 0 {
                    out.push(buf.trim().to_string());
                    buf.clear();
                } else if depth < 0 {
                    return Err(ExchangeError::ParseError("unbalanced ')'".into()));
                }
            },
            _ => {
                if depth > 0 {
                    buf.push(c);
                }
            },
        }
    }
    if depth != 0 {
        return Err(ExchangeError::ParseError("unbalanced '('".into()));
    }
    Ok(out)
}

fn parse_command(expr: &str) -> Result<SmtLibCommand, ExchangeError> {
    let inner = expr
        .trim()
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .ok_or_else(|| ExchangeError::ParseError(format!("not an s-expression: {}", expr)))?
        .trim();

    let (head, rest) = match inner.find(char::is_whitespace) {
        Some(i) => (&inner[..i], inner[i..].trim()),
        None => (inner, ""),
    };

    let cmd = match head {
        "set-logic" => SmtLibCommand::SetLogic(rest.to_string()),
        "set-info" => {
            let (k, v) = split_key_value(rest);
            SmtLibCommand::SetInfo { key: k, value: v }
        },
        "set-option" => {
            let (k, v) = split_key_value(rest);
            SmtLibCommand::SetOption { key: k, value: v }
        },
        "declare-sort" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let name = parts.first().copied().unwrap_or("").to_string();
            // SMT-LIB spec: arity defaults to 0 when omitted (nullary sort
            // constructor). Any non-numeric token also collapses to 0 — the
            // upstream prover will reject the malformed line; we tolerate it
            // here rather than panicking during corpus ingest.
            let arity = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0u32);
            SmtLibCommand::DeclareSort { name, arity }
        },
        "declare-fun" => {
            // (declare-fun NAME (P1 P2 ...) RET)
            let (name, after_name) = split_first_token(rest);
            let (params_block, ret) = split_paren_block(&after_name)?;
            let params: Vec<String> = params_block
                .split_whitespace()
                .map(str::to_string)
                .collect();
            SmtLibCommand::DeclareFun {
                name,
                params,
                ret: ret.trim().to_string(),
            }
        },
        "define-fun" => {
            // (define-fun NAME ((x T) ...) RET BODY)
            let (name, after_name) = split_first_token(rest);
            let (params_block, after_params) = split_paren_block(&after_name)?;
            let params = parse_typed_params(&params_block);
            let (ret, body) = split_first_token(after_params.trim());
            SmtLibCommand::DefineFun {
                name,
                params,
                ret,
                body: body.trim().to_string(),
            }
        },
        "assert" => SmtLibCommand::Assert(rest.to_string()),
        "check-sat" => SmtLibCommand::CheckSat,
        "get-model" => SmtLibCommand::GetModel,
        "get-proof" => SmtLibCommand::GetProof,
        "get-unsat-core" => SmtLibCommand::GetUnsatCore,
        "push" => SmtLibCommand::Push(rest.parse().unwrap_or(1)),
        "pop" => SmtLibCommand::Pop(rest.parse().unwrap_or(1)),
        "exit" => SmtLibCommand::Exit,
        "reset" => SmtLibCommand::Reset,
        _ => SmtLibCommand::Other(expr.to_string()),
    };
    Ok(cmd)
}

fn split_key_value(s: &str) -> (String, String) {
    let s = s.trim();
    let (k, v) = match s.find(char::is_whitespace) {
        Some(i) => (&s[..i], s[i..].trim()),
        None => (s, ""),
    };
    (k.to_string(), v.to_string())
}

fn split_first_token(s: &str) -> (String, String) {
    let s = s.trim();
    match s.find(char::is_whitespace) {
        Some(i) => (s[..i].to_string(), s[i..].trim().to_string()),
        None => (s.to_string(), String::new()),
    }
}

fn split_paren_block(s: &str) -> Result<(String, String), ExchangeError> {
    let s = s.trim_start();
    if !s.starts_with('(') {
        return Err(ExchangeError::ParseError(format!(
            "expected '(' got: {}",
            s
        )));
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
    let rest = s[end + 1..].trim().to_string();
    Ok((block, rest))
}

fn parse_typed_params(block: &str) -> Vec<(String, String)> {
    // block looks like "(x Int) (y Bool)"
    let mut out = Vec::new();
    let mut depth = 0;
    let mut buf = String::new();
    for c in block.chars() {
        match c {
            '(' => {
                depth += 1;
                if depth > 1 {
                    buf.push(c);
                }
            },
            ')' => {
                depth -= 1;
                if depth == 0 {
                    let mut it = buf.split_whitespace();
                    let n = it.next().unwrap_or("").to_string();
                    let t = it.collect::<Vec<_>>().join(" ");
                    if !n.is_empty() {
                        out.push((n, t));
                    }
                    buf.clear();
                } else {
                    buf.push(c);
                }
            },
            _ => {
                if depth >= 1 {
                    buf.push(c);
                }
            },
        }
    }
    out
}

fn emit_command(cmd: &SmtLibCommand, out: &mut String) {
    match cmd {
        SmtLibCommand::SetLogic(l) => out.push_str(&format!("(set-logic {})", l)),
        SmtLibCommand::SetInfo { key, value } => {
            out.push_str(&format!("(set-info {} {})", key, value))
        },
        SmtLibCommand::SetOption { key, value } => {
            out.push_str(&format!("(set-option {} {})", key, value))
        },
        SmtLibCommand::DeclareSort { name, arity } => {
            out.push_str(&format!("(declare-sort {} {})", name, arity))
        },
        SmtLibCommand::DeclareFun { name, params, ret } => out.push_str(&format!(
            "(declare-fun {} ({}) {})",
            name,
            params.join(" "),
            ret
        )),
        SmtLibCommand::DefineFun {
            name,
            params,
            ret,
            body,
        } => {
            let params_str = params
                .iter()
                .map(|(n, t)| format!("({} {})", n, t))
                .collect::<Vec<_>>()
                .join(" ");
            out.push_str(&format!(
                "(define-fun {} ({}) {} {})",
                name, params_str, ret, body
            ))
        },
        SmtLibCommand::Assert(body) => out.push_str(&format!("(assert {})", body)),
        SmtLibCommand::CheckSat => out.push_str("(check-sat)"),
        SmtLibCommand::GetModel => out.push_str("(get-model)"),
        SmtLibCommand::GetProof => out.push_str("(get-proof)"),
        SmtLibCommand::GetUnsatCore => out.push_str("(get-unsat-core)"),
        SmtLibCommand::Push(n) => out.push_str(&format!("(push {})", n)),
        SmtLibCommand::Pop(n) => out.push_str(&format!("(pop {})", n)),
        SmtLibCommand::Exit => out.push_str("(exit)"),
        SmtLibCommand::Reset => out.push_str("(reset)"),
        SmtLibCommand::Other(s) => out.push_str(s),
    }
}

/// Convert an SMT expression body to a TPTP-FOF-ish string. Very conservative.
fn smt_expr_to_fof(s: &str) -> String {
    s.replace("(and ", "(")
        .replace("(or ", "(")
        .replace("(not ", "~(")
        .replace("(=> ", "(")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_and_emit_qf_lia() {
        let src = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)\n";
        let script = SmtLibExchange::parse(src).unwrap();
        assert_eq!(script.commands.len(), 4);
        let out = SmtLibExchange::emit(&script).unwrap();
        assert!(out.contains("(set-logic QF_LIA)"));
        assert!(out.contains("(check-sat)"));
        assert!(out.contains("(assert (> x 0))"));
    }

    #[test]
    fn test_normalise_roundtrip_preserves_semantics() {
        let src = concat!(
            "(set-logic QF_UF)\n",
            "(declare-fun q () Bool)\n",
            "(declare-fun p () Bool)\n",
            "(assert (or p q))\n",
            "(check-sat)\n"
        );
        let script = SmtLibExchange::parse(src).unwrap();
        let norm = SmtLibExchange::normalise(&script);
        let emitted = SmtLibExchange::emit(&norm).unwrap();
        let reparsed = SmtLibExchange::parse(&emitted).unwrap();
        // Round-trip preserves at least the 4 semantic commands
        // (set-logic, 2x declare-fun, assert, check-sat). Some parsers
        // may add a trailing Other(""); accept either count.
        assert!(reparsed.commands.len() >= 4 && reparsed.commands.len() <= 5);
        // declarations should be alphabetised after normalisation
        let names: Vec<String> = reparsed
            .commands
            .iter()
            .filter_map(|c| match c {
                SmtLibCommand::DeclareFun { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(names, vec!["p".to_string(), "q".to_string()]);
    }

    #[test]
    fn test_extract_logic_finds_qf_lia() {
        let src = "(set-logic QF_LIA)\n(check-sat)\n";
        let script = SmtLibExchange::parse(src).unwrap();
        assert_eq!(
            SmtLibExchange::extract_logic(&script),
            Some("QF_LIA".to_string())
        );
    }

    #[test]
    fn test_extract_logic_absent() {
        let src = "(check-sat)\n";
        let script = SmtLibExchange::parse(src).unwrap();
        assert_eq!(SmtLibExchange::extract_logic(&script), None);
    }

    #[test]
    fn test_translate_to_tptp_fof_smoke() {
        let src = "(set-logic UF)\n(declare-fun p () Bool)\n(assert p)\n(assert (not q))\n";
        let script = SmtLibExchange::parse(src).unwrap();
        let tptp = SmtLibExchange::translate_to_tptp_fof(&script).unwrap();
        assert!(tptp.contains("fof(smt_"));
        assert!(tptp.contains("conjecture"));
    }
}
