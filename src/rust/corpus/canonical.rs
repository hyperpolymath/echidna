// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Structural canonical form of a declaration's *type*, for cross-prover
//! identity keys (VeriSim E6 `GraphModality.cross_prover_identity_key`).
//!
//! The corpus stores one `statement` string per declaration, written in
//! whatever the source prover's surface syntax is. Matching those strings
//! by name (or by a synonym table) is what the estate did before: it needs
//! a dictionary entry per naming convention, and it silently fails for
//! anything the dictionary has never seen.
//!
//! This module takes the other route. It normalises the statement into a
//! *shape* — a nameless prefix term — and hashes that. Two declarations
//! that state the same theorem get the same shape even when their source
//! languages disagree about almost everything:
//!
//! ```text
//! Agda     +-comm : ∀ (x y : ℕ) → x + y ≡ y + x
//! Coq      Lemma add_comm : forall x y : nat, x + y = y + x.
//! Lean 4   theorem Nat.add_comm (x y : Nat) : x + y = y + x := by omega
//! Idris2   addComm : (x, y : Nat) -> x + y = y + x
//! SMT-LIB  (assert (forall ((x Nat) (y Nat)) (= (+ x y) (+ y x))))
//! Dedukti  def add_comm : Π (x y : Nat), eq Nat (add x y) (add y x).
//!          ⟹ (PI [NAT NAT] (EQ (ADD v0 v1) (ADD v1 v0)))
//! ```
//!
//! Isabelle elides the binders (`lemma add_comm: "(x::nat) + y = y + x"`),
//! and Why3 states the same arithmetic over `int` rather than `nat`. Those
//! two therefore miss the primary key but match the *skeleton* key, which
//! is the same shape with the binder prefix and sort atoms erased:
//!
//! ```text
//!          ⟹ (EQ (ADD v0 v1) (ADD v1 v0))
//! ```
//!
//! So a lookup tries the primary key first (exact, sort-aware) and falls
//! back to the skeleton key (binder- and sort-free) — a two-tier join, not
//! a fuzzy one. Nothing here consults a dictionary: the normalisation is
//! purely syntactic.
//!
//! ## What is normalised
//!
//! 1. **Declaration header** — `theorem`/`lemma`/`def`/`opaque`/`assert`/…
//!    plus the declared *name*, and any proof body after `:=`/`by`/`where`.
//! 2. **Module qualifiers** — `Nat.add_comm` and `bvadd` reduce to their
//!    last component before the operator table is consulted.
//! 3. **Operator spelling** — `+`, `plus`, `add`, `HAdd.hAdd`, `bvadd` are
//!    all `ADD`; `=`, `==`, `≡`, `eq` are `EQ`; `->`, `→` are `ARROW`.
//!    Canonical operators are emitted in **prefix** form, so infix input
//!    (`x + y`) and SMT-LIB prefix input (`(+ x y)`) agree.
//! 4. **Associativity** — arrows and `↔` are right-associative; arithmetic
//!    and comparison are left-associative.
//! 5. **Sorts** — `nat`/`ℕ` → `NAT`, `int`/`ℤ` → `INT`, `Prop`/`Set`/
//!    `Type` → `TYPE`, and so on. Unknown sorts keep their (unqualified,
//!    lower-cased) name.
//! 6. **Variables** — every variable, bound or free, is renamed `v0`, `v1`,
//!    … in order of first appearance. That is the alpha-normalisation: the
//!    *names* disappear, the *positions* do not, and a prover that writes
//!    `(x, y : Nat)` and one that writes `(a, b : Nat)` land on the same
//!    key. De Bruijn's point — that binding structure, not the spelling of
//!    variables, carries the meaning — is what is being exploited; the
//!    indices here are assigned by first use rather than by binder depth
//!    because real corpus statements routinely elide binders entirely, and
//!    depth indices would then not line up (see Isabelle above).
//! 7. **Type ascriptions** — Isabelle's `(x::nat)` is a term ascription,
//!    not a binder, and is unwrapped; Dedukti's explicit `eq Nat a b`
//!    type argument is dropped so it matches the infix form.
//! 8. **Agda operator names** — `_<_`, `_+_`, `_≡_` are read as the
//!    operator they wrap rather than as three punctuation tokens.
//!
//! ## What is *not* normalised
//!
//! Commutativity, associativity and other equational theories are **not**
//! applied: `x + y` and `y + x` are different shapes, deliberately. Nor is
//! the calculus changed: a statement that mentions `WellFounded` keeps
//! `WellFounded`. This is a syntactic identity key, not a decision
//! procedure, and the docs say so.
//!
//! The Rust here is a transcription of a Python prototype that was run
//! against the spellings above before it was ported; the unit tests at the
//! bottom of the file pin each of them.

#![allow(dead_code)]

use sha2::{Digest, Sha256};

/// Version tag for the normalisation scheme, stored next to every key so a
/// future change of rules cannot be mistaken for a change of theorem.
pub const SCHEME: &str = "dk-shape-v1";

/// How much of the statement a key is known to preserve.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum KeyTier {
    /// Bindings and sorts survived: the strongest key.
    Structural,
    /// Binders/sorts were erased to get a match.
    Skeleton,
    /// The statement did not parse into a term; keyed on normalised text.
    Text,
}

impl KeyTier {
    pub fn as_str(self) -> &'static str {
        match self {
            KeyTier::Structural => "structural",
            KeyTier::Skeleton => "skeleton",
            KeyTier::Text => "text",
        }
    }
}

/// A declaration's structural identity.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct StructuralKey {
    /// Version of the normalisation rules that produced this key.
    pub scheme: String,
    /// Canonical prefix shape, binders and sorts included.
    pub shape: String,
    /// Canonical prefix shape with binders and sorts erased.
    pub skeleton: String,
    /// SHA-256 of `shape`, hex.
    pub key: String,
    /// SHA-256 of `skeleton`, hex.
    pub skeleton_key: String,
    /// Which tier this declaration's shape is trustworthy at.
    pub tier: KeyTier,
    /// Whether the shape accounts for the whole statement. False when the
    /// parser stopped early (anything but a trailing `.`/`,`/`;` or an
    /// unmatched closing bracket left over), when the input ended inside an
    /// open bracket (a statement truncated mid-group), when the body holds notation
    /// this scheme has no rule for ([`is_unread_notation`]), when the header
    /// drop discarded tokens that were not a declared head, or when a leading
    /// bracket group was misread as a binder telescope. In each case the
    /// shape is still reported at the structural tier but stands for part of
    /// the statement, and different statements can share it. Always `false`
    /// at the text tier. Not part of `key`: it qualifies the key, so adding
    /// it changed no key.
    #[serde(default)]
    pub complete: bool,
}

// ===========================================================================
// Vocabulary
// ===========================================================================

/// Operator spellings → canonical operator. Lookup is on the *last*
/// component of a dotted name and is case-insensitive.
fn op_of(name: &str) -> Option<&'static str> {
    let raw = unqualify(name);
    let low = raw.to_lowercase();
    let op = match low.as_str() {
        // arithmetic
        "+" | "add" | "plus" | "hadd" | "bvadd" | "addn" => "ADD",
        "*" | "mul" | "times" | "hmul" | "bvmul" | "muln" => "MUL",
        "-" | "sub" | "minus" | "hsub" | "bvsub" => "SUB",
        "/" | "div" | "bvsdiv" => "DIV",
        "%" | "mod" | "bvsmod" => "MOD",
        // relations
        "=" | "==" | "≡" | "eq" | "beq" => "EQ",
        "≠" | "!=" | "<>" => "NEQ",
        "<" | "lt" | "bvslt" => "LT",
        "<=" | "≤" | "le" | "bvsle" => "LE",
        ">" | "gt" | "bvsgt" => "GT",
        ">=" | "≥" | "ge" | "bvsge" => "GE",
        // logic
        "∧" | "and" | "/\\" | "&&" | "conj" => "AND",
        "∨" | "or" | "\\/" | "||" | "disj" => "OR",
        "¬" | "not" => "NOT",
        "→" | "->" | "⟶" => "ARROW",
        "↔" | "<->" | "<=>" | "iff" => "IFF",
        "∈" | "in" => "IN",
        "++" | "append" => "APPEND",
        _ => return None,
    };
    Some(op)
}

/// Infix precedence. `ARROW`/`IFF` are right-associative, the rest are
/// left-associative (see [`Parser::expr`]).
fn precedence(op: &str) -> Option<u8> {
    let p = match op {
        "IFF" => 5,
        "ARROW" => 7,
        "OR" => 8,
        "AND" => 9,
        "EQ" | "NEQ" | "IN" => 10,
        "LT" | "LE" | "GT" | "GE" => 20,
        "ADD" | "SUB" | "APPEND" => 30,
        "MUL" | "DIV" | "MOD" => 40,
        _ => return None,
    };
    Some(p)
}

/// Sort aliases. Deliberately does *not* include single letters (`n`, `z`,
/// `b`): those are variable names in real statements far more often than
/// they are sort names.
fn sort_of(name: &str) -> Option<&'static str> {
    let low = unqualify(name).to_lowercase();
    let s = match low.as_str() {
        "nat" | "ℕ" | "natural" => "NAT",
        "int" | "ℤ" | "integer" => "INT",
        "bool" | "𝔹" | "boolean" => "BOOL",
        "real" | "ℝ" => "REAL",
        "prop" | "set" | "type" | "sort" | "type0" | "universe" => "TYPE",
        "string" | "text" => "STRING",
        "list" => "LIST",
        "vector" | "vect" => "VEC",
        _ => return None,
    };
    Some(s)
}

fn is_pi_kw(name: &str) -> bool {
    let low = unqualify(name).to_lowercase();
    matches!(low.as_str(), "forall" | "∀" | "pi" | "π" | "all")
}

fn is_lam_kw(name: &str) -> bool {
    let low = unqualify(name).to_lowercase();
    matches!(low.as_str(), "fun" | "lambda" | "λ" | "fn")
}

fn is_decl_kw(name: &str) -> bool {
    let low = unqualify(name).to_lowercase();
    matches!(
        low.as_str(),
        "theorem"
            | "lemma"
            | "def"
            | "definition"
            | "opaque"
            | "axiom"
            | "corollary"
            | "proposition"
            | "remark"
            | "fact"
            | "example"
            | "goal"
            | "assert"
            | "fixpoint"
            | "inductive"
            | "coinductive"
            | "data"
            | "record"
            | "function"
            | "procedure"
            | "declare-fun"
            | "declare-const"
            | "declare"
            | "thm"
            | "prop"
            | "constant"
    )
}

fn is_cut_kw(name: &str) -> bool {
    matches!(
        unqualify(name).to_lowercase().as_str(),
        ":=" | "by" | "proof" | "qed" | "where"
    )
}

/// Dotted names reduce to their last component before lookup.
fn unqualify(name: &str) -> &str {
    match name.rfind('.') {
        Some(i) if i + 1 < name.len() => &name[i + 1..],
        _ => name,
    }
}

// ===========================================================================
// Lexer
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tk {
    /// A source identifier (candidate variable, sort, name or operator).
    Id(String),
    /// An identifier that must not be re-read as an operator (`_<_` …).
    Name(String),
    Num(String),
    Sym(String),
    Open(char),
    Close(char),
}

const MULTI: [&str; 19] = [
    "<->", "<=>", "-->", "->>", "::=", ":=", "->", "=>", "<=", ">=", "!=", "==", "/\\", "\\/",
    "&&", "||", "::", "++", "<>",
];

fn is_ident_start(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn lex(src: &str) -> Vec<Tk> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut out: Vec<Tk> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // line comments
        if (c == '-' && i + 1 < n && chars[i + 1] == '-')
            || (c == '/' && i + 1 < n && chars[i + 1] == '/')
        {
            while i < n && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // block comment
        if c == '(' && i + 1 < n && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < n && !(chars[i] == '*' && chars[i + 1] == ')') {
                i += 1;
            }
            i = (i + 2).min(n);
            continue;
        }
        // quoted statement (Isabelle quotes the whole formula)
        if c == '"' {
            let mut j = i + 1;
            while j < n && chars[j] != '"' {
                j += 1;
            }
            let inner: String = chars[i + 1..j.min(n)].iter().collect();
            out.extend(lex(&inner));
            i = j + 1;
            continue;
        }
        // multi-character symbols (longest match first)
        let mut matched: Option<&str> = None;
        for m in MULTI {
            let mchars: Vec<char> = m.chars().collect();
            if chars[i..].starts_with(&mchars) {
                matched = Some(m);
                break;
            }
        }
        if let Some(m) = matched {
            out.push(Tk::Sym(m.to_string()));
            i += m.chars().count();
            continue;
        }
        if c == '(' || c == '[' || c == '{' {
            out.push(Tk::Open(c));
            i += 1;
            continue;
        }
        if c == ')' || c == ']' || c == '}' {
            out.push(Tk::Close(c));
            i += 1;
            continue;
        }
        if is_ident_start(c) || c == '.' {
            let mut j = i;
            while j < n && is_ident_char(chars[j]) {
                j += 1;
            }
            // dotted qualification: only when an identifier continues
            while j + 1 < n && chars[j] == '.' && is_ident_start(chars[j + 1]) {
                j += 1;
                while j < n && is_ident_char(chars[j]) {
                    j += 1;
                }
            }
            if j == i {
                out.push(Tk::Sym(c.to_string()));
                i += 1;
                continue;
            }
            let text: String = chars[i..j].iter().collect();
            let is_num = text.chars().all(|ch| ch.is_ascii_digit());
            out.push(if is_num { Tk::Num(text) } else { Tk::Id(text) });
            i = j;
            continue;
        }
        out.push(Tk::Sym(c.to_string()));
        i += 1;
    }
    out
}

// ===========================================================================
// Token pre-pass
// ===========================================================================

fn token_text(t: &Tk) -> String {
    match t {
        Tk::Id(s) | Tk::Name(s) | Tk::Num(s) | Tk::Sym(s) => s.clone(),
        Tk::Open(c) | Tk::Close(c) => c.to_string(),
    }
}

fn is_open(t: &Tk) -> bool {
    matches!(t, Tk::Open(_))
}

fn is_close(t: &Tk) -> bool {
    matches!(t, Tk::Close(_))
}

/// Index of the bracket matching `toks[at]` (an opening bracket), or the
/// last index when unbalanced.
fn matching(toks: &[Tk], at: usize) -> usize {
    let mut depth = 0usize;
    for (j, t) in toks.iter().enumerate().skip(at) {
        if is_open(t) {
            depth += 1;
        } else if is_close(t) {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return j;
            }
        }
    }
    toks.len().saturating_sub(1)
}

/// The tokens strictly between an opening bracket at `open` and the index
/// [`matching`] returned for it. Empty when nothing lies between, which
/// includes an unbalanced opening bracket that is the last token: there
/// [`matching`] returns `open` itself, and slicing `open + 1..open` panics.
fn between(toks: &[Tk], open: usize, close: usize) -> &[Tk] {
    toks.get(open + 1..close).unwrap_or(&[])
}

/// Agda writes operators as names: `_<_`, `_+_`, `_≡_`. Read the wrapped
/// symbol as one atom so it is not mistaken for three punctuation tokens.
fn glue_agda_operators(toks: &[Tk]) -> Vec<Tk> {
    let mut out: Vec<Tk> = Vec::new();
    let mut i = 0usize;
    while i < toks.len() {
        let is_underscore = matches!(&toks[i], Tk::Id(s) if s == "_");
        if is_underscore && i + 2 < toks.len() {
            let inner = match &toks[i + 1] {
                Tk::Sym(s) => Some(s.clone()),
                Tk::Id(s) if s == "_" => Some(s.clone()),
                _ => None,
            };
            let closes = matches!(&toks[i + 2], Tk::Id(s) if s == "_" || s == "'_" || s == "_'");
            if let (Some(sym), true) = (inner, closes) {
                let canon = op_of(&sym).map(|s| s.to_string()).unwrap_or(sym);
                out.push(Tk::Name(canon));
                i += 3;
                if i < toks.len() && matches!(&toks[i], Tk::Id(s) if s == "'") {
                    i += 1;
                }
                continue;
            }
        }
        out.push(toks[i].clone());
        i += 1;
    }
    out
}

/// A binder group is `x y : T`; `(A -> B)` is a type and must not be
/// mistaken for one.
fn has_colon(toks: &[Tk]) -> bool {
    toks.iter()
        .any(|t| matches!(t, Tk::Sym(s) if s == ":" || s == "::"))
}

/// Whether a top-level `:` or `::=` occurs in `toks` (depth 0 relative to
/// the start of the slice).
fn colon_at_top(toks: &[Tk]) -> bool {
    let mut depth = 0usize;
    for t in toks {
        if is_open(t) {
            depth += 1;
        } else if is_close(t) {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && matches!(t, Tk::Sym(s) if s == ":" || s == "::=") {
            return true;
        }
    }
    false
}

/// `+-comm : body` and `addComm : body` and `: Π …` all have the declared
/// name before a top-level colon; drop it. A group that starts the
/// statement (`(x y : Nat) : body`) means there is no head to drop.
///
/// The second value reports a drop that was *not* a declared head: the
/// first top-level bracket comes after other tokens and no top-level colon
/// follows it, so the dropped tokens were the statement's own (`f (g x) = y`
/// loses `f`). The key is unchanged; [`StructuralKey::complete`] reports it.
fn drop_declared_head(toks: Vec<Tk>) -> (Vec<Tk>, bool) {
    let mut depth = 0usize;
    for (i, t) in toks.iter().enumerate() {
        if is_open(t) {
            if depth == 0 {
                let unexplained = i > 0 && !colon_at_top(&toks[i..]);
                return (toks[i..].to_vec(), unexplained);
            }
            depth += 1;
        } else if is_close(t) {
            depth = depth.saturating_sub(1);
        } else if depth == 0 {
            if let Tk::Sym(s) = t {
                if s == ":" || s == "::=" {
                    return (toks[i + 1..].to_vec(), false);
                }
            }
            if let Tk::Id(s) = t {
                if is_pi_kw(s) || is_lam_kw(s) {
                    return (toks[i..].to_vec(), false);
                }
            }
        }
    }
    (toks, false)
}

/// `(assert (forall …))` → `(forall …)`.
fn unwrap_assert(toks: Vec<Tk>) -> Vec<Tk> {
    let mut cur = toks;
    loop {
        if !cur.first().map(is_open).unwrap_or(false) {
            return cur;
        }
        let j = matching(&cur, 0);
        if j + 1 != cur.len() {
            return cur;
        }
        let inner = between(&cur, 0, j).to_vec();
        let head_is_assert = match inner.first() {
            Some(Tk::Id(s)) => matches!(
                s.to_lowercase().as_str(),
                "assert" | "goal" | "check-sat" | "theorem"
            ),
            _ => false,
        };
        if !head_is_assert {
            return cur;
        }
        cur = inner[1..].to_vec();
    }
}

/// The statement body with any declaration header and proof body removed, and
/// whether the header drop discarded tokens that were not a declared head:
/// a bracket drop (see [`drop_declared_head`]), or a declaration keyword
/// with no top-level `:` or `::=` after it. Keywords match case-insensitively, so a
/// statement that merely *starts* with one (HOL4's `FACT 1 = 1`, keyed as
/// `1 = 1`) loses it; without either separator the drop is flagged.
fn strip_header(toks: &[Tk]) -> (Vec<Tk>, bool) {
    let mut cur = unwrap_assert(glue_agda_operators(toks));
    // declaration keyword + declared name
    let mut dropped_kw = false;
    loop {
        let drops_kw = matches!(cur.first(), Some(Tk::Id(s)) if is_decl_kw(s));
        if !drops_kw {
            break;
        }
        dropped_kw = true;
        cur.remove(0);
        if matches!(cur.first(), Some(Tk::Id(_))) {
            cur.remove(0);
        }
    }
    // proof body begins at a top-level `:=` / `by` / `where`
    let mut depth = 0usize;
    let mut cut: Option<usize> = None;
    for (i, t) in cur.iter().enumerate() {
        if is_open(t) {
            depth += 1;
        } else if is_close(t) {
            depth = depth.saturating_sub(1);
        } else if depth == 0 {
            let text = token_text(t);
            if is_cut_kw(&text) || text == ":=" {
                cut = Some(i);
                break;
            }
        }
    }
    let cur = match cut {
        Some(i) => cur[..i].to_vec(),
        None => cur,
    };
    let keyword_unexplained = dropped_kw && !colon_at_top(&cur);
    let (body, head_unexplained) = drop_declared_head(cur);
    (body, head_unexplained || keyword_unexplained)
}

/// `x y : Nat` → (["x","y"], NAT); SMT-LIB `x Nat` likewise.
fn split_binder_group(inner: &[Tk]) -> (Vec<String>, String) {
    let mut names: Vec<String> = Vec::new();
    for (k, t) in inner.iter().enumerate() {
        if let Tk::Sym(s) = t {
            if s == ":" || s == "::" {
                return (names, sort_name(&inner[k + 1..]));
            }
        }
        if let Tk::Id(s) = t {
            names.push(s.clone());
        }
    }
    if names.len() == 2 && !inner.iter().any(|t| matches!(t, Tk::Sym(_))) {
        let sort = sort_of(&names[1])
            .map(|s| s.to_string())
            .unwrap_or_else(|| names[1].to_uppercase());
        return (vec![names[0].clone()], sort);
    }
    (names, "?".to_string())
}

fn sort_name(toks: &[Tk]) -> String {
    for t in toks {
        if let Tk::Id(s) = t {
            return sort_of(s)
                .map(|s| s.to_string())
                .unwrap_or_else(|| unqualify(s).to_uppercase());
        }
    }
    "?".to_string()
}

/// Declared binders, in declaration order, with their sorts.
#[derive(Debug, Clone, Default)]
struct Binders {
    names: Vec<String>,
    sorts: Vec<String>,
    /// A leading bracket group was read as a telescope although one of its
    /// "names" is a binder keyword: `(forall x : nat, P x) -> Q` binds
    /// `forall` and `x` and keeps only `Q`. Reported through
    /// [`StructuralKey::complete`]; the key is unchanged.
    misread: bool,
}

impl Binders {
    fn push(&mut self, names: &[String], sort: &str) {
        for n in names {
            self.names.push(n.clone());
            self.sorts.push(sort.to_string());
        }
    }
}

/// Remove binder syntax from the stream, recording what was bound.
///
/// Handles the four shapes that actually occur: SMT-LIB
/// `(forall ((x Nat) (y Nat)) …)`, keyword binders `forall x y : T, …` /
/// `∀ (x y : T) → …` / `Π (x y : Nat), …`, keyword-less leading groups
/// (`theorem f (x y : Nat) : …`, `f : (x, y : Nat) -> …`), and Isabelle's
/// `(x::nat)` ascriptions (which bind nothing).
fn extract_binders(toks: &[Tk]) -> (Vec<Tk>, Binders) {
    let mut bound = Binders::default();
    let mut cur: Vec<Tk> = toks.to_vec();

    // 1. leading binder group without a keyword
    while cur.first().map(is_open).unwrap_or(false) {
        let j = matching(&cur, 0);
        let (names, sort) = split_binder_group(between(&cur, 0, j));
        if names.is_empty() {
            break;
        }
        let after_ok = cur
            .get(j + 1)
            .map(|t| matches!(t, Tk::Sym(s) if s == ":" || s == "->" || s == "→" || s == ","))
            .unwrap_or(false);
        if !after_ok {
            break;
        }
        if !has_colon(between(&cur, 0, j)) {
            break;
        }
        if names.iter().any(|n| is_pi_kw(n) || is_lam_kw(n)) {
            bound.misread = true;
        }
        for n in &names {
            bound.push(std::slice::from_ref(n), &sort);
        }
        cur = cur[(j + 2).min(cur.len())..].to_vec();
    }

    // 2. SMT-LIB: the whole statement is `(forall ((x Nat) (y Nat)) body)`
    if cur.first().map(is_open).unwrap_or(false) {
        let j = matching(&cur, 0);
        if j + 1 == cur.len() {
            let inner: Vec<Tk> = between(&cur, 0, j).to_vec();
            let head_ok = matches!(inner.first(), Some(Tk::Id(s)) if is_pi_kw(s) || is_lam_kw(s));
            if head_ok {
                let rest: Vec<Tk> = inner[1..].to_vec();
                if rest.first().map(is_open).unwrap_or(false) {
                    let m = matching(&rest, 0);
                    let group: Vec<Tk> = between(&rest, 0, m).to_vec();
                    let mut names: Vec<String> = Vec::new();
                    let mut sorts: Vec<String> = Vec::new();
                    if group.first().map(is_open).unwrap_or(false) {
                        let mut k = 0usize;
                        while k < group.len() && is_open(&group[k]) {
                            let e = matching(&group, k);
                            let (n, s) = split_binder_group(between(&group, k, e));
                            for name in n {
                                names.push(name);
                                sorts.push(s.clone());
                            }
                            k = e + 1;
                        }
                    } else {
                        let (n, s) = split_binder_group(&group);
                        for name in n {
                            names.push(name);
                            sorts.push(s.clone());
                        }
                    }
                    if !names.is_empty() {
                        for (name, sort) in names.iter().zip(sorts.iter()) {
                            bound.push(std::slice::from_ref(name), sort);
                        }
                        cur = rest[m + 1..].to_vec();
                    }
                }
            }
        }
    }

    // 3. keyword binders anywhere at the head of the remaining stream
    let mut out: Vec<Tk> = Vec::new();
    let mut i = 0usize;
    while i < cur.len() {
        let head_ok = match &cur[i] {
            Tk::Id(s) => is_pi_kw(s) || is_lam_kw(s),
            Tk::Sym(s) => is_pi_kw(s) || is_lam_kw(s),
            _ => false,
        };
        if !head_ok {
            out.push(cur[i].clone());
            i += 1;
            continue;
        }
        i += 1;
        let mut names: Vec<String> = Vec::new();
        let mut sorts: Vec<String> = Vec::new();
        let mut pending: Vec<String> = Vec::new();
        while i < cur.len() {
            let stop = matches!(&cur[i], Tk::Sym(s) if s == "," || s == "." || s == "->" || s == "→" || s == "=>");
            if stop {
                for n in pending.drain(..) {
                    names.push(n);
                    sorts.push("?".to_string());
                }
                i += 1;
                break;
            }
            if is_open(&cur[i]) {
                let m = matching(&cur, i);
                let (n, s) = split_binder_group(between(&cur, i, m));
                if n.is_empty() {
                    break;
                }
                for name in n {
                    names.push(name);
                    sorts.push(s.clone());
                }
                i = m + 1;
                continue;
            }
            if let Tk::Id(name) = cur[i].clone() {
                let next_colon = matches!(
                    cur.get(i + 1),
                    Some(Tk::Sym(s)) if s == ":" || s == "::"
                );
                if next_colon {
                    let mut k = i + 2;
                    let mut st: Vec<Tk> = Vec::new();
                    while k < cur.len() {
                        let terminator = is_close(&cur[k])
                            || matches!(&cur[k], Tk::Sym(s) if s == "," || s == "." || s == "->" || s == "→");
                        if terminator {
                            break;
                        }
                        st.push(cur[k].clone());
                        k += 1;
                    }
                    pending.push(name);
                    for n in pending.drain(..) {
                        names.push(n);
                        sorts.push(sort_name(&st));
                    }
                    i = k;
                    continue;
                }
                pending.push(name);
                i += 1;
                continue;
            }
            break;
        }
        for n in pending.drain(..) {
            names.push(n);
            sorts.push("?".to_string());
        }
        if !names.is_empty() {
            for (name, sort) in names.iter().zip(sorts.iter()) {
                bound.push(std::slice::from_ref(name), sort);
            }
        }
    }
    (out, bound)
}

/// Unwrap Isabelle-style `(x :: nat)` ascriptions with recognised sorts,
/// retaining the term identifier. Other groups are preserved.
fn drop_ascriptions(toks: &[Tk]) -> Vec<Tk> {
    let mut out: Vec<Tk> = Vec::new();
    let mut i = 0usize;
    while i < toks.len() {
        if is_open(&toks[i]) {
            // Only `( x :: sort )` qualifies, so a group without `::` in second
            // place is left alone without scanning for its close (that scan
            // made this quadratic on deeply nested input).
            let could_ascribe = matches!(toks.get(i + 2), Some(Tk::Sym(s)) if s == "::");
            if !could_ascribe {
                out.push(toks[i].clone());
                i += 1;
                continue;
            }
            let j = matching(toks, i);
            let inner: Vec<Tk> = between(toks, i, j).to_vec();
            let ids: Vec<&String> = inner
                .iter()
                .filter_map(|t| match t {
                    Tk::Id(s) => Some(s),
                    _ => None,
                })
                .collect();
            let syms: Vec<&String> = inner
                .iter()
                .filter_map(|t| match t {
                    Tk::Sym(s) => Some(s),
                    _ => None,
                })
                .collect();
            if ids.len() == 2 && syms.len() == 1 && syms[0] == "::" && sort_of(ids[1]).is_some() {
                out.push(Tk::Id(ids[0].clone()));
                i = j + 1;
                continue;
            }
        }
        out.push(toks[i].clone());
        i += 1;
    }
    out
}

// ===========================================================================
// Term
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum Node {
    Var(String),
    Name(String),
    Num(String),
    Sort(String),
    Hole,
    Op(&'static str, Vec<Node>),
    App(Vec<Node>),
}

struct Parser {
    toks: Vec<Tk>,
    i: usize,
    varmap: std::collections::HashMap<String, String>,
    /// Opening brackets the input ended before closing: a statement
    /// truncated inside a group (`(x = y`) parses to the end and would
    /// otherwise look complete.
    unclosed: usize,
    /// Current bracket nesting, bounded by [`MAX_NESTING`].
    depth: usize,
    /// A group deeper than [`MAX_NESTING`] was skipped as a hole.
    too_deep: bool,
}

/// Deepest bracket nesting the parser descends into. Each level costs three
/// stack frames (`expr` → `app` → `atom`), and `structural_key` runs on the
/// caller's stack (`corpus ingest`, octad export), so a statement nested
/// deeper than this is cut off rather than allowed to overflow it. The
/// shipped corpora reach a depth in the fifties.
const MAX_NESTING: usize = 256;

impl Parser {
    /// Start at the first token, using `varmap` to map source names to canonical variables.
    fn new(toks: Vec<Tk>, varmap: std::collections::HashMap<String, String>) -> Self {
        Parser {
            toks,
            i: 0,
            varmap,
            unclosed: 0,
            depth: 0,
            too_deep: false,
        }
    }

    fn peek(&self) -> Option<&Tk> {
        self.toks.get(self.i)
    }

    /// Whether everything after the cursor is ignorable: a statement
    /// terminator (`.`, `,`, `;`) or an unmatched closing bracket.
    fn rest_is_ignorable(&self) -> bool {
        self.toks[self.i.min(self.toks.len())..]
            .iter()
            .all(|t| match t {
                Tk::Close(_) => true,
                Tk::Sym(s) => matches!(s.as_str(), "." | "," | ";"),
                _ => false,
            })
    }

    /// Canonical operator starting at the cursor, if any.
    fn op_at(&self) -> Option<&'static str> {
        match self.peek()? {
            Tk::Id(s) | Tk::Sym(s) => op_of(s),
            _ => None,
        }
    }

    /// Read an atom or bracketed expression, advancing the cursor. Return
    /// `None` at end of input, before a closing bracket, or after consuming
    /// `:`, `::`, `,` or `.`. Groups beyond the nesting limit become holes
    /// and set `too_deep`; groups ending at EOF set `unclosed`.
    fn atom(&mut self) -> Option<Node> {
        let t = self.peek()?.clone();
        match t {
            Tk::Open(_) => {
                if self.depth >= MAX_NESTING {
                    // Skip the whole group; the key is marked incomplete.
                    self.too_deep = true;
                    self.i = matching(&self.toks, self.i) + 1;
                    return Some(Node::Hole);
                }
                self.depth += 1;
                self.i += 1;
                let inner = self.expr(0);
                self.depth -= 1;
                if matches!(self.peek(), Some(Tk::Close(_))) {
                    self.i += 1;
                } else if self.peek().is_none() {
                    self.unclosed += 1;
                }
                Some(inner)
            },
            Tk::Close(_) => None,
            Tk::Num(s) => {
                self.i += 1;
                Some(Node::Num(s))
            },
            Tk::Name(s) => {
                self.i += 1;
                Some(Node::Name(s))
            },
            Tk::Sym(s) => {
                if s == ":" || s == "::" || s == "," || s == "." {
                    self.i += 1;
                    return None;
                }
                match op_of(&s) {
                    Some(op) => {
                        self.i += 1;
                        Some(Node::Op(op, Vec::new()))
                    },
                    None => {
                        self.i += 1;
                        Some(Node::Name(s))
                    },
                }
            },
            Tk::Id(s) => {
                self.i += 1;
                if let Some(v) = self.varmap.get(&s).cloned() {
                    return Some(Node::Var(v));
                }
                if let Some(op) = op_of(&s) {
                    return Some(Node::Op(op, Vec::new()));
                }
                if let Some(sort) = sort_of(&s) {
                    return Some(Node::Sort(sort.to_string()));
                }
                Some(Node::Name(unqualify(&s).to_string()))
            },
        }
    }

    /// Application, including prefix operator use: `(+ x y)`.
    fn app(&mut self) -> Node {
        // A bracketed group is already complete: `(eq a b)` must not be
        // re-read as the prefix form `eq a b`, or the group's own arguments
        // are swallowed by the enclosing application and the term collapses
        // to a bare operator name.
        let from_group = matches!(self.peek(), Some(Tk::Open(_)));
        let head = match self.atom() {
            Some(h) => h,
            None => return Node::Hole,
        };
        if let Node::Op(op, args) = head.clone() {
            if from_group {
                return if args.is_empty() {
                    Node::Name(op.to_string())
                } else {
                    head
                };
            }
            let mut args: Vec<Node> = Vec::new();
            loop {
                let stop = match self.peek() {
                    None => true,
                    Some(t) => is_close(t) || self.op_at().is_some(),
                };
                if stop {
                    break;
                }
                match self.atom() {
                    Some(a) => args.push(a),
                    None => break,
                }
            }
            let op_name = op;
            // Dedukti/SMT-LIB write the sort explicitly: `eq Nat a b`.
            if args.len() == 3
                && matches!(args[0], Node::Sort(_))
                && matches!(op_name, "EQ" | "NEQ" | "LT" | "LE" | "GT" | "GE")
            {
                args.remove(0);
            }
            if args.is_empty() {
                return Node::Name(op_name.to_string());
            }
            return Node::Op(op_name, args);
        }
        let mut args: Vec<Node> = vec![head.clone()];
        loop {
            match self.peek() {
                None => break,
                Some(t) => {
                    if is_close(t) || self.op_at().is_some() {
                        break;
                    }
                    if matches!(t, Tk::Sym(s) if s == "," || s == ":" || s == "::" || s == ".") {
                        break;
                    }
                },
            }
            match self.atom() {
                Some(a) => args.push(a),
                None => break,
            }
        }
        if args.len() == 1 {
            return args.remove(0);
        }
        Node::App(args)
    }

    fn expr(&mut self, min_prec: u8) -> Node {
        let mut left = self.app();
        while let Some(op) = self.op_at() {
            let Some(prec) = precedence(op) else {
                break;
            };
            if prec < min_prec {
                break;
            }
            self.i += 1;
            let rhs_min = if op == "ARROW" || op == "IFF" {
                prec
            } else {
                prec + 1
            };
            let right = self.expr(rhs_min);
            left = Node::Op(op, vec![left, right]);
        }
        left
    }
}

fn render(node: &Node, skeleton: bool) -> String {
    match node {
        Node::Var(s) | Node::Name(s) | Node::Num(s) => s.clone(),
        Node::Sort(s) => {
            if skeleton {
                "?".to_string()
            } else {
                s.clone()
            }
        },
        Node::Hole => "_".to_string(),
        Node::Op(op, kids) => {
            let mut out = String::from("(");
            out.push_str(op);
            for k in kids {
                out.push(' ');
                out.push_str(&render(k, skeleton));
            }
            out.push(')');
            out
        },
        Node::App(kids) => {
            let mut out = String::from("(");
            for (i, k) in kids.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&render(k, skeleton));
            }
            out.push(')');
            out
        },
    }
}

// ===========================================================================
// Public API
// ===========================================================================

fn sha256_hex(s: &str) -> String {
    let mut h = Sha256::new();
    h.update(s.as_bytes());
    let digest = h.finalize();
    let mut out = String::with_capacity(digest.len() * 2);
    for b in digest.iter() {
        out.push_str(&format!("{:02x}", b));
    }
    out
}

/// Normalised text, used as the last-resort tier when a statement does not
/// parse into a term at all (a bare type name, a stray data declaration).
fn text_shape(statement: &str) -> String {
    statement
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_lowercase()
}

fn is_blank_shape(shape: &str) -> bool {
    let trimmed = shape.trim();
    trimmed.is_empty() || trimmed == "_" || trimmed == "()" || trimmed.chars().all(|c| c == '?')
}

/// Number every variable `v0`, `v1`, … in order of first appearance.
///
/// A name counts as a variable when it is a declared binder, a short
/// lower-case name (`x`, `xs`, `p'`), or a single upper-case letter (`A`,
/// the Coq/Lean convention for a type variable). Sorts and canonical
/// operators never become variables, whatever they look like.
fn number_variables(body: &[Tk], bound: &Binders) -> std::collections::HashMap<String, String> {
    let mut varmap: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut next = 0usize;
    for t in body {
        let name = match t {
            Tk::Id(name) => name,
            _ => continue,
        };
        if sort_of(name).is_some() || op_of(name).is_some() || is_pi_kw(name) || is_lam_kw(name) {
            continue;
        }
        let tail = unqualify(name);
        let looks_like_var = bound.names.iter().any(|n| n == name)
            || match tail.chars().next() {
                Some(c) if c.is_lowercase() => tail.chars().count() <= 3,
                Some(c) if c.is_uppercase() => tail.chars().count() == 1,
                _ => false,
            };
        if looks_like_var && !varmap.contains_key(name) {
            varmap.insert(name.clone(), format!("v{}", next));
            next += 1;
        }
    }
    varmap
}

/// Tokens that introduce notation this scheme has no rule for: HOL's `!`,
/// `?`, `@` and `\` binders and `~` negation, Isabelle's `\<…>` symbol
/// escapes (which lex as `\`, `<`, name, `>`), and Lean 3's `$` application.
/// The parser reads them as plain names and consumes them, so a shape can
/// look complete and still be wrong; their presence marks the key
/// incomplete. Over-cautious by design: Lean's `s \ t` set difference is
/// flagged too.
fn is_unread_notation(t: &Tk) -> bool {
    matches!(t, Tk::Sym(s) if matches!(s.as_str(), "\\" | "!" | "?" | "@" | "$" | "~"))
}

/// Whether the body holds unread notation: a token [`is_unread_notation`]
/// names, or HOL's `==>` implication, which the lexer splits into `==` and
/// `>` (the shape it then renders is an equality applied to a comparison).
/// The lexer is left alone so that no key changes; only the flag sees it.
fn has_unread_notation(body: &[Tk]) -> bool {
    body.iter().any(is_unread_notation)
        || body
            .windows(2)
            .any(|w| matches!((&w[0], &w[1]), (Tk::Sym(a), Tk::Sym(b)) if a == "==" && b == ">"))
}

/// Both canonical forms from one pass, and whether the shape accounts for
/// the whole statement: `(shape, skeleton, complete)`. Complete means the
/// header drop discarded only a declared head, no leading group was misread
/// as a telescope, the body holds no unread notation, and the parser
/// left only ignorable terminators or closing brackets, with no group
/// left open at end of input or skipped beyond [`MAX_NESTING`].
fn normalise(statement: &str) -> (String, String, bool) {
    let (toks, dropped_body) = strip_header(&lex(statement));
    let toks = drop_ascriptions(&toks);
    let (body, bound) = extract_binders(&toks);
    let varmap = number_variables(&body, &bound);
    let unread = has_unread_notation(&body);
    let mut parser = Parser::new(body, varmap);
    let ast = parser.expr(0);
    let complete = parser.rest_is_ignorable()
        && parser.unclosed == 0
        && !parser.too_deep
        && !unread
        && !dropped_body
        && !bound.misread;

    let core = render(&ast, false);
    let skel = render(&ast, true);

    let mut shape = if is_blank_shape(&core) {
        String::new()
    } else {
        core
    };
    if !shape.is_empty() && !bound.names.is_empty() {
        shape = format!("(PI [{}] {})", bound.sorts.join(" "), shape);
    }
    let skeleton = if is_blank_shape(&skel) {
        String::new()
    } else {
        skel
    };
    (shape, skeleton, complete)
}

/// Canonical prefix shape of `statement`, binder prefix included.
pub fn canonical_shape(statement: &str) -> String {
    normalise(statement).0
}

/// Same normalisation as [`canonical_shape`] with binders and sorts erased.
pub fn canonical_skeleton(statement: &str) -> String {
    normalise(statement).1
}

/// Structural identity of a declaration's statement.
///
/// The three tiers are tried in order: the shape as written; the shape with
/// binders and sorts erased (covers provers that elide them); and finally
/// whitespace-normalised text (covers statements that are not terms).
/// A partial parse can still yield a structural key; consult
/// [`StructuralKey::complete`] before treating it as the whole statement.
/// Text-tier keys always have `complete = false`.
pub fn structural_key(statement: &str) -> StructuralKey {
    let (shape, skeleton, parsed_all) = normalise(statement);

    let (shape, skeleton, tier) = if !shape.is_empty() {
        (shape, skeleton, KeyTier::Structural)
    } else if !skeleton.is_empty() {
        (skeleton.clone(), skeleton, KeyTier::Skeleton)
    } else {
        let text = text_shape(statement);
        (text.clone(), text, KeyTier::Text)
    };

    StructuralKey {
        scheme: SCHEME.to_string(),
        key: sha256_hex(&shape),
        skeleton_key: sha256_hex(&skeleton),
        shape,
        skeleton,
        complete: parsed_all && tier != KeyTier::Text,
        tier,
    }
}

/// Canonical atoms of a statement, for the structural embedder's n-grams.
///
/// Falls back to the lower-cased source tokens when the statement does not
/// parse, so every declaration contributes *something*.
pub fn canonical_tokens(statement: &str) -> Vec<String> {
    let shape = canonical_shape(statement);
    let source = if shape.is_empty() {
        text_shape(statement)
    } else {
        shape
    };
    source
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']')
        .filter(|t| !t.is_empty())
        .map(|t| t.to_string())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ADD_COMM: [(&str, &str); 8] = [
        ("agda", "+-comm : ∀ (x y : ℕ) → x + y ≡ y + x"),
        ("coq", "Lemma add_comm : forall x y : nat, x + y = y + x."),
        (
            "lean4",
            "theorem Nat.add_comm (x y : Nat) : x + y = y + x := by omega",
        ),
        ("idris2", "addComm : (x, y : Nat) -> x + y = y + x"),
        ("isabelle", "lemma add_comm: \"(x::nat) + y = y + x\""),
        ("why3", "lemma add_comm: forall x y: int. x + y = y + x"),
        (
            "smtlib",
            "(assert (forall ((x Nat) (y Nat)) (= (+ x y) (+ y x))))",
        ),
        (
            "dedukti",
            "def add_comm : Π (x y : Nat), eq Nat (add x y) (add y x).",
        ),
    ];

    #[test]
    fn add_comm_is_one_shape_across_the_explicit_binder_provers() {
        let expected = "(PI [NAT NAT] (EQ (ADD v0 v1) (ADD v1 v0)))";
        for (lang, src) in ADD_COMM {
            if lang == "isabelle" || lang == "why3" {
                continue; // elided binders / different sort: see the skeleton test
            }
            assert_eq!(canonical_shape(src), expected, "{lang} disagrees");
        }
    }

    #[test]
    fn add_comm_skeleton_covers_the_eliding_provers() {
        let expected = "(EQ (ADD v0 v1) (ADD v1 v0))";
        for (lang, src) in ADD_COMM {
            assert_eq!(canonical_skeleton(src), expected, "{lang} disagrees");
        }
    }

    #[test]
    fn structural_key_agrees_across_languages() {
        let coq = structural_key(ADD_COMM[1].1);
        let lean = structural_key(ADD_COMM[2].1);
        let idris = structural_key(ADD_COMM[3].1);
        let smt = structural_key(ADD_COMM[6].1);
        let dk = structural_key(ADD_COMM[7].1);
        for k in [&lean, &idris, &smt, &dk] {
            assert_eq!(k.key, coq.key, "primary key drifted: {}", k.shape);
        }
        // Isabelle states the same theorem without binders or an explicit
        // sort; it must still join on the skeleton.
        let isabelle = structural_key(ADD_COMM[4].1);
        assert_eq!(isabelle.skeleton_key, coq.skeleton_key);
        assert_eq!(coq.tier, KeyTier::Structural);
    }

    #[test]
    fn alpha_renaming_does_not_change_the_key() {
        let a = structural_key("Lemma c : forall x y : nat, x + y = y + x.");
        let b = structural_key("Lemma c : forall a b : nat, a + b = b + a.");
        assert_eq!(a.key, b.key);
        assert_eq!(a.shape, b.shape);
    }

    #[test]
    fn different_statements_keep_different_keys() {
        let comm = structural_key("forall x y : nat, x + y = y + x");
        let assoc = structural_key("forall x y z : nat, (x + y) + z = x + (y + z)");
        assert_ne!(comm.key, assoc.key);
        // a free-variable statement must not collapse into a constant
        assert_ne!(comm.key, structural_key("").key);
    }

    #[test]
    fn arrows_are_right_associative_like_the_toolchains() {
        let coq = canonical_shape("Definition compose : (B -> C) -> (A -> B) -> A -> C.");
        let lean = canonical_shape("theorem compose : (B -> C) -> (A -> B) -> A -> C");
        assert_eq!(
            coq,
            "(ARROW (ARROW v0 v1) (ARROW (ARROW v2 v0) (ARROW v2 v1)))"
        );
        assert_eq!(coq, lean);
    }

    #[test]
    fn deduction_headers_and_bodies_are_dropped() {
        let with_body = structural_key("theorem add_zero (n : Nat) : n + 0 = n := by simp");
        let without = structural_key("theorem add_zero (n : Nat) : n + 0 = n");
        assert_eq!(with_body.key, without.key);
        assert_eq!(with_body.shape, "(PI [NAT] (EQ (ADD v0 0) v0))");
    }

    #[test]
    fn statements_with_no_term_fall_back_to_text() {
        // `data … where …` has no type expression before the `where` cut,
        // so there is nothing to key on structurally.
        let k = structural_key("data Bool where true false");
        assert_eq!(k.tier, KeyTier::Text);
        assert_eq!(k.shape, "data bool where true false");
        assert_eq!(k.key.len(), 64);
        assert_ne!(k.key, structural_key("data Nat where zero suc").key);
        // whitespace is not part of the text tier
        assert_eq!(
            k.key,
            structural_key("  data  Bool\n where  true false ").key
        );
    }

    #[test]
    fn scheme_is_versioned() {
        let k = structural_key("forall n : nat, n = n");
        assert_eq!(k.scheme, SCHEME);
        assert_eq!(k.key.len(), 64);
        assert_eq!(k.skeleton_key.len(), 64);
    }

    #[test]
    fn canonical_tokens_are_atoms_not_punctuation() {
        let toks = canonical_tokens("forall x y : nat, x + y = y + x");
        assert!(toks.contains(&"ADD".to_string()));
        assert!(toks.contains(&"EQ".to_string()));
        assert!(toks.contains(&"v0".to_string()));
        assert!(!toks.iter().any(|t| t.contains("forall")));
    }

    /// An opening bracket with nothing after it used to make `matching`
    /// return the bracket's own index, and every `open + 1..close` slice
    /// then panicked. Corpus statements truncated mid-term hit this.
    #[test]
    fn unbalanced_trailing_bracket_does_not_panic() {
        for s in [
            "(",
            "f x = (",
            "forall (",
            "∀ x, x = (",
            "(assert (",
            "(forall ((x Nat)) (",
            "theorem t (x : nat) : x = (",
        ] {
            let k = structural_key(s);
            assert_eq!(k.key.len(), 64, "{s:?}");
            assert_eq!(k.scheme, SCHEME);
        }
    }

    /// Every fixture spelling parses completely; the flag does not change
    /// any key.
    #[test]
    fn fixture_spellings_parse_completely() {
        for (prover, s) in ADD_COMM {
            let k = structural_key(s);
            assert!(k.complete, "{prover}: {s:?} -> {}", k.shape);
        }
        assert!(structural_key("Lemma add_comm : forall x y : nat, x + y = y + x.").complete);
    }

    /// Statements the scheme cannot read are marked incomplete even though
    /// they still get a structural-tier key.
    #[test]
    fn unread_notation_and_early_stops_are_incomplete() {
        for s in [
            // HOL binders, negation and implication (`==>` lexes as `==` `>`)
            "!m n. m + n = n + m",
            "?x. x = 0",
            "(\\x. x) = I",
            "~F",
            "F ==> T",
            // truncated inside a group: the parser reaches the end with the
            // group still open
            "(x = y",
            "(implies (and (bvp m) (< (len m) (expt 2 64))",
            // Isabelle ASCII symbol escapes
            "x \\<noteq> y \\<Longrightarrow> f x = f y",
            // Lean 3 `$`
            "f $ g x = h x",
        ] {
            let k = structural_key(s);
            assert!(!k.complete, "{s:?} -> {} should be incomplete", k.shape);
        }
        // Text tier is never complete.
        assert!(!structural_key("data Bool where true false").complete);
    }

    /// A statement with no declared head used to lose everything before its
    /// first top-level bracket (`exp(&0) = &1` keyed as `(EQ (& 0) (& 1))`,
    /// shared with `cos(&0) = &1`). The key is unchanged here; the drop is
    /// reported as incomplete so no consumer treats the prefix as identity.
    #[test]
    fn header_less_bracket_drop_is_incomplete() {
        let exp = structural_key("exp(0) = 1");
        let cos = structural_key("cos(0) = 1");
        assert_eq!(exp.key, cos.key, "the dk-shape-v1 behaviour this flags");
        assert!(!exp.complete && !cos.complete);
        assert!(!structural_key("closed (closure M)").complete);
        // A real declared head before a group is still a head.
        let lean = structural_key("theorem t (x y : nat) : x + y = y + x");
        assert!(lean.complete, "{}", lean.shape);
        let idris = structural_key("addComm : (x, y : Nat) -> x + y = y + x");
        assert!(idris.complete, "{}", idris.shape);
    }

    /// `FACT` is HOL's factorial and also matches the `fact` keyword: the
    /// key drops it (`FACT 1 = 1` keys as `1 = 1`), so the key is reported
    /// incomplete. A keyword followed by a declaration is still complete.
    #[test]
    fn keyword_drop_without_a_declaration_is_incomplete() {
        let fact = structural_key("FACT 1 = 1");
        assert_eq!(
            fact.key,
            structural_key("1 = 1").key,
            "the behaviour this flags"
        );
        assert!(!fact.complete);
        assert!(structural_key("1 = 1").complete);
        assert!(structural_key("Lemma add_comm : forall x y : nat, x + y = y + x.").complete);
        assert!(structural_key("theorem t (x y : nat) : x + y = y + x").complete);
    }

    /// A parenthesised quantified antecedent at the start of a statement is
    /// read as a binder telescope (`forall` and `x` become bound names and
    /// only `Q` is left). The key is unchanged; it is reported incomplete.
    #[test]
    fn telescope_misread_of_a_quantified_antecedent_is_incomplete() {
        let k = structural_key("(forall x : nat, P x) -> Q");
        assert_eq!(k.shape, "(PI [NAT NAT] v0)", "the behaviour this flags");
        assert!(!k.complete);
        // A real telescope is still complete.
        assert!(structural_key("(x y : nat) : x + y = y + x").complete);
    }

    /// Nesting past `MAX_NESTING` is cut off and marked incomplete instead
    /// of recursing once per level. Fifty thousand levels would overflow a
    /// test thread's stack without the bound; within the bound keys are as
    /// before.
    #[test]
    fn nesting_is_bounded() {
        let deep = format!("{}x{}", "(".repeat(50_000), ")".repeat(50_000));
        let k = structural_key(&deep);
        assert!(!k.complete);
        assert_eq!(k.key.len(), 64);
        let shallow = format!("{}x = y{}", "(".repeat(60), ")".repeat(60));
        let s = structural_key(&shallow);
        assert!(s.complete, "{}", s.shape);
        assert_eq!(s.key, structural_key("x = y").key);
    }

    /// The guard is a no-op on balanced input: keys stay as they were.
    #[test]
    fn balanced_input_keys_are_unchanged_by_the_bracket_guard() {
        assert_eq!(
            canonical_shape("forall x y : nat, x + y = y + x"),
            "(PI [NAT NAT] (EQ (ADD v0 v1) (ADD v1 v0)))"
        );
        assert_eq!(
            canonical_shape("(assert (forall ((x Nat) (y Nat)) (= (+ x y) (+ y x))))"),
            "(PI [NAT NAT] (EQ (ADD v0 v1) (ADD v1 v0)))"
        );
    }
}
