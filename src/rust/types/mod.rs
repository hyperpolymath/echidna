// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Unified native type-system decorations.
//!
//! ECHIDNA's core `Term` (see [`crate::core::Term`]) implements a minimal
//! dependently-typed λ-calculus. Many backends, however, operate under richer
//! type disciplines: linear / affine / graded types (Idris2 QTT, TypedWasm),
//! refinement types (F*, PVS), algebraic effects (F*, Dafny), modal logics
//! (epistemic / doxastic), temporal logics (SPIN, NuSMV, PRISM), relational /
//! parametric reasoning (Alloy), tropical semirings, and homotopy-level
//! stratifications (HoTT / cubical Agda).
//!
//! Rather than bloat `Term` with twelve new variants, we expose an optional
//! side-car [`TypeInfo`] decoration attachable to [`crate::core::Hypothesis`],
//! [`crate::core::Definition`], and [`crate::core::Variable`]. Backends that
//! understand a given decoration consume it; all other backends ignore it and
//! continue to work unchanged.
//!
//! # Supported dimensions
//!
//! | Dimension       | Representation                |
//! |-----------------|-------------------------------|
//! | Universes       | [`Universe`] (level, cumulativity, impredicativity, homotopy n-level) |
//! | Multiplicity    | [`Multiplicity`] (QTT / linear / affine / shared) |
//! | Effects         | [`EffectRow`] (row-polymorphic algebraic effects) |
//! | Refinements     | predicate `Term` attached under [`TypeInfo::refinement`] |
//! | Modality        | [`Modality`] (□, ◇, epistemic K_a, doxastic B_a, common, distributed) |
//! | Temporal        | [`TemporalOp`] (LTL / CTL / CTL\*) |
//! | Semiring        | [`Semiring`] (Boolean, ℕ, tropical min/max-plus, Viterbi, …) |
//! | Relational      | `relational_arity: u8` — 1 = unary, 2 = dyadic, n = n-ary |
//!
//! All decorations are optional: `TypeInfo::default()` carries no extra
//! obligations and is semantically transparent.

use crate::core::Term;
use serde::{Deserialize, Serialize};

/// Full decoration record attached to a typed entity.
///
/// Construction: start from [`TypeInfo::default()`] and use the chainable
/// `with_*` methods, e.g.:
///
/// ```
/// use echidna::types::{TypeInfo, Multiplicity};
/// let info = TypeInfo::default().with_multiplicity(Multiplicity::Linear);
/// assert_eq!(info.multiplicity, Some(Multiplicity::Linear));
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeInfo {
    /// Universe / sort stratification (level, cumulativity, HoTT level).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub universe: Option<Universe>,

    /// QTT multiplicity / linearity annotation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub multiplicity: Option<Multiplicity>,

    /// Algebraic / monadic effect row.
    #[serde(default, skip_serializing_if = "EffectRow::is_empty")]
    pub effects: EffectRow,

    /// Predicate refinement `{x : T | P x}` — stored as the predicate `Term`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refinement: Option<Box<Term>>,

    /// Modal decoration (alethic, epistemic, doxastic, deontic, …).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub modality: Option<Modality>,

    /// Temporal-logic operator (LTL / CTL / CTL*).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub temporal: Option<TemporalOp>,

    /// Underlying semiring for quantitative / tropical reasoning.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub semiring: Option<Semiring>,

    /// Relational arity: 1 = ordinary, 2 = dyadic / binary-parametric, n ≥ 3 = n-ary.
    /// `None` is equivalent to `Some(1)` — a normal unary type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub relational_arity: Option<u8>,
}

impl TypeInfo {
    /// Construct a fresh empty decoration (equivalent to `Default::default()`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Attach a universe specification.
    pub fn with_universe(mut self, u: Universe) -> Self {
        self.universe = Some(u);
        self
    }

    /// Attach a multiplicity / linearity annotation.
    pub fn with_multiplicity(mut self, m: Multiplicity) -> Self {
        self.multiplicity = Some(m);
        self
    }

    /// Attach an effect row.
    pub fn with_effects(mut self, e: EffectRow) -> Self {
        self.effects = e;
        self
    }

    /// Attach a refinement predicate (`{x : T | P x}`).
    pub fn with_refinement(mut self, pred: Term) -> Self {
        self.refinement = Some(Box::new(pred));
        self
    }

    /// Attach a modal operator.
    pub fn with_modality(mut self, m: Modality) -> Self {
        self.modality = Some(m);
        self
    }

    /// Attach a temporal operator.
    pub fn with_temporal(mut self, t: TemporalOp) -> Self {
        self.temporal = Some(t);
        self
    }

    /// Attach a semiring.
    pub fn with_semiring(mut self, s: Semiring) -> Self {
        self.semiring = Some(s);
        self
    }

    /// Declare relational arity (2 = dyadic / parametric, etc.).
    pub fn with_relational_arity(mut self, n: u8) -> Self {
        self.relational_arity = Some(n);
        self
    }

    /// True when no decoration is present — backends can skip processing.
    pub fn is_empty(&self) -> bool {
        self.universe.is_none()
            && self.multiplicity.is_none()
            && self.effects.is_empty()
            && self.refinement.is_none()
            && self.modality.is_none()
            && self.temporal.is_none()
            && self.semiring.is_none()
            && self.relational_arity.is_none()
    }
}

/// Universe / sort specification.
///
/// Captures level, cumulativity (ℝocq / Lean cumulative universes),
/// impredicativity (`Prop` / `SProp`), and HoTT n-type stratification.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Universe {
    /// Universe level (0 = ground / `Type 0`).
    pub level: usize,

    /// Is this universe cumulative (`Type i ⊆ Type (i+1)`)?
    #[serde(default)]
    pub cumulative: bool,

    /// Is this universe impredicative (e.g. Coq's `Prop`, Lean's `Prop`)?
    #[serde(default)]
    pub impredicative: bool,

    /// HoTT homotopy level (n-type): `Some(0)` = contractible, `Some(1)` =
    /// prop, `Some(2)` = set, higher = higher-groupoidal. `None` = unspecified
    /// (default for non-HoTT provers).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub homotopy_level: Option<u8>,
}

impl Universe {
    /// Predicative cumulative `Type level`.
    pub fn ty(level: usize) -> Self {
        Self { level, cumulative: true, impredicative: false, homotopy_level: None }
    }

    /// Impredicative proposition universe (`Prop`).
    pub fn prop() -> Self {
        Self { level: 0, cumulative: false, impredicative: true, homotopy_level: Some(1) }
    }

    /// HoTT n-type universe at the given homotopy level.
    pub fn hott(level: usize, n: u8) -> Self {
        Self { level, cumulative: true, impredicative: false, homotopy_level: Some(n) }
    }
}

/// Multiplicity / usage annotation (QTT 0/1/ω + linear / affine).
///
/// Idris2 uses 0-1-ω directly. Linear Haskell uses `Linear` (exactly-once).
/// Affine systems (Rust borrowck flavour) use `Affine` (at-most-once).
/// `Graded(n)` covers finer grading systems (exactly-n use).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Multiplicity {
    /// Erased at runtime (QTT 0).
    Zero,
    /// Used exactly once (QTT 1 / Linear Haskell `:1->`).
    One,
    /// Unrestricted (QTT ω).
    Omega,
    /// Used at most once (affine).
    Affine,
    /// Used exactly once (linear). Alias for [`Multiplicity::One`]-style but
    /// retained for systems that distinguish the two (e.g. Clean, Granule).
    Linear,
    /// Shared / unrestricted — alias of `Omega` for bang-calculus presentations.
    Shared,
    /// Exactly-n usage (bounded linear logic, graded modalities).
    Graded(u32),
}

/// Algebraic / monadic effect row (row-polymorphic).
///
/// `effects` is the concrete list of effects present. `row_var`, when set,
/// names a polymorphic tail (e.g. `{IO, Exn | ρ}`) — closed rows leave it
/// `None`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectRow {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effects: Vec<Effect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub row_var: Option<String>,
}

impl EffectRow {
    pub fn pure_row() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.effects.is_empty() && self.row_var.is_none()
    }

    pub fn with(mut self, e: Effect) -> Self {
        self.effects.push(e);
        self
    }

    pub fn open(mut self, var: impl Into<String>) -> Self {
        self.row_var = Some(var.into());
        self
    }
}

/// A single algebraic / monadic effect.
///
/// `Pure` is the identity; `Custom` is the escape hatch for backend-specific
/// effects (e.g. F*'s `ST`, `Tot`, `GTot`, `Ghost`, `Div`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Effect {
    Pure,
    IO,
    State,
    Exception,
    NonDet,
    Async,
    Div,
    Ghost,
    Tot,
    Custom(String),
}

/// Modal operator.
///
/// Covers alethic (□ / ◇), epistemic (K_a, common / distributed knowledge),
/// doxastic (B_a), deontic (O / P / F), and provability logic.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Modality {
    /// Alethic necessity □.
    Box,
    /// Alethic possibility ◇.
    Diamond,
    /// Agent `a` knows φ (epistemic K_a).
    Knows(String),
    /// Agent `a` believes φ (doxastic B_a).
    Believes(String),
    /// Common knowledge among a group of agents.
    Common(Vec<String>),
    /// Distributed knowledge among a group of agents.
    Distributed(Vec<String>),
    /// Deontic obligation O.
    Obligation,
    /// Deontic permission P.
    Permission,
    /// Provability □_PA (GL / Löb).
    Provability,
    /// Escape hatch for exotic modalities (dynamic, action, …).
    Custom(String),
}

/// Temporal-logic operator (LTL / CTL / CTL\*).
///
/// Path-quantified variants `A*` and `E*` are CTL; unquantified variants are
/// LTL. `Since` / `Release` / `Triggered` are past-time operators.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TemporalOp {
    /// LTL `G` / □ — globally / always.
    Always,
    /// LTL `F` / ◇ — finally / eventually.
    Eventually,
    /// LTL `X` / ○ — next.
    Next,
    /// LTL `U` — until.
    Until,
    /// LTL `R` — release.
    Release,
    /// Past-time `S` — since.
    Since,
    /// Past-time `T` — triggered.
    Triggered,
    /// CTL `AG` — on all paths, globally.
    AG,
    /// CTL `EG` — on some path, globally.
    EG,
    /// CTL `AF` — on all paths, eventually.
    AF,
    /// CTL `EF` — on some path, eventually.
    EF,
    /// CTL `AX` — on all paths, next.
    AX,
    /// CTL `EX` — on some path, next.
    EX,
    /// μ-calculus least fixed point.
    Mu(String),
    /// μ-calculus greatest fixed point.
    Nu(String),
}

/// Underlying semiring for quantitative / tropical reasoning.
///
/// ECHIDNA's backends default to the Boolean semiring (classical truth). The
/// tropical semiring enables min-plus / max-plus algebra for shortest-path-
/// style optimization problems; Viterbi / Łukasiewicz unlock fuzzy and
/// probabilistic variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Semiring {
    /// Boolean semiring `(⊥ ⊤, ∨, ∧)` — classical truth.
    Boolean,
    /// Natural-number semiring `(0, 1, +, ·)` — counting.
    Natural,
    /// Tropical / min-plus `(∞, 0, min, +)` when `min = true`;
    /// max-plus `(-∞, 0, max, +)` when `min = false`.
    Tropical { min: bool },
    /// Viterbi `([0,1], 0, 1, max, ·)` — probabilistic best-path.
    Viterbi,
    /// Łukasiewicz fuzzy semiring.
    Lukasiewicz,
    /// Named custom semiring (provenance, security lattices, …).
    Custom(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Term;

    #[test]
    fn default_typeinfo_is_empty() {
        let t = TypeInfo::default();
        assert!(t.is_empty());
    }

    #[test]
    fn linear_multiplicity_attaches() {
        let t = TypeInfo::new().with_multiplicity(Multiplicity::Linear);
        assert_eq!(t.multiplicity, Some(Multiplicity::Linear));
        assert!(!t.is_empty());
    }

    #[test]
    fn effect_row_composition() {
        let row = EffectRow::default().with(Effect::IO).with(Effect::State);
        let t = TypeInfo::new().with_effects(row);
        assert_eq!(t.effects.effects.len(), 2);
        assert!(t.effects.row_var.is_none());
    }

    #[test]
    fn epistemic_modality() {
        let t = TypeInfo::new().with_modality(Modality::Knows("alice".into()));
        assert!(matches!(t.modality, Some(Modality::Knows(ref a)) if a == "alice"));
    }

    #[test]
    fn tropical_semiring() {
        let t = TypeInfo::new().with_semiring(Semiring::Tropical { min: true });
        assert_eq!(t.semiring, Some(Semiring::Tropical { min: true }));
    }

    #[test]
    fn refinement_predicate_stores_term() {
        let pred = Term::App {
            func: Box::new(Term::Const("positive".into())),
            args: vec![Term::Var("x".into())],
        };
        let t = TypeInfo::new().with_refinement(pred.clone());
        assert_eq!(t.refinement.as_deref(), Some(&pred));
    }

    #[test]
    fn hott_universe() {
        let u = Universe::hott(0, 2);
        assert_eq!(u.homotopy_level, Some(2));
    }

    #[test]
    fn dyadic_relational_arity() {
        let t = TypeInfo::new().with_relational_arity(2);
        assert_eq!(t.relational_arity, Some(2));
    }

    #[test]
    fn typeinfo_roundtrips_through_json() {
        let t = TypeInfo::new()
            .with_multiplicity(Multiplicity::Linear)
            .with_effects(EffectRow::default().with(Effect::IO))
            .with_modality(Modality::Knows("agent_a".into()))
            .with_temporal(TemporalOp::Always)
            .with_semiring(Semiring::Tropical { min: true })
            .with_relational_arity(2)
            .with_universe(Universe::hott(1, 1));
        let json = serde_json::to_string(&t).expect("serialize");
        let back: TypeInfo = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(t, back);
    }

    #[test]
    fn empty_typeinfo_serializes_compactly() {
        let t = TypeInfo::default();
        let json = serde_json::to_string(&t).unwrap();
        // all fields skipped when empty
        assert_eq!(json, "{}");
    }

    #[test]
    fn sigma_term_renders_and_roundtrips() {
        let sigma = Term::Sigma {
            param: "x".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::App {
                func: Box::new(Term::Const("positive".to_string())),
                args: vec![Term::Var("x".to_string())],
            }),
        };
        assert_eq!(format!("{}", sigma), "(Σ x: Nat. (positive x))");
        let json = serde_json::to_string(&sigma).expect("serialize");
        let back: Term = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(sigma, back);
    }

    #[test]
    fn hypothesis_with_type_info_roundtrips() {
        use crate::core::Hypothesis;
        let h = Hypothesis { name: "h".into(), ty: Term::Const("Nat".to_string()), body: None, type_info: Some(TypeInfo::new().with_multiplicity(Multiplicity::Linear)) };
        let json = serde_json::to_string(&h).expect("serialize");
        assert!(json.contains("Linear"));
        let back: Hypothesis = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(
            back.type_info.and_then(|t| t.multiplicity),
            Some(Multiplicity::Linear)
        );
    }

    #[test]
    fn plain_hypothesis_deserializes_without_type_info_field() {
        use crate::core::Hypothesis;
        // Prior-format JSON (no type_info field) must still parse.
        let json = r#"{"name":"h","ty":{"Const":"Nat"},"body":null}"#;
        let h: Hypothesis = serde_json::from_str(json).expect("deserialize");
        assert_eq!(h.name, "h");
        assert!(h.type_info.is_none());
    }
}
