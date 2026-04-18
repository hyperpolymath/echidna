// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Type-discipline taxonomy — **Axis 2** of echidna's prover classification.
//!
//! # Two orthogonal axes
//!
//! Echidna classifies proving tools along two independent axes:
//!
//! * **Axis 1 — `ProverKind`** in `src/rust/provers/mod.rs`. The thing
//!   people type into a search box: *Agda*, *Coq*, *Lean 4*, *Z3*, *CVC5*,
//!   *Isabelle*, *HOL Light*, *Idris2*, *F\**, … Real binaries with
//!   websites, papers, and communities of practice.
//! * **Axis 2 — `TypeDiscipline`** (this module). The thing the prover is
//!   *applied to*: dependent types, linear types, modal logic, session
//!   types, tropical resource typing, homotopy type theory, algebraic
//!   effects, … The semantic shape of the reasoning problem.
//!
//! Both axes must be first-class. A user arriving from "Agda" wants to see
//! that Agda serves the dependent, indexed, higher-kinded, cubical, and
//! homotopy disciplines. A user arriving from "linear types" wants to see
//! that Idris2 (via QTT) and the HP-ecosystem `LinearTypeChecker` can
//! serve it. Cross-links in both directions: discipline → provers via
//! [`TypeDiscipline::provers_serving`]; prover → disciplines via the
//! convention that `ProverKind::*TypeChecker` is the HP dispatch route and
//! classical provers have their discipline coverage listed in the mapping
//! below.
//!
//! # Relationship to katagoria
//!
//! This module is the downstream target for `developer-ecosystem/katagoria/`.
//! When katagoria graduates a new level in its type-theory pipeline
//! (`katagoria → typell → typed-wasm → PanLL`), the corresponding variant
//! is expected to already exist here.
//!
//! # Design notes
//!
//! The enum is deliberately exhaustive up-front. Opening it again is
//! expensive: `ProverKind::*TypeChecker` is referenced in six exhaustive
//! match arms in `src/rust/provers/mod.rs` plus the HP-ecosystem dispatch
//! table. Every variant here has an immediate 1:1 mapping to a
//! `ProverKind::*TypeChecker` via [`TypeDiscipline::prover_kind`] — adding
//! a discipline means adding both.
//!
//! Phase 1 (the transition landed 2026-04-17) keeps wiring at the dispatch
//! level only — each discipline routes to `typell --discipline=<tag>` (or
//! the two named upstreams for `Tropical` / `Katagoria`). Phase 2 followups
//! (see `AI-WORK-todo.md`) deepen the support: per-discipline proof
//! encoding, Idris2 validator tagging, family-aware GNN features,
//! discipline-tagged corpus fixtures.
//!
//! # Family grouping
//!
//! Disciplines are grouped into families that share proof-theoretic
//! structure and dispatch heuristics. The `DisciplineFamily` tag is used
//! by the dispatcher to pick siblings as fallbacks (e.g. if `Linear` is
//! unavailable, fall back to the umbrella `Qtt`; if `Epistemic` is
//! unavailable, fall back to the umbrella `Modal`).

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

use crate::provers::ProverKind;

/// Canonical enumeration of every type discipline echidna routes through the
/// HP ecosystem. One variant per `ProverKind::*TypeChecker`.
///
/// Order is stable; inserting a new variant should always append, never
/// re-order, because downstream consumers serialise by discriminant.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub enum TypeDiscipline {
    // Entry points / kernels.
    TypeLl,
    Katagoria,
    // Foundations.
    Ordinary,
    // Polymorphism family.
    Phantom,
    Polymorphic,
    Existential,
    HigherKinded,
    Row,
    // Subtyping family.
    Subtyping,
    Intersection,
    Union,
    Gradual,
    // Dependent / refinement family.
    Dependent,
    Refinement,
    Hoare,
    Indexed,
    // Substructural family.
    Qtt,
    Linear,
    Affine,
    Relevant,
    Ordered,
    Uniqueness,
    // Mutability / capability family.
    Immutable,
    Capability,
    Bunched,
    // Modal family.
    Modal,
    Epistemic,
    Temporal,
    Provability,
    // Effects / coeffects family.
    EffectRow,
    Impure,
    Coeffect,
    Probabilistic,
    // Process / communication family.
    Session,
    Choreographic,
    Dyadic,
    Echo,
    // Resource semirings.
    Tropical,
    // Homotopy foundations.
    Homotopy,
    Cubical,
}

/// High-level family grouping. Disciplines in the same family share
/// proof-theoretic structure and should share GNN features.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DisciplineFamily {
    /// `TypeLl`, `Katagoria` — meta / kernel entry points.
    EntryPoint,
    /// `Ordinary` — simply-typed lambda calculus baseline.
    Foundation,
    /// Polymorphism: parametric, phantom, existential, HKT, row.
    Polymorphism,
    /// Subtyping, intersection, union, gradual.
    Subtyping,
    /// Dependent types, refinement, Hoare, indexed.
    DependentRefinement,
    /// Substructural resource-sensitive: QTT umbrella + linear/affine/
    /// relevant/ordered/uniqueness siblings.
    Substructural,
    /// Mutability / capability / separation (including bunched).
    MutabilityCapability,
    /// Modal logic: box/diamond, epistemic, temporal, provability.
    Modal,
    /// Effects and coeffects: algebraic effects, impure, coeffect,
    /// probabilistic.
    EffectsCoeffects,
    /// Process / communication: session, choreographic, dyadic, echo.
    Process,
    /// Resource semirings (tropical, min-plus / max-plus).
    ResourceSemiring,
    /// Homotopy type theory and cubical type theory.
    Homotopy,
}

impl TypeDiscipline {
    /// Every discipline the echidna TypeDiscipline transition admits.
    /// Kept in sync with `ProverKind::is_hp_ecosystem`.
    pub const ALL: [TypeDiscipline; 40] = [
        TypeDiscipline::TypeLl,
        TypeDiscipline::Katagoria,
        TypeDiscipline::Ordinary,
        TypeDiscipline::Phantom,
        TypeDiscipline::Polymorphic,
        TypeDiscipline::Existential,
        TypeDiscipline::HigherKinded,
        TypeDiscipline::Row,
        TypeDiscipline::Subtyping,
        TypeDiscipline::Intersection,
        TypeDiscipline::Union,
        TypeDiscipline::Gradual,
        TypeDiscipline::Dependent,
        TypeDiscipline::Refinement,
        TypeDiscipline::Hoare,
        TypeDiscipline::Indexed,
        TypeDiscipline::Qtt,
        TypeDiscipline::Linear,
        TypeDiscipline::Affine,
        TypeDiscipline::Relevant,
        TypeDiscipline::Ordered,
        TypeDiscipline::Uniqueness,
        TypeDiscipline::Immutable,
        TypeDiscipline::Capability,
        TypeDiscipline::Bunched,
        TypeDiscipline::Modal,
        TypeDiscipline::Epistemic,
        TypeDiscipline::Temporal,
        TypeDiscipline::Provability,
        TypeDiscipline::EffectRow,
        TypeDiscipline::Impure,
        TypeDiscipline::Coeffect,
        TypeDiscipline::Probabilistic,
        TypeDiscipline::Session,
        TypeDiscipline::Choreographic,
        TypeDiscipline::Dyadic,
        TypeDiscipline::Echo,
        TypeDiscipline::Tropical,
        TypeDiscipline::Homotopy,
        TypeDiscipline::Cubical,
    ];

    /// Which family this discipline belongs to.
    pub fn family(self) -> DisciplineFamily {
        use DisciplineFamily::*;
        use TypeDiscipline as D;
        match self {
            D::TypeLl | D::Katagoria => EntryPoint,
            D::Ordinary => Foundation,
            D::Phantom | D::Polymorphic | D::Existential | D::HigherKinded | D::Row => {
                Polymorphism
            }
            D::Subtyping | D::Intersection | D::Union | D::Gradual => Subtyping,
            D::Dependent | D::Refinement | D::Hoare | D::Indexed => DependentRefinement,
            D::Qtt | D::Linear | D::Affine | D::Relevant | D::Ordered | D::Uniqueness => {
                Substructural
            }
            D::Immutable | D::Capability | D::Bunched => MutabilityCapability,
            D::Modal | D::Epistemic | D::Temporal | D::Provability => Modal,
            D::EffectRow | D::Impure | D::Coeffect | D::Probabilistic => EffectsCoeffects,
            D::Session | D::Choreographic | D::Dyadic | D::Echo => Process,
            D::Tropical => ResourceSemiring,
            D::Homotopy | D::Cubical => Homotopy,
        }
    }

    /// The canonical discipline tag passed to `typell --discipline=<tag>`
    /// (or the name of the distinct upstream CLI for `Tropical` /
    /// `Katagoria`). Must match `HPEcosystemBackend::upstream()`.
    pub fn tag(self) -> &'static str {
        use TypeDiscipline as D;
        match self {
            D::TypeLl => "typell",
            D::Katagoria => "verify",
            D::Tropical => "tropical",
            D::Ordinary => "ordinary",
            D::Phantom => "phantom",
            D::Polymorphic => "polymorphic",
            D::Existential => "existential",
            D::HigherKinded => "higher-kinded",
            D::Row => "row",
            D::Subtyping => "subtyping",
            D::Intersection => "intersection",
            D::Union => "union",
            D::Gradual => "gradual",
            D::Dependent => "dependent",
            D::Refinement => "refinement",
            D::Hoare => "hoare",
            D::Indexed => "indexed",
            D::Qtt => "qtt",
            D::Linear => "linear",
            D::Affine => "affine",
            D::Relevant => "relevant",
            D::Ordered => "ordered",
            D::Uniqueness => "uniqueness",
            D::Immutable => "immutable",
            D::Capability => "capability",
            D::Bunched => "bunched",
            D::Modal => "modal",
            D::Epistemic => "epistemic",
            D::Temporal => "temporal",
            D::Provability => "provability",
            D::EffectRow => "effect-row",
            D::Impure => "impure",
            D::Coeffect => "coeffect",
            D::Probabilistic => "probabilistic",
            D::Session => "session",
            D::Choreographic => "choreographic",
            D::Dyadic => "dyadic",
            D::Echo => "echo",
            D::Homotopy => "homotopy",
            D::Cubical => "cubical",
        }
    }

    /// Umbrella discipline that subsumes this one, if any. Used by the
    /// dispatcher when the specific discipline is unavailable. For example,
    /// `Linear → Qtt` (linear is QTT with multiplicity 1); `Epistemic →
    /// Modal`; `Choreographic → Session`.
    pub fn umbrella(self) -> Option<TypeDiscipline> {
        use TypeDiscipline as D;
        match self {
            // Substructural siblings fall back to the QTT umbrella.
            D::Linear | D::Affine | D::Relevant | D::Ordered | D::Uniqueness => Some(D::Qtt),
            // Modal siblings fall back to generic Modal.
            D::Epistemic | D::Temporal | D::Provability => Some(D::Modal),
            // Effect siblings fall back to EffectRow.
            D::Impure | D::Coeffect | D::Probabilistic => Some(D::EffectRow),
            // Process siblings: Choreographic/Dyadic/Echo are richer than
            // plain binary Session; fall back to Session.
            D::Choreographic | D::Dyadic | D::Echo => Some(D::Session),
            // Refinement/Hoare/Indexed all reduce to Dependent when the
            // refinement/predicate/index machinery is unavailable.
            D::Refinement | D::Hoare | D::Indexed => Some(D::Dependent),
            // Polymorphism siblings fall back to Polymorphic.
            D::Phantom | D::Existential | D::HigherKinded | D::Row => Some(D::Polymorphic),
            // Subtyping refinements fall back to generic Subtyping.
            D::Intersection | D::Union | D::Gradual => Some(D::Subtyping),
            // Cubical is a model of Homotopy.
            D::Cubical => Some(D::Homotopy),
            // Capability/Bunched refine Immutable's concern (aliasing).
            D::Capability | D::Bunched => Some(D::Immutable),
            // Kernels / umbrellas have no fallback.
            D::TypeLl
            | D::Katagoria
            | D::Ordinary
            | D::Polymorphic
            | D::Subtyping
            | D::Dependent
            | D::Qtt
            | D::Immutable
            | D::Modal
            | D::EffectRow
            | D::Session
            | D::Tropical
            | D::Homotopy => None,
        }
    }

    /// The `ProverKind` that backs this discipline. Every variant has one.
    pub fn prover_kind(self) -> ProverKind {
        use ProverKind as P;
        use TypeDiscipline as D;
        match self {
            D::TypeLl => P::TypeLL,
            D::Katagoria => P::KatagoriaVerifier,
            D::Tropical => P::TropicalTypeChecker,
            D::Choreographic => P::ChoreographicTypeChecker,
            D::Epistemic => P::EpistemicTypeChecker,
            D::Echo => P::EchoTypeChecker,
            D::Session => P::SessionTypeChecker,
            D::Modal => P::ModalTypeChecker,
            D::Qtt => P::QTTTypeChecker,
            D::EffectRow => P::EffectRowTypeChecker,
            D::Dependent => P::DependentTypeChecker,
            D::Refinement => P::RefinementTypeChecker,
            D::Ordinary => P::OrdinaryTypeChecker,
            D::Phantom => P::PhantomTypeChecker,
            D::Polymorphic => P::PolymorphicTypeChecker,
            D::Existential => P::ExistentialTypeChecker,
            D::HigherKinded => P::HigherKindedTypeChecker,
            D::Row => P::RowTypeChecker,
            D::Subtyping => P::SubtypingTypeChecker,
            D::Intersection => P::IntersectionTypeChecker,
            D::Union => P::UnionTypeChecker,
            D::Gradual => P::GradualTypeChecker,
            D::Hoare => P::HoareTypeChecker,
            D::Indexed => P::IndexedTypeChecker,
            D::Linear => P::LinearTypeChecker,
            D::Affine => P::AffineTypeChecker,
            D::Relevant => P::RelevantTypeChecker,
            D::Ordered => P::OrderedTypeChecker,
            D::Uniqueness => P::UniquenessTypeChecker,
            D::Immutable => P::ImmutableTypeChecker,
            D::Capability => P::CapabilityTypeChecker,
            D::Bunched => P::BunchedTypeChecker,
            D::Temporal => P::TemporalTypeChecker,
            D::Provability => P::ProvabilityTypeChecker,
            D::Impure => P::ImpureTypeChecker,
            D::Coeffect => P::CoeffectTypeChecker,
            D::Probabilistic => P::ProbabilisticTypeChecker,
            D::Dyadic => P::DyadicTypeChecker,
            D::Homotopy => P::HomotopyTypeChecker,
            D::Cubical => P::CubicalTypeChecker,
        }
    }

    /// Which **classical** (Axis-1) provers can natively serve this
    /// discipline, beyond the HP-ecosystem dispatch route.
    ///
    /// Returned kinds are the real binaries a user would reach for if they
    /// searched for this discipline by name — Agda for dependent types, NuSMV
    /// for temporal logic, Viper for separation, and so on. The HP-ecosystem
    /// dispatcher (available through [`prover_kind`]) is always a valid route
    /// and is intentionally *not* listed here — this helper exists to power
    /// Axis-1-first discovery.
    ///
    /// An empty `Vec` means no classical prover in echidna's current lineup
    /// has mainstream coverage of the discipline; the HP dispatcher is the
    /// only known route. That is not a judgement on the discipline's
    /// importance — several communication-style disciplines (Session,
    /// Choreographic, Echo, Dyadic) live entirely in the research-prototype
    /// world that the HP stack is specifically here to serve.
    ///
    /// Conservative by construction: a prover is only listed when its
    /// mainstream documentation explicitly advertises the discipline, or
    /// when a widely-used published encoding exists. Extend carefully;
    /// spurious entries mislead users worse than empty lists.
    pub fn provers_serving(self) -> Vec<ProverKind> {
        use ProverKind as P;
        use TypeDiscipline as D;
        match self {
            // Foundation — simply-typed lambda calculus. Everyone who
            // supports anything supports this; listing the proof assistants
            // that have explicit STLC tutorials.
            D::Ordinary => {
                vec![P::Agda, P::Coq, P::Lean, P::Isabelle, P::Idris2, P::FStar]
            }

            // Polymorphism family.
            D::Polymorphic => vec![
                P::Agda,
                P::Coq,
                P::Lean,
                P::Isabelle,
                P::Idris2,
                P::FStar,
                P::HOL4,
                P::HOLLight,
                P::PVS,
            ],
            D::Existential => vec![P::Agda, P::Coq, P::Lean, P::Idris2, P::FStar],
            D::HigherKinded => vec![P::Agda, P::Coq, P::Lean, P::Idris2, P::FStar],
            D::Row => vec![], // Koka-native; none in echidna's classical lineup.
            D::Phantom => vec![
                P::Agda, P::Coq, P::Lean, P::Idris2, P::FStar, P::Dafny,
            ],

            // Subtyping family.
            D::Subtyping => vec![P::FStar, P::Dafny],
            D::Intersection => vec![], // Flow / Typed Racket territory; none classical.
            D::Union => vec![P::FStar, P::Dafny],
            D::Gradual => vec![], // Grift / Reticulated Python; none in echidna.

            // Dependent / refinement family.
            D::Dependent => vec![P::Agda, P::Coq, P::Lean, P::Idris2, P::FStar, P::PVS],
            // LiquidHaskell is the canonical refinement-type home but is
            // not in echidna's classical lineup, so it's intentionally
            // absent here.
            D::Refinement => vec![P::FStar, P::Dafny, P::Why3],
            D::Hoare => vec![P::Dafny, P::Viper, P::FramaC, P::KeY, P::Why3],
            D::Indexed => vec![P::Agda, P::Coq, P::Idris2],

            // Substructural family. Mainstream support is thin; Idris2 via
            // QTT is the canonical route for Linear/Affine, the rest are
            // research-prototype (routed through the HP dispatcher).
            D::Qtt => vec![P::Idris2],
            D::Linear => vec![P::Idris2],
            D::Affine => vec![P::Idris2],
            D::Relevant => vec![],
            D::Ordered => vec![],
            D::Uniqueness => vec![], // Clean is canonical but not in echidna.

            // Mutability / capability.
            D::Immutable => vec![P::Dafny, P::Viper, P::FramaC, P::KeY],
            D::Capability => vec![P::Viper],
            D::Bunched => vec![P::Viper], // Separation-logic flavoured.

            // Modal family.
            D::Modal => vec![P::Isabelle], // Isabelle/ModalHOL + other instances.
            D::Epistemic => vec![], // DEL / S5 tooling lives outside echidna's current lineup.
            D::Temporal => vec![
                P::NuSMV, P::TLC, P::SPIN, P::UPPAAL, P::Prism, P::TLAPS,
            ],
            D::Provability => vec![], // GL logic, mostly research.

            // Effects / coeffects.
            D::EffectRow => vec![P::FStar], // F* effect algebras.
            D::Impure => vec![P::FStar, P::Dafny], // Stateful-program verifiers.
            D::Coeffect => vec![], // Granule; not in echidna.
            D::Probabilistic => vec![P::Prism, P::DReal],

            // Process / communication — the HP stack is specifically here
            // to serve these. No classical prover in echidna advertises
            // first-class session / choreographic / echo / dyadic typing.
            D::Session => vec![],
            D::Choreographic => vec![],
            D::Dyadic => vec![],
            D::Echo => vec![],

            // Resource semirings — Tropical is an HP-stack specialty.
            D::Tropical => vec![],

            // Homotopy foundations.
            D::Homotopy => vec![P::Agda, P::Lean], // HoTT libraries on both.
            D::Cubical => vec![P::Agda], // Cubical Agda is the canonical home.

            // Entry-point kernels: these are the HP gateways themselves;
            // they don't correspond to a classical prover in the Axis-1
            // sense.
            D::TypeLl | D::Katagoria => vec![],
        }
    }

    /// Inverse of [`prover_kind`]. Returns `None` for non-HP-ecosystem kinds.
    pub fn from_prover_kind(kind: ProverKind) -> Option<TypeDiscipline> {
        use ProverKind as P;
        use TypeDiscipline as D;
        Some(match kind {
            P::TypeLL => D::TypeLl,
            P::KatagoriaVerifier => D::Katagoria,
            P::TropicalTypeChecker => D::Tropical,
            P::ChoreographicTypeChecker => D::Choreographic,
            P::EpistemicTypeChecker => D::Epistemic,
            P::EchoTypeChecker => D::Echo,
            P::SessionTypeChecker => D::Session,
            P::ModalTypeChecker => D::Modal,
            P::QTTTypeChecker => D::Qtt,
            P::EffectRowTypeChecker => D::EffectRow,
            P::DependentTypeChecker => D::Dependent,
            P::RefinementTypeChecker => D::Refinement,
            P::OrdinaryTypeChecker => D::Ordinary,
            P::PhantomTypeChecker => D::Phantom,
            P::PolymorphicTypeChecker => D::Polymorphic,
            P::ExistentialTypeChecker => D::Existential,
            P::HigherKindedTypeChecker => D::HigherKinded,
            P::RowTypeChecker => D::Row,
            P::SubtypingTypeChecker => D::Subtyping,
            P::IntersectionTypeChecker => D::Intersection,
            P::UnionTypeChecker => D::Union,
            P::GradualTypeChecker => D::Gradual,
            P::HoareTypeChecker => D::Hoare,
            P::IndexedTypeChecker => D::Indexed,
            P::LinearTypeChecker => D::Linear,
            P::AffineTypeChecker => D::Affine,
            P::RelevantTypeChecker => D::Relevant,
            P::OrderedTypeChecker => D::Ordered,
            P::UniquenessTypeChecker => D::Uniqueness,
            P::ImmutableTypeChecker => D::Immutable,
            P::CapabilityTypeChecker => D::Capability,
            P::BunchedTypeChecker => D::Bunched,
            P::TemporalTypeChecker => D::Temporal,
            P::ProvabilityTypeChecker => D::Provability,
            P::ImpureTypeChecker => D::Impure,
            P::CoeffectTypeChecker => D::Coeffect,
            P::ProbabilisticTypeChecker => D::Probabilistic,
            P::DyadicTypeChecker => D::Dyadic,
            P::HomotopyTypeChecker => D::Homotopy,
            P::CubicalTypeChecker => D::Cubical,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_has_expected_size() {
        assert_eq!(TypeDiscipline::ALL.len(), 40);
    }

    #[test]
    fn all_is_deduplicated() {
        let mut sorted: Vec<TypeDiscipline> = TypeDiscipline::ALL.to_vec();
        sorted.sort();
        let before = sorted.len();
        sorted.dedup();
        assert_eq!(before, sorted.len(), "TypeDiscipline::ALL has duplicates");
    }

    #[test]
    fn tags_are_unique() {
        let mut tags: Vec<&'static str> =
            TypeDiscipline::ALL.iter().map(|d| d.tag()).collect();
        tags.sort_unstable();
        let before = tags.len();
        tags.dedup();
        assert_eq!(before, tags.len(), "duplicate discipline tag detected");
    }

    #[test]
    fn prover_kind_roundtrip() {
        for &d in TypeDiscipline::ALL.iter() {
            let back = TypeDiscipline::from_prover_kind(d.prover_kind())
                .unwrap_or_else(|| panic!("no discipline for prover_kind {:?}", d));
            assert_eq!(back, d, "roundtrip failed for {:?}", d);
        }
    }

    #[test]
    fn non_hp_kind_returns_none() {
        assert!(TypeDiscipline::from_prover_kind(ProverKind::Agda).is_none());
        assert!(TypeDiscipline::from_prover_kind(ProverKind::Z3).is_none());
        assert!(TypeDiscipline::from_prover_kind(ProverKind::Coq).is_none());
    }

    #[test]
    fn every_hp_kind_has_a_discipline() {
        // Cross-check: every ProverKind flagged is_hp_ecosystem must have a
        // TypeDiscipline. This is the invariant that makes adding a new
        // variant a single-source-of-truth change.
        use crate::provers::ProverKind;
        let all_hp: Vec<ProverKind> = vec![
            ProverKind::TypeLL,
            ProverKind::KatagoriaVerifier,
            ProverKind::TropicalTypeChecker,
            ProverKind::ChoreographicTypeChecker,
            ProverKind::EpistemicTypeChecker,
            ProverKind::EchoTypeChecker,
            ProverKind::SessionTypeChecker,
            ProverKind::ModalTypeChecker,
            ProverKind::QTTTypeChecker,
            ProverKind::EffectRowTypeChecker,
            ProverKind::DependentTypeChecker,
            ProverKind::RefinementTypeChecker,
            ProverKind::OrdinaryTypeChecker,
            ProverKind::PhantomTypeChecker,
            ProverKind::PolymorphicTypeChecker,
            ProverKind::ExistentialTypeChecker,
            ProverKind::HigherKindedTypeChecker,
            ProverKind::RowTypeChecker,
            ProverKind::SubtypingTypeChecker,
            ProverKind::IntersectionTypeChecker,
            ProverKind::UnionTypeChecker,
            ProverKind::GradualTypeChecker,
            ProverKind::HoareTypeChecker,
            ProverKind::IndexedTypeChecker,
            ProverKind::LinearTypeChecker,
            ProverKind::AffineTypeChecker,
            ProverKind::RelevantTypeChecker,
            ProverKind::OrderedTypeChecker,
            ProverKind::UniquenessTypeChecker,
            ProverKind::ImmutableTypeChecker,
            ProverKind::CapabilityTypeChecker,
            ProverKind::BunchedTypeChecker,
            ProverKind::TemporalTypeChecker,
            ProverKind::ProvabilityTypeChecker,
            ProverKind::ImpureTypeChecker,
            ProverKind::CoeffectTypeChecker,
            ProverKind::ProbabilisticTypeChecker,
            ProverKind::DyadicTypeChecker,
            ProverKind::HomotopyTypeChecker,
            ProverKind::CubicalTypeChecker,
        ];
        assert_eq!(all_hp.len(), 40);
        for k in all_hp {
            assert!(k.is_hp_ecosystem(), "{:?} should be hp_ecosystem", k);
            assert!(
                TypeDiscipline::from_prover_kind(k).is_some(),
                "{:?} has no TypeDiscipline mapping",
                k
            );
        }
    }

    #[test]
    fn umbrella_never_cycles() {
        // Walking the umbrella chain from any discipline must terminate.
        for &d in TypeDiscipline::ALL.iter() {
            let mut steps = 0;
            let mut current = d;
            while let Some(up) = current.umbrella() {
                current = up;
                steps += 1;
                assert!(steps < 16, "umbrella chain too deep from {:?}", d);
            }
        }
    }

    #[test]
    fn provers_serving_only_lists_classical_kinds() {
        // Axis-1-first discovery: `provers_serving` must never list
        // the HP-ecosystem dispatcher (which is already reachable via
        // `prover_kind`). Otherwise a user arriving via "which prover
        // serves linear types?" sees `LinearTypeChecker` in the list
        // and is no better off than when they started.
        for &d in TypeDiscipline::ALL.iter() {
            for kind in d.provers_serving() {
                assert!(
                    !kind.is_hp_ecosystem(),
                    "{:?} lists HP-ecosystem kind {:?} in provers_serving; should be classical only",
                    d,
                    kind
                );
            }
        }
    }

    #[test]
    fn provers_serving_is_deduplicated() {
        for &d in TypeDiscipline::ALL.iter() {
            let list = d.provers_serving();
            let mut sorted: Vec<ProverKind> = list.clone();
            sorted.sort_by_key(|k| format!("{:?}", k));
            let before = sorted.len();
            sorted.dedup();
            assert_eq!(
                before,
                sorted.len(),
                "{:?} has duplicates in provers_serving: {:?}",
                d,
                list
            );
        }
    }

    #[test]
    fn provers_serving_canonical_spot_checks() {
        // Ground-truth spot checks anchored in mainstream usage.
        // Breaking these should be a deliberate taxonomy decision.
        use TypeDiscipline as D;

        let dep = D::Dependent.provers_serving();
        assert!(dep.contains(&ProverKind::Agda));
        assert!(dep.contains(&ProverKind::Coq));
        assert!(dep.contains(&ProverKind::Lean));
        assert!(dep.contains(&ProverKind::Idris2));

        let linear = D::Linear.provers_serving();
        assert!(linear.contains(&ProverKind::Idris2)); // QTT.

        let cubical = D::Cubical.provers_serving();
        assert!(cubical.contains(&ProverKind::Agda)); // Cubical Agda.

        let temporal = D::Temporal.provers_serving();
        assert!(temporal.contains(&ProverKind::NuSMV));
        assert!(temporal.contains(&ProverKind::SPIN));
        assert!(temporal.contains(&ProverKind::TLC));

        let hoare = D::Hoare.provers_serving();
        assert!(hoare.contains(&ProverKind::Dafny));
        assert!(hoare.contains(&ProverKind::Viper));
        assert!(hoare.contains(&ProverKind::KeY));

        // Communication-style disciplines: HP stack is their home.
        assert!(D::Session.provers_serving().is_empty());
        assert!(D::Choreographic.provers_serving().is_empty());
        assert!(D::Dyadic.provers_serving().is_empty());
        assert!(D::Echo.provers_serving().is_empty());

        // Entry-point kernels don't have a classical counterpart.
        assert!(D::TypeLl.provers_serving().is_empty());
        assert!(D::Katagoria.provers_serving().is_empty());
    }

    #[test]
    fn tag_matches_hp_ecosystem_upstream() {
        // Sanity: TypeDiscipline::tag() must agree with the string passed
        // to `typell --discipline=<tag>` in `HPEcosystemBackend::upstream()`.
        // We only spot-check a handful here — the exhaustive check is in
        // `hp_ecosystem::tests::all_discipline_kinds_are_hp`.
        assert_eq!(TypeDiscipline::Linear.tag(), "linear");
        assert_eq!(TypeDiscipline::Cubical.tag(), "cubical");
        assert_eq!(TypeDiscipline::Phantom.tag(), "phantom");
        assert_eq!(TypeDiscipline::EffectRow.tag(), "effect-row");
        assert_eq!(TypeDiscipline::HigherKinded.tag(), "higher-kinded");
    }
}
