// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Canonical type-discipline taxonomy for echidna.
//!
//! This module is the single source of truth for every type discipline that
//! echidna can route, encode, validate, or reason about. It is the downstream
//! target for `developer-ecosystem/katagoria/` — when katagoria graduates a
//! new level in its type-theory pipeline (`katagoria → typell → typed-wasm
//! → PanLL`), the corresponding variant should already exist here.
//!
//! # Design
//!
//! The enum is deliberately exhaustive up-front. Opening it again is
//! expensive: `ProverKind::*TypeChecker` is referenced in six exhaustive
//! match arms in `src/rust/provers/mod.rs` plus the HP-ecosystem dispatch
//! table. Every variant added here has an immediate 1:1 mapping to a
//! `ProverKind::*TypeChecker` — adding a discipline means adding both.
//!
//! Phase 1 (this transition) keeps wiring at the dispatch level only — each
//! discipline routes to `typell --discipline=<tag>` (or the two named
//! upstreams for `Tropical` / `Katagoria`). Phase 2 followups (see
//! `AI-WORK-todo.md`) deepen the support: per-discipline proof encoding,
//! Idris2 validator tagging, family-aware GNN features, discipline-tagged
//! corpus fixtures.
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
