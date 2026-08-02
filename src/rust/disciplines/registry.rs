// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Discipline marker registry for the corpus-side detector.
//!
//! See `docs/architecture/TYPE-DISCIPLINE-EMBEDDING.md` for the
//! theoretical background. The registry is read-only and seeded by
//! [`MarkerRegistry::canonical`] — no runtime mutation expected.
//!
//! # Confidence model
//!
//! Each marker carries a per-marker confidence in `[0.0, 1.0]`. The
//! detector sums confidences across all markers that match a haystack
//! and flags any discipline whose total reaches `0.7`. Very strong
//! markers (textual identifier of the discipline itself: `"linear"`,
//! `"ceremonial"`, `"choreographic"`) carry `0.8` and singlehandedly
//! trip the flag. Weaker corroborating markers (sigils, operator
//! glyphs, qualifier prefixes) carry `0.25 – 0.5` and require a
//! companion hit to cross the threshold. This keeps the false-positive
//! rate down on adapters that share punctuation with unrelated tooling
//! (e.g. `!` in Rust-the-language is not a linear-types marker).
//!
//! # Adapter scoping
//!
//! When a marker is unambiguous for a single adapter (e.g. `"@1"` in
//! `affinescript` source), the `adapters` slice pins the marker to
//! that adapter. The empty slice means the marker is adapter-agnostic
//! and will run against every adapter.

use super::TypeDiscipline;
use std::collections::HashMap;

/// A textual marker that signals the presence of a discipline.
#[derive(Debug, Clone)]
pub struct DisciplineMarker {
    pub discipline: TypeDiscipline,
    pub token: &'static str,
    /// Adapter names this marker applies to (empty = all adapters).
    pub adapters: &'static [&'static str],
    /// `0.0..=1.0` marker confidence; sum across markers must reach
    /// `0.7` to flag.
    pub confidence: f32,
}

/// Read-only catalogue of marker tokens per discipline.
pub struct MarkerRegistry {
    by_discipline: HashMap<TypeDiscipline, Vec<DisciplineMarker>>,
}

impl MarkerRegistry {
    /// Build the canonical seeded registry. Every variant in
    /// [`TypeDiscipline::ALL`] has at least three markers.
    pub fn canonical() -> Self {
        let entries: &[(TypeDiscipline, &str, &[&str], f32)] = &CANONICAL_MARKERS;
        let mut by_discipline: HashMap<TypeDiscipline, Vec<DisciplineMarker>> = HashMap::new();
        for &(discipline, token, adapters, confidence) in entries {
            by_discipline
                .entry(discipline)
                .or_default()
                .push(DisciplineMarker {
                    discipline,
                    token,
                    adapters,
                    confidence,
                });
        }
        MarkerRegistry { by_discipline }
    }

    /// All markers registered for a discipline (empty slice if none).
    pub fn markers_for(&self, d: TypeDiscipline) -> &[DisciplineMarker] {
        self.by_discipline
            .get(&d)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Flat iterator over every marker in the registry.
    pub fn all_markers(&self) -> impl Iterator<Item = &DisciplineMarker> {
        self.by_discipline.values().flat_map(|v| v.iter())
    }
}

/// Adapter-agnostic empty slice used for markers that apply everywhere.
const ANY: &[&str] = &[];

/// Canonical seed table. Three or more markers per discipline. Order
/// within a discipline is informational; the detector treats them as a
/// set. Confidence levels follow the rubric in the module-level docs.
#[rustfmt::skip]
const CANONICAL_MARKERS: [(TypeDiscipline, &str, &[&str], f32); 138] = [
    // --- Entry points / kernels ------------------------------------------
    (TypeDiscipline::TypeLl,        "typell",         ANY, 0.8),
    (TypeDiscipline::TypeLl,        "TypeLL",         ANY, 0.8),
    (TypeDiscipline::TypeLl,        "--discipline=",  ANY, 0.5),
    (TypeDiscipline::Katagoria,     "katagoria",      ANY, 0.8),
    (TypeDiscipline::Katagoria,     "Katagoria",      ANY, 0.8),
    (TypeDiscipline::Katagoria,     "kategoria",      ANY, 0.7),

    // --- Foundation ------------------------------------------------------
    (TypeDiscipline::Ordinary,      "STLC",           ANY, 0.8),
    (TypeDiscipline::Ordinary,      "simply-typed",   ANY, 0.7),
    (TypeDiscipline::Ordinary,      "Church",         ANY, 0.4),

    // --- Polymorphism family ---------------------------------------------
    (TypeDiscipline::Phantom,       "phantom",        ANY, 0.8),
    (TypeDiscipline::Phantom,       "PhantomData",    ANY, 0.7),
    (TypeDiscipline::Phantom,       "_phantom",       ANY, 0.4),
    (TypeDiscipline::Polymorphic,   "polymorphic",    ANY, 0.8),
    (TypeDiscipline::Polymorphic,   "forall ",        ANY, 0.5),
    (TypeDiscipline::Polymorphic,   "∀",              ANY, 0.5),
    (TypeDiscipline::Existential,   "existential",    ANY, 0.8),
    (TypeDiscipline::Existential,   "exists ",        ANY, 0.5),
    (TypeDiscipline::Existential,   "∃",              ANY, 0.5),
    (TypeDiscipline::HigherKinded,  "higher-kinded",  ANY, 0.8),
    (TypeDiscipline::HigherKinded,  "HKT",            ANY, 0.7),
    (TypeDiscipline::HigherKinded,  "kind *",         ANY, 0.4),
    (TypeDiscipline::Row,           "row-poly",       ANY, 0.8),
    (TypeDiscipline::Row,           "row polymorph",  ANY, 0.7),
    (TypeDiscipline::Row,           "..r ",           ANY, 0.3),

    // --- Subtyping family ------------------------------------------------
    (TypeDiscipline::Subtyping,     "subtyping",      ANY, 0.8),
    (TypeDiscipline::Subtyping,     "<:",             ANY, 0.5),
    (TypeDiscipline::Subtyping,     "subtype",        ANY, 0.5),
    (TypeDiscipline::Intersection,  "intersection",   ANY, 0.8),
    (TypeDiscipline::Intersection,  " & ",            ANY, 0.3),
    (TypeDiscipline::Intersection,  "&&-type",        ANY, 0.4),
    (TypeDiscipline::Union,         "union",          ANY, 0.7),
    (TypeDiscipline::Union,         " | ",            ANY, 0.3),
    (TypeDiscipline::Union,         "tagged union",   ANY, 0.6),
    (TypeDiscipline::Gradual,       "gradual",        ANY, 0.8),
    (TypeDiscipline::Gradual,       "?:",             ANY, 0.3),
    (TypeDiscipline::Gradual,       "Dyn",            ANY, 0.4),

    // --- Dependent / refinement family -----------------------------------
    (TypeDiscipline::Dependent,     "dependent",      ANY, 0.8),
    (TypeDiscipline::Dependent,     "Pi ",            ANY, 0.4),
    (TypeDiscipline::Dependent,     "Π",              ANY, 0.5),
    (TypeDiscipline::Dependent,     "Sigma ",         ANY, 0.4),
    (TypeDiscipline::Dependent,     "Σ",              ANY, 0.5),
    (TypeDiscipline::Dependent,     "Vec ",           ANY, 0.3),
    (TypeDiscipline::Refinement,    "refinement",     ANY, 0.8),
    (TypeDiscipline::Refinement,    "{x:",            ANY, 0.4),
    (TypeDiscipline::Refinement,    " | ",            &["fstar", "liquid"], 0.5),
    (TypeDiscipline::Refinement,    "≡",              ANY, 0.4),
    (TypeDiscipline::Refinement,    "Eq ",            ANY, 0.3),
    (TypeDiscipline::Hoare,         "hoare",          ANY, 0.8),
    (TypeDiscipline::Hoare,         "requires ",      ANY, 0.4),
    (TypeDiscipline::Hoare,         "ensures ",       ANY, 0.4),
    (TypeDiscipline::Hoare,         "{P} ",           ANY, 0.3),
    (TypeDiscipline::Indexed,       "indexed",        ANY, 0.8),
    (TypeDiscipline::Indexed,       "GADT",           ANY, 0.6),
    (TypeDiscipline::Indexed,       "Fin ",           ANY, 0.3),

    // --- Substructural family --------------------------------------------
    (TypeDiscipline::Qtt,           "QTT",            ANY, 0.8),
    (TypeDiscipline::Qtt,           "quantitative",   ANY, 0.7),
    (TypeDiscipline::Qtt,           "0 ",             &["idris2"], 0.3),
    (TypeDiscipline::Linear,        "linear",         ANY, 0.8),
    (TypeDiscipline::Linear,        "let!",           ANY, 0.6),
    (TypeDiscipline::Linear,        "⊸",              ANY, 0.7),
    (TypeDiscipline::Linear,        "Lin ",           ANY, 0.4),
    (TypeDiscipline::Linear,        "%1 ->",          ANY, 0.5),
    (TypeDiscipline::Affine,        "affine",         ANY, 0.8),
    (TypeDiscipline::Affine,        "@1",             ANY, 0.5),
    (TypeDiscipline::Affine,        "AffineScript",   ANY, 0.8),
    (TypeDiscipline::Affine,        ".affine",        ANY, 0.4),
    (TypeDiscipline::Relevant,      "relevant",       ANY, 0.8),
    (TypeDiscipline::Relevant,      "Rel ",           ANY, 0.3),
    (TypeDiscipline::Relevant,      "ω usage",        ANY, 0.5),
    (TypeDiscipline::Ordered,       "ordered",        ANY, 0.7),
    (TypeDiscipline::Ordered,       "non-commutative", ANY, 0.6),
    (TypeDiscipline::Ordered,       "Lambek",         ANY, 0.7),
    (TypeDiscipline::Uniqueness,    "uniqueness",     ANY, 0.8),
    (TypeDiscipline::Uniqueness,    "*World",         ANY, 0.5),
    (TypeDiscipline::Uniqueness,    "unique ",        ANY, 0.4),

    // --- Mutability / capability family ----------------------------------
    (TypeDiscipline::Immutable,     "immutable",      ANY, 0.8),
    (TypeDiscipline::Immutable,     "readonly",       ANY, 0.4),
    (TypeDiscipline::Immutable,     "const ",         ANY, 0.2),
    (TypeDiscipline::Capability,    "capability",     ANY, 0.8),
    (TypeDiscipline::Capability,    "ocap",           ANY, 0.6),
    (TypeDiscipline::Capability,    "@capability",    ANY, 0.7),
    (TypeDiscipline::Bunched,       "bunched",        ANY, 0.8),
    (TypeDiscipline::Bunched,       "separation",     ANY, 0.5),
    (TypeDiscipline::Bunched,       "*-conjunction",  ANY, 0.6),

    // --- Modal family ----------------------------------------------------
    (TypeDiscipline::Modal,         "modal",          ANY, 0.8),
    (TypeDiscipline::Modal,         "□",              ANY, 0.4),
    (TypeDiscipline::Modal,         "◇",              ANY, 0.4),
    (TypeDiscipline::Epistemic,     "epistemic",      ANY, 0.8),
    (TypeDiscipline::Epistemic,     "knows",          ANY, 0.5),
    (TypeDiscipline::Epistemic,     "K_i",            ANY, 0.6),
    (TypeDiscipline::Temporal,      "temporal",       ANY, 0.8),
    (TypeDiscipline::Temporal,      "always ",        ANY, 0.4),
    (TypeDiscipline::Temporal,      "eventually ",    ANY, 0.5),
    (TypeDiscipline::Provability,   "provability",    ANY, 0.8),
    (TypeDiscipline::Provability,   "GL logic",       ANY, 0.7),
    (TypeDiscipline::Provability,   "Bew(",           ANY, 0.5),

    // --- Effects / coeffects family --------------------------------------
    (TypeDiscipline::EffectRow,     "effect-row",     ANY, 0.8),
    (TypeDiscipline::EffectRow,     "algebraic effect", ANY, 0.7),
    (TypeDiscipline::EffectRow,     "handle ",        ANY, 0.4),
    (TypeDiscipline::Impure,        "impure",         ANY, 0.7),
    (TypeDiscipline::Impure,        "ST ",            ANY, 0.3),
    (TypeDiscipline::Impure,        "IO ",            ANY, 0.3),
    (TypeDiscipline::Coeffect,      "coeffect",       ANY, 0.8),
    (TypeDiscipline::Coeffect,      "Granule",        ANY, 0.7),
    (TypeDiscipline::Coeffect,      "[r]",            ANY, 0.3),
    (TypeDiscipline::Probabilistic, "probabilistic",  ANY, 0.8),
    (TypeDiscipline::Probabilistic, "sample ",        ANY, 0.4),
    (TypeDiscipline::Probabilistic, "Pr[",            ANY, 0.4),

    // --- Process / communication family ----------------------------------
    (TypeDiscipline::Session,       "session",        ANY, 0.8),
    (TypeDiscipline::Session,       "!T.",            ANY, 0.4),
    (TypeDiscipline::Session,       "?T.",            ANY, 0.4),
    (TypeDiscipline::Choreographic, "choreographic",  ANY, 0.8),
    (TypeDiscipline::Choreographic, "Choreo",         ANY, 0.7),
    (TypeDiscipline::Choreographic, "global ",        ANY, 0.3),
    (TypeDiscipline::Dyadic,        "dyadic",         ANY, 0.8),
    (TypeDiscipline::Dyadic,        "L→R",            ANY, 0.7),
    (TypeDiscipline::Dyadic,        "Echo.Dyadic",    ANY, 0.8),
    (TypeDiscipline::Echo,          "echo",           ANY, 0.7),
    (TypeDiscipline::Echo,          "echo-types",     ANY, 0.8),
    (TypeDiscipline::Echo,          "EchoType",       ANY, 0.7),

    // --- Resource semirings ----------------------------------------------
    (TypeDiscipline::Tropical,      "tropical",       ANY, 0.8),
    (TypeDiscipline::Tropical,      "min-plus",       ANY, 0.7),
    (TypeDiscipline::Tropical,      "⊕",              ANY, 0.4),
    (TypeDiscipline::Tropical,      "max-plus",       ANY, 0.7),

    // --- Homotopy foundations --------------------------------------------
    (TypeDiscipline::Homotopy,      "homotopy",       ANY, 0.8),
    (TypeDiscipline::Homotopy,      "HoTT",           ANY, 0.8),
    (TypeDiscipline::Homotopy,      "Univalence",     ANY, 0.7),
    (TypeDiscipline::Cubical,       "cubical",        ANY, 0.8),
    (TypeDiscipline::Cubical,       "PathP ",         ANY, 0.6),
    (TypeDiscipline::Cubical,       "interval I",     ANY, 0.5),

    // --- Nominal logic / HOAS --------------------------------------------
    (TypeDiscipline::Nominal,       "nominal",        ANY, 0.8),
    (TypeDiscipline::Nominal,       "fresh ",         ANY, 0.5),
    (TypeDiscipline::Nominal,       "∇",              ANY, 0.6),
    (TypeDiscipline::Nominal,       "HOAS",           ANY, 0.6),

    // --- Ceremonial / ritual / protocol-bound ----------------------------
    (TypeDiscipline::Ceremonial,    "ceremonial",     ANY, 0.8),
    (TypeDiscipline::Ceremonial,    "ritual",         ANY, 0.6),
    (TypeDiscipline::Ceremonial,    "@[ceremony]",    ANY, 0.8),
    (TypeDiscipline::Ceremonial,    "ceremony ",      ANY, 0.5),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_discipline_has_at_least_three_markers() {
        let registry = MarkerRegistry::canonical();
        for &d in TypeDiscipline::ALL.iter() {
            let markers = registry.markers_for(d);
            assert!(
                markers.len() >= 3,
                "{:?} has only {} markers; need ≥3",
                d,
                markers.len()
            );
        }
    }

    #[test]
    fn markers_for_linear_contains_linear() {
        let registry = MarkerRegistry::canonical();
        let markers = registry.markers_for(TypeDiscipline::Linear);
        assert!(
            markers.iter().any(|m| m.token == "linear"),
            "Linear must register the 'linear' token",
        );
    }

    #[test]
    fn markers_for_ceremonial_contains_ceremonial() {
        let registry = MarkerRegistry::canonical();
        let markers = registry.markers_for(TypeDiscipline::Ceremonial);
        assert!(
            markers.iter().any(|m| m.token == "ceremonial"),
            "Ceremonial must register the 'ceremonial' token",
        );
    }

    #[test]
    fn all_markers_iterator_matches_table_size() {
        let registry = MarkerRegistry::canonical();
        let count = registry.all_markers().count();
        assert_eq!(count, CANONICAL_MARKERS.len());
    }

    #[test]
    fn marker_confidence_is_in_unit_interval() {
        let registry = MarkerRegistry::canonical();
        for m in registry.all_markers() {
            assert!(
                (0.0..=1.0).contains(&m.confidence),
                "marker {:?} for {:?} has out-of-range confidence {}",
                m.token,
                m.discipline,
                m.confidence
            );
        }
    }
}
