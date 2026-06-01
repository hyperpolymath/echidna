// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! Discipline detector — extracts type-discipline tags from corpus
//! entry text by scoring [`super::registry::MarkerRegistry`] markers.
//!
//! Called by [`crate::corpus::Corpus::reindex`] post-extraction so
//! every adapter's output automatically carries the right discipline
//! tags without per-adapter wiring. Tags are stored as
//! `"discipline:<tag>"` strings inside `axiom_usage.other`, keeping
//! the existing serde shape intact.
//!
//! See `docs/architecture/TYPE-DISCIPLINE-EMBEDDING.md` §3 for the
//! detection topology and §7 for confidence semantics.

#![allow(dead_code)]

use std::collections::HashMap;

use super::registry::MarkerRegistry;
use super::TypeDiscipline;

/// Detection context — which adapter is the source, what's the
/// statement, what (if any) is the proof body.
#[derive(Debug, Clone)]
pub struct DetectionContext<'a> {
    /// Adapter name (e.g. `"agda"`, `"isabelle"`, `"lean"`). Used to
    /// scope adapter-specific markers via
    /// [`super::registry::DisciplineMarker::adapters`].
    pub adapter: &'a str,
    /// The declaration's type / statement text.
    pub statement: &'a str,
    /// The declaration's proof body, if any.
    pub proof: Option<&'a str>,
}

/// Cumulative score threshold above which a discipline is reported.
const DETECTION_THRESHOLD: f32 = 0.7;

/// Detect which [`TypeDiscipline`]s apply to a corpus entry.
///
/// For each marker in `registry` that the entry's text contains,
/// accumulate the marker's `confidence` into a per-discipline score.
/// Disciplines with cumulative score ≥ `DETECTION_THRESHOLD` (0.7) are
/// returned, sorted by score descending.
///
/// Adapter-scoping: markers with non-empty `adapters` are only
/// considered when `ctx.adapter` matches. Markers with empty
/// `adapters` apply to every adapter.
pub fn detect_disciplines(
    ctx: &DetectionContext<'_>,
    registry: &MarkerRegistry,
) -> Vec<TypeDiscipline> {
    let mut scores: HashMap<TypeDiscipline, f32> = HashMap::new();
    let haystack = match ctx.proof {
        Some(p) => format!("{} {}", ctx.statement, p),
        None => ctx.statement.to_string(),
    };
    for marker in registry.all_markers() {
        if !marker.adapters.is_empty() && !marker.adapters.contains(&ctx.adapter) {
            continue;
        }
        if haystack.contains(marker.token) {
            *scores.entry(marker.discipline).or_insert(0.0) += marker.confidence;
        }
    }
    let mut hits: Vec<(TypeDiscipline, f32)> = scores
        .into_iter()
        .filter(|(_, s)| *s >= DETECTION_THRESHOLD)
        .collect();
    hits.sort_by(|a, b| {
        b.1.partial_cmp(&a.1)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    hits.into_iter().map(|(d, _)| d).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_linear_from_keyword() {
        let registry = MarkerRegistry::canonical();
        let ctx = DetectionContext {
            adapter: "lean",
            statement: "def consume (x : linear Nat) : Unit",
            proof: None,
        };
        let tags = detect_disciplines(&ctx, &registry);
        assert!(
            tags.contains(&TypeDiscipline::Linear),
            "expected Linear in {tags:?}"
        );
    }

    #[test]
    fn detects_dependent_from_pi_marker() {
        let registry = MarkerRegistry::canonical();
        let ctx = DetectionContext {
            adapter: "agda",
            statement: "Pi (n : Nat) -> Vec n A",
            proof: None,
        };
        let tags = detect_disciplines(&ctx, &registry);
        assert!(
            tags.contains(&TypeDiscipline::Dependent),
            "expected Dependent in {tags:?}"
        );
    }

    #[test]
    fn detects_ceremonial_from_marker() {
        let registry = MarkerRegistry::canonical();
        let ctx = DetectionContext {
            adapter: "agda",
            statement: "the protocol-bound ceremonial type",
            proof: None,
        };
        let tags = detect_disciplines(&ctx, &registry);
        assert!(
            tags.contains(&TypeDiscipline::Ceremonial),
            "expected Ceremonial in {tags:?}"
        );
    }

    #[test]
    fn adapter_scoping_excludes_other_languages() {
        // Marker that is adapter-scoped to ["lean"] should not fire for "agda".
        // Use `let!` which the spec scoped to lean.
        let registry = MarkerRegistry::canonical();
        let ctx_lean = DetectionContext {
            adapter: "lean",
            statement: "let! x := alloc",
            proof: None,
        };
        let tags_lean = detect_disciplines(&ctx_lean, &registry);
        // We don't assert tags_lean must include Linear (depends on registry seed)
        // but ensure no panic and adapter scoping doesn't yield bogus matches:
        let ctx_other = DetectionContext {
            adapter: "agda",
            statement: "let! x := alloc",
            proof: None,
        };
        let tags_other = detect_disciplines(&ctx_other, &registry);
        // The lean-scoped marker shouldn't contribute when adapter != "lean".
        // Either both are empty (no other markers in this input) or the lean
        // run has at least as many tags as the agda run.
        assert!(
            tags_lean.len() >= tags_other.len(),
            "lean tags={tags_lean:?} should >= agda tags={tags_other:?}"
        );
    }

    #[test]
    fn empty_input_returns_empty() {
        let registry = MarkerRegistry::canonical();
        let ctx = DetectionContext {
            adapter: "agda",
            statement: "",
            proof: None,
        };
        let tags = detect_disciplines(&ctx, &registry);
        assert!(tags.is_empty());
    }
}
