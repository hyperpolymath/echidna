// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Rank-function search for unbudgeted `wf-<ᵇʳᶠ_`.
//!
//! Goal: prove `WellFounded _<ᵇʳᶠ_` directly (without the ℕ budget
//! that `RecursiveSurfaceBudget.agda` currently carries) under
//! `--safe --without-K`. The plan from `docs/buchholz-plan.adoc`:
//! build `rank : BT → Ord` (mapping into Brouwer ordinals), prove
//! `rank-mono : _<ᵇʳᶠ_ ⇒ (_<_ on rank)`, then the Subrelation-on-
//! InverseImage construction transports `Brouwer.wf-<` over.
//!
//! There are several plausible rank functions; this module
//! enumerates them, scores each by how many of its three constructor
//! cases (`<ᵇʳᶠ-core`, `<ᵇʳᶠ-ψα`, `<ᵇʳᶠ-+2`) yield a `rank-mono`
//! clause that can be proved from already-landed lemmas, and reports
//! the best candidate(s) for human translation to Agda.
//!
//! Three knobs (one per BT constructor that takes substructure):
//!   * **bplus** — how to rank `bplus x y`:
//!       - LeftSum:   `rank x ⊕ rank y`
//!       - OsucSum:   `osuc (rank x ⊕ rank y)`
//!       - Hessenberg: `rank x #o rank y`  (commutative natural sum)
//!         (not currently in `Brouwer.Arithmetic`; tracked as a
//!         capability gap)
//!   * **bpsi** — how to rank `bpsi ν α`:
//!       - PsiRank:    `psi-rank ν (rank α)` (the existing
//!                     `osuc (ω-rank ν ⊕ rank α)`)
//!       - PsiRankPlain: `ω-rank ν ⊕ rank α`
//!       - OsucOmegaPlus: `osuc (ω-rank ν) ⊕ rank α`
//!   * **bOmega** — how to rank `bOmega ν`:
//!       - OmegaRank: `ω-rank ν`
//!       - OsucOmegaRank: `osuc (ω-rank ν)`
//!
//! `bzero` is fixed at `oz` (no nontrivial choice).
//!
//! The energy is keyed on:
//!   1. Number of `<ᵇʳᶠ` constructor cases that go through with
//!      already-available lemmas (lower is better; we encode as
//!      "blockers").
//!   2. Capability-gap count: choices like Hessenberg, which need
//!      lemmas that don't yet exist in `Ordinal.Brouwer.Arithmetic`,
//!      add to this.
//!   3. Structural cost: prefer simpler ranks.

#![allow(dead_code)]

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::design_search::DesignProblem;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BplusShape {
    LeftSum,      // rank (bplus x y) = rank x ⊕ rank y
    OsucSum,      // rank (bplus x y) = osuc (rank x ⊕ rank y)
    Hessenberg,   // rank (bplus x y) = rank x #o rank y (commutative; needs lemma)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BpsiShape {
    PsiRank,         // rank (bpsi ν α) = psi-rank ν (rank α) = osuc (ω-rank ν ⊕ rank α)
    PsiRankPlain,    // rank (bpsi ν α) = ω-rank ν ⊕ rank α       (no outer osuc)
    OsucOmegaPlus,   // rank (bpsi ν α) = osuc (ω-rank ν) ⊕ rank α
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BomegaShape {
    OmegaRank,       // rank (bOmega ν) = ω-rank ν
    OsucOmegaRank,   // rank (bOmega ν) = osuc (ω-rank ν)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RankShape {
    pub bplus: BplusShape,
    pub bpsi: BpsiShape,
    pub bomega: BomegaShape,
}

impl RankShape {
    pub fn baseline() -> Self {
        // The most directly "obvious" choice based on what's already
        // landed: psi-rank from Brouwer.Arithmetic, OsucSum (so
        // bplus is strictly above both summands), OmegaRank.
        RankShape {
            bplus: BplusShape::OsucSum,
            bpsi: BpsiShape::PsiRank,
            bomega: BomegaShape::OmegaRank,
        }
    }
}

pub struct BuchholzRankProblem {
    /// Names that are known to be present in the project corpus
    /// (e.g. loaded from `data/corpus/agda.json`). The energy
    /// function consults this to decide whether a rank shape can be
    /// implemented from existing lemmas or whether new ones must be
    /// added (capability gap).
    pub corpus_names: BTreeSet<String>,
}

impl BuchholzRankProblem {
    /// Build with the lemmas we know exist in echo-types as of the
    /// start of this session. The energy function compares against
    /// this baseline; lemmas not present here count as a capability
    /// gap.
    pub fn with_baseline_corpus() -> Self {
        let mut s = BTreeSet::new();
        // Existing in Ordinal.Brouwer:
        s.insert("wf-<".into());
        s.insert("≤-trans".into());
        s.insert("<-trans".into());
        s.insert("<-irrefl".into());
        s.insert("≤-suc".into());
        s.insert("≤-lim".into());
        s.insert("≤-refl".into());
        s.insert("f-in-lim".into());
        s.insert("≤-zero".into());
        // Existing in Ordinal.Brouwer.Arithmetic:
        s.insert("_⊕_".into());
        s.insert("ω-rank".into());
        s.insert("psi-rank".into());
        s.insert("nat-to-ord".into());
        // Existing in Buchholz layer:
        s.insert("_<ᵇ_".into());
        s.insert("_<ᵇʳᶠ_".into());
        s.insert("BT".into());
        BuchholzRankProblem { corpus_names: s }
    }
}

impl DesignProblem for BuchholzRankProblem {
    type State = RankShape;

    fn initial(&self) -> Self::State {
        RankShape::baseline()
    }

    fn neighbours(&self, s: &Self::State) -> Vec<Self::State> {
        let mut out = Vec::new();
        for cand in &[BplusShape::LeftSum, BplusShape::OsucSum, BplusShape::Hessenberg] {
            if *cand != s.bplus {
                out.push(RankShape {
                    bplus: *cand,
                    bpsi: s.bpsi,
                    bomega: s.bomega,
                });
            }
        }
        for cand in &[
            BpsiShape::PsiRank,
            BpsiShape::PsiRankPlain,
            BpsiShape::OsucOmegaPlus,
        ] {
            if *cand != s.bpsi {
                out.push(RankShape {
                    bplus: s.bplus,
                    bpsi: *cand,
                    bomega: s.bomega,
                });
            }
        }
        for cand in &[BomegaShape::OmegaRank, BomegaShape::OsucOmegaRank] {
            if *cand != s.bomega {
                out.push(RankShape {
                    bplus: s.bplus,
                    bpsi: s.bpsi,
                    bomega: *cand,
                });
            }
        }
        out
    }

    fn energy(&self, s: &Self::State) -> Vec<i64> {
        let blockers = blockers(s);
        let cap_gaps = capability_gaps(s, &self.corpus_names);
        let cost = structural_cost(s);
        vec![blockers, cap_gaps, cost]
    }

    fn describe(&self, s: &Self::State) -> String {
        let plus = match s.bplus {
            BplusShape::LeftSum => "rank x ⊕ rank y",
            BplusShape::OsucSum => "osuc (rank x ⊕ rank y)",
            BplusShape::Hessenberg => "rank x #o rank y  [needs Hessenberg sum]",
        };
        let psi = match s.bpsi {
            BpsiShape::PsiRank => "psi-rank ν (rank α)",
            BpsiShape::PsiRankPlain => "ω-rank ν ⊕ rank α",
            BpsiShape::OsucOmegaPlus => "osuc (ω-rank ν) ⊕ rank α",
        };
        let omega = match s.bomega {
            BomegaShape::OmegaRank => "ω-rank ν",
            BomegaShape::OsucOmegaRank => "osuc (ω-rank ν)",
        };
        format!(
            "rank bzero        = oz\nrank (bOmega ν)   = {}\nrank (bplus x y)  = {}\nrank (bpsi ν α)   = {}",
            omega, plus, psi
        )
    }
}

/// Predict how many of the three `<ᵇʳᶠ` constructor cases of
/// `rank-mono` would *fail* to prove with this rank function.
///
/// Constructor cases (need `α <ᵇʳᶠ β → rank α < rank β`):
///   * `<ᵇʳᶠ-core x<ᵇy`: needs `rank x < rank y` from `x <ᵇ y`.
///     This is the Phase-2.2 `rank-mono` for the base Buchholz order
///     — a separate proof obligation. Counts as a blocker for ANY
///     rank shape (because it's a downstream proof, not a property
///     of the rank shape itself).
///   * `<ᵇʳᶠ-ψα α<ᵇʳᶠβ`: need `psi-rank ν (rank α) < psi-rank ν (rank β)`
///     given `rank α < rank β` (recursive). For the `PsiRank` shape,
///     this reduces to `osuc-mono-<` on `(ω-rank ν ⊕ rank α)`, which
///     reduces to `⊕-mono-<-right`. Both are Phase-1.3 deliverables.
///   * `<ᵇʳᶠ-+2 y<ᵇʳᶠz`: need `bplus-rank x α < bplus-rank x β`
///     given `rank α < rank β` (recursive). For OsucSum/LeftSum
///     shapes, reduces to `⊕-mono-<-right`. Hessenberg needs its
///     own monotonicity (not yet proved).
///
/// We model this honestly: every shape blocks on the Phase-1.3 +
/// Phase-2.2 deliverables, but the *number* of new lemmas needed
/// varies. Lower = closer to the goal.
fn blockers(s: &RankShape) -> i64 {
    let mut blockers: i64 = 0;
    // <ᵇʳᶠ-core always needs rank-mono-<ᵇ (Phase 2.2). +1 always.
    blockers += 1;
    // <ᵇʳᶠ-ψα: needs ⊕-mono-< right + osuc-strict-mono.
    // PsiRank has the outer osuc, which is helpful (strict descent
    // is "free"); PsiRankPlain doesn't and is harder.
    match s.bpsi {
        BpsiShape::PsiRank => blockers += 1,        // need ⊕-mono-<-right
        BpsiShape::PsiRankPlain => blockers += 2,   // need ⊕-mono-<-right AND a different psi-strict-mono
        BpsiShape::OsucOmegaPlus => blockers += 2,  // similar issue, plus extra osuc step
    }
    // <ᵇʳᶠ-+2: needs ⊕-mono-<-right.
    match s.bplus {
        BplusShape::LeftSum => blockers += 1,
        BplusShape::OsucSum => blockers += 1,
        BplusShape::Hessenberg => blockers += 2, // also needs Hessenberg-mono
    }
    blockers
}

/// Count rank-shape ingredients that aren't in the corpus yet.
fn capability_gaps(s: &RankShape, names: &BTreeSet<String>) -> i64 {
    let mut gaps: i64 = 0;
    // Hessenberg is not in Ordinal.Brouwer.Arithmetic.
    if s.bplus == BplusShape::Hessenberg {
        gaps += 1;
    }
    // PsiRank uses `psi-rank`, which IS in the corpus.
    // PsiRankPlain / OsucOmegaPlus are inline expressions over
    // existing primitives — no new defs needed.
    // OsucOmegaRank for bOmega is `osuc (ω-rank ν)` — both already
    // present.
    // ω-rank itself:
    if !names.contains("ω-rank") {
        gaps += 1;
    }
    // psi-rank:
    if s.bpsi == BpsiShape::PsiRank && !names.contains("psi-rank") {
        gaps += 1;
    }
    // ⊕:
    if !names.contains("_⊕_") {
        gaps += 1;
    }
    gaps
}

fn structural_cost(s: &RankShape) -> i64 {
    let mut c: i64 = 0;
    if s.bplus == BplusShape::OsucSum {
        c += 1;
    }
    if s.bplus == BplusShape::Hessenberg {
        c += 2;
    }
    if s.bpsi == BpsiShape::PsiRank {
        c += 1;
    }
    if s.bpsi == BpsiShape::OsucOmegaPlus {
        c += 1;
    }
    if s.bomega == BomegaShape::OsucOmegaRank {
        c += 1;
    }
    c
}

/// Render the rank-mono proof skeleton for the chosen shape, as an
/// Agda fragment. Useful for the handoff document.
pub fn render_rank_mono_skeleton(s: &RankShape) -> String {
    let mut out = String::new();
    out.push_str("-- Phase 2 rank function for the unbudgeted `wf-<ᵇʳᶠ_` proof.\n");
    out.push_str("-- All clauses below are TYPE-SIGNATURE-ONLY scaffolds; bodies must\n");
    out.push_str("-- be written by hand or by a follow-up agent that consults\n");
    out.push_str("-- `data/synonyms/agda.toml` for the relevant tactic vocabulary.\n\n");
    out.push_str("rank : BT → Ord\n");
    out.push_str("rank bzero        = oz\n");
    out.push_str(&match s.bomega {
        BomegaShape::OmegaRank => "rank (bOmega ν)   = ω-rank ν\n".to_string(),
        BomegaShape::OsucOmegaRank => "rank (bOmega ν)   = osuc (ω-rank ν)\n".to_string(),
    });
    out.push_str(&match s.bplus {
        BplusShape::LeftSum => {
            "rank (bplus x y)  = rank x ⊕ rank y\n".to_string()
        }
        BplusShape::OsucSum => {
            "rank (bplus x y)  = osuc (rank x ⊕ rank y)\n".to_string()
        }
        BplusShape::Hessenberg => {
            "rank (bplus x y)  = rank x #o rank y  -- DEFINE Hessenberg sum first\n".to_string()
        }
    });
    out.push_str(&match s.bpsi {
        BpsiShape::PsiRank => "rank (bpsi ν α)   = psi-rank ν (rank α)\n".to_string(),
        BpsiShape::PsiRankPlain => {
            "rank (bpsi ν α)   = ω-rank ν ⊕ rank α\n".to_string()
        }
        BpsiShape::OsucOmegaPlus => {
            "rank (bpsi ν α)   = osuc (ω-rank ν) ⊕ rank α\n".to_string()
        }
    });
    out.push_str("\n-- The transport theorem.\n");
    out.push_str("rank-mono : ∀ {x y} → x <ᵇʳᶠ y → rank x < rank y\n");
    out.push_str("rank-mono (<ᵇʳᶠ-core p) = -- needs Phase-2.2 rank-mono-<ᵇ\n");
    out.push_str("rank-mono (<ᵇʳᶠ-ψα p)   = -- needs ⊕-mono-<-right (Phase 1.3)\n");
    out.push_str("rank-mono (<ᵇʳᶠ-+2 p)   = -- needs ⊕-mono-<-right (Phase 1.3)\n\n");
    out.push_str("-- Closing the goal:\n");
    out.push_str("wf-<ᵇʳᶠ : WellFounded _<ᵇʳᶠ_\n");
    out.push_str("wf-<ᵇʳᶠ = Subrelation.wellFounded rank-mono\n");
    out.push_str("            (InverseImage.wellFounded rank wf-<)\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::learning::design_search::anneal;
    use crate::learning::design_search::AnnealConfig;

    #[test]
    fn baseline_has_modest_blockers() {
        let p = BuchholzRankProblem::with_baseline_corpus();
        let e = p.energy(&p.initial());
        // Baseline is Phase-2.2 + ⊕-mono blockers; expect 3.
        assert_eq!(e[0], 3, "baseline blockers should be 3, got {:?}", e);
        // No capability gaps (everything present in corpus).
        assert_eq!(e[1], 0, "baseline should have no capability gaps");
    }

    #[test]
    fn hessenberg_has_capability_gap() {
        let p = BuchholzRankProblem::with_baseline_corpus();
        let mut s = RankShape::baseline();
        s.bplus = BplusShape::Hessenberg;
        let e = p.energy(&s);
        assert!(e[1] >= 1, "Hessenberg should flag a capability gap");
    }

    #[test]
    fn anneal_finds_minimal_blocker_shape() {
        let p = BuchholzRankProblem::with_baseline_corpus();
        let cfg = AnnealConfig {
            max_iterations: 200,
            initial_temp: 4.0,
            cooling: 0.99,
            seed: 99,
            restarts: 4,
        };
        let result = anneal(&p, &cfg);
        // Best should be the baseline (PsiRank + OsucSum).
        assert_eq!(
            result.best_energy[0], 3,
            "expected 3 blockers (Phase-2.2 + ⊕-mono twice); got {:?}",
            result.best_energy
        );
        assert_eq!(result.best_energy[1], 0, "best should have no capability gaps");
    }
}
