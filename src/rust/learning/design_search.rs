// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Simulated annealing over **proof-design space** (not tactic space).
//!
//! The existing `learning/mcts.rs` searches over tactic sequences for
//! a fixed signature. This module searches over the *signature itself*
//! — what constructors the relation should have, whether it's defined
//! as a `data` type or as a recursive function, etc. The use case is
//! a class of problem where the proof goal is well-formed but the
//! current axiomatisation makes one or more downstream lemmas
//! awkward; the search asks "which axiomatisation makes the most
//! downstream lemmas land cleanly?"
//!
//! Concretely seeded for echo-types' Phase 1.3 Brouwer redesign:
//! `Ordinal.Brouwer._≤_` currently has constructors
//! `≤-refl / ≤-suc / ≤-lim`, which makes `osuc-mono-≤ : x ≤ y → osuc x
//! ≤ osuc y` blocked in the `≤-lim` case (premise `x ≤ f n` doesn't
//! lift to `osuc x ≤ f n`). Two candidate fixes named in
//! `docs/buchholz-plan.adoc`: add a `≤-lim-below` constructor, or
//! switch to a recursive definition. This module enumerates these
//! and a few neighbours, ranks them by a symbolic energy, and reports
//! the top candidates for human spot-check before recompiling Agda.
//!
//! The framework is generic; the Brouwer instance lives in
//! `learning::design_search::brouwer`.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::fmt::Debug;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::{Deserialize, Serialize};

/// The minimum surface a domain has to expose for the annealer.
pub trait DesignProblem {
    /// Self-contained representation of one candidate design.
    type State: Clone + Debug + Eq + std::hash::Hash;

    /// Initial state — typically the *current* axiomatisation we want
    /// to improve on.
    fn initial(&self) -> Self::State;

    /// Generate the candidate moves available from `s`. Caller is
    /// responsible for ensuring the moves are bounded; the annealer
    /// picks one uniformly at random.
    fn neighbours(&self, s: &Self::State) -> Vec<Self::State>;

    /// Lex-ordered energy. Lower is better in every coordinate.
    /// Lex order means the annealer prefers a state that's
    /// strictly-better in coordinate i over any state that's better
    /// only in coordinate j > i.
    fn energy(&self, s: &Self::State) -> Vec<i64>;

    /// Human-readable description (a few lines).
    fn describe(&self, s: &Self::State) -> String;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnnealConfig {
    pub max_iterations: usize,
    pub initial_temp: f64,
    /// Multiplicative cooling factor per iteration. 0.995 over 1000
    /// iterations gives final/initial ≈ 0.0067.
    pub cooling: f64,
    pub seed: u64,
    /// Number of independent restarts. Each restart uses a different
    /// derived seed and contributes its best to the final result.
    pub restarts: usize,
}

impl Default for AnnealConfig {
    fn default() -> Self {
        AnnealConfig {
            max_iterations: 1_000,
            initial_temp: 4.0,
            cooling: 0.995,
            seed: 0xC0FFEE,
            restarts: 4,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AnnealResult<S> {
    /// Best state across all restarts.
    pub best: S,
    pub best_energy: Vec<i64>,
    /// Top-K distinct states sorted ascending by energy. Includes
    /// `best` at index 0.
    pub topk: Vec<(S, Vec<i64>)>,
    /// Total Metropolis steps across restarts.
    pub steps: usize,
    /// How many of those steps were accepted.
    pub accepted: usize,
}

/// Lex-compare two energy vectors. Shorter vectors are padded with 0
/// at the tail (so a 3-coord state and a 4-coord state still compare
/// in their shared prefix).
fn lex_cmp(a: &[i64], b: &[i64]) -> std::cmp::Ordering {
    let n = a.len().max(b.len());
    for i in 0..n {
        let ai = a.get(i).copied().unwrap_or(0);
        let bi = b.get(i).copied().unwrap_or(0);
        match ai.cmp(&bi) {
            std::cmp::Ordering::Equal => continue,
            other => return other,
        }
    }
    std::cmp::Ordering::Equal
}

/// Approximate "how much worse is `to` than `from`". Used as the
/// Metropolis ΔE. We collapse the lex vector into a scalar by
/// weighting earlier coordinates more heavily.
fn delta_energy(from: &[i64], to: &[i64]) -> f64 {
    let n = from.len().max(to.len());
    let mut delta: f64 = 0.0;
    for i in 0..n {
        let f = from.get(i).copied().unwrap_or(0) as f64;
        let t = to.get(i).copied().unwrap_or(0) as f64;
        // Weight: 1000^(n-i-1). The first coord dominates by a
        // factor of 1000 per position.
        let w = (1000_f64).powi((n - i - 1) as i32);
        delta += w * (t - f);
    }
    delta
}

pub fn anneal<P: DesignProblem>(problem: &P, config: &AnnealConfig) -> AnnealResult<P::State> {
    use std::collections::HashMap;

    let mut all_seen: HashMap<P::State, Vec<i64>> = HashMap::new();
    let mut total_steps = 0usize;
    let mut total_accepted = 0usize;
    let mut overall_best: Option<(P::State, Vec<i64>)> = None;

    for restart in 0..config.restarts.max(1) {
        let mut rng = StdRng::seed_from_u64(config.seed.wrapping_add(restart as u64));
        let mut current = problem.initial();
        let mut current_e = problem.energy(&current);
        let mut best = current.clone();
        let mut best_e = current_e.clone();
        let mut temp = config.initial_temp;

        all_seen.entry(current.clone()).or_insert_with(|| current_e.clone());

        for _ in 0..config.max_iterations {
            total_steps += 1;
            let neighbours = problem.neighbours(&current);
            if neighbours.is_empty() {
                break;
            }
            let pick = rng.gen_range(0..neighbours.len());
            let cand = neighbours[pick].clone();
            let cand_e = problem.energy(&cand);

            all_seen.entry(cand.clone()).or_insert_with(|| cand_e.clone());

            let accept = match lex_cmp(&cand_e, &current_e) {
                std::cmp::Ordering::Less => true,
                std::cmp::Ordering::Equal => true,
                std::cmp::Ordering::Greater => {
                    let de = delta_energy(&current_e, &cand_e);
                    let p: f64 = (-de / temp).exp();
                    rng.gen::<f64>() < p
                }
            };

            if accept {
                total_accepted += 1;
                current = cand;
                current_e = cand_e.clone();
                if lex_cmp(&cand_e, &best_e) == std::cmp::Ordering::Less {
                    best = current.clone();
                    best_e = cand_e;
                }
            }

            temp *= config.cooling;
        }

        if let Some((_, oe)) = &overall_best {
            if lex_cmp(&best_e, oe) == std::cmp::Ordering::Less {
                overall_best = Some((best, best_e));
            }
        } else {
            overall_best = Some((best, best_e));
        }
    }

    let mut all: Vec<(P::State, Vec<i64>)> = all_seen.into_iter().collect();
    all.sort_by(|(_, a), (_, b)| lex_cmp(a, b));
    let topk: Vec<_> = all.into_iter().take(12).collect();

    let (best, best_energy) = overall_best.expect("annealer ran 0 restarts");

    AnnealResult {
        best,
        best_energy,
        topk,
        steps: total_steps,
        accepted: total_accepted,
    }
}

// ===========================================================================
// Brouwer instance: the Phase-1.3 problem.
// ===========================================================================

pub mod brouwer {
    //! The Phase-1.3 Brouwer `_≤_` redesign as a `DesignProblem`.
    //!
    //! State space = a candidate axiomatisation:
    //!   * `style ∈ {Data, Recursive}`,
    //!   * `constructors ⊆ { Refl, SucRight, LimRight, LimBelow,
    //!                       CongSuc, ZeroMin, AntiRefl, TransClosure }`.
    //!
    //! Hard constraint: at least one constructor mentioning each
    //! Ord-shape pair (osuc/osuc, osuc/olim, olim/β) must be derivable
    //! — we'd reject states that can't even prove `≤-zero`.
    //!
    //! Energy (lex, lower is better):
    //!   1. number of *blocked* monotonicity lemmas (osuc-mono, ⊕-mono-right,
    //!      ≤-trans),
    //!   2. number of K-elimination hazards introduced,
    //!   3. constructor count (preferring smaller axiomatisations),
    //!   4. tie-breaker: data > recursive (recursive preferred when
    //!      everything else ties, because definitional equalities
    //!      simplify downstream proofs).

    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum Ctor {
        /// `≤-refl : ∀ {α} → α ≤ α`
        Refl,
        /// `≤-suc : ∀ {α β} → α ≤ β → α ≤ osuc β`
        SucRight,
        /// `≤-lim : ∀ {α f} n → α ≤ f n → α ≤ olim f`
        LimRight,
        /// NEW: `≤-lim-below : (∀ n → f n ≤ β) → olim f ≤ β`
        LimBelow,
        /// NEW: `≤-cong-suc : x ≤ y → osuc x ≤ osuc y`
        ///   (hardwires `osuc-mono-≤` as a constructor)
        CongSuc,
        /// `≤-zero : ∀ {α} → oz ≤ α`
        ///   (currently a derived lemma; making it a constructor
        ///    flattens some proof obligations)
        ZeroMin,
        /// CLOSURE-TRANS: include transitivity as a constructor (rare;
        /// usually a theorem). Adds K-elim risk.
        TransClosure,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum Style {
        /// `data _≤_ : Ord → Ord → Set where …`
        Data,
        /// `_≤_ : Ord → Ord → Set` with pattern-matching equations.
        Recursive,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct LeqState {
        pub style: Style,
        pub ctors: BTreeSet<Ctor>,
    }

    impl LeqState {
        /// The current Phase-1.1 axiomatisation, our baseline.
        pub fn phase1_1() -> Self {
            let mut s = BTreeSet::new();
            s.insert(Ctor::Refl);
            s.insert(Ctor::SucRight);
            s.insert(Ctor::LimRight);
            LeqState {
                style: Style::Data,
                ctors: s,
            }
        }
    }

    pub struct BrouwerLeqProblem {
        /// Optional cap on constructor count to keep the search
        /// space bounded.
        pub max_ctors: usize,
    }

    impl Default for BrouwerLeqProblem {
        fn default() -> Self {
            BrouwerLeqProblem { max_ctors: 6 }
        }
    }

    impl DesignProblem for BrouwerLeqProblem {
        type State = LeqState;

        fn initial(&self) -> Self::State {
            LeqState::phase1_1()
        }

        fn neighbours(&self, s: &Self::State) -> Vec<Self::State> {
            let mut out: Vec<LeqState> = Vec::new();
            let all = [
                Ctor::Refl,
                Ctor::SucRight,
                Ctor::LimRight,
                Ctor::LimBelow,
                Ctor::CongSuc,
                Ctor::ZeroMin,
                Ctor::TransClosure,
            ];

            // Add a missing constructor.
            if s.ctors.len() < self.max_ctors {
                for c in &all {
                    if !s.ctors.contains(c) {
                        let mut nc = s.ctors.clone();
                        nc.insert(*c);
                        out.push(LeqState {
                            style: s.style,
                            ctors: nc,
                        });
                    }
                }
            }

            // Remove a constructor (provided we keep at least Refl
            // and at least one of {SucRight, CongSuc} so successor
            // is reachable).
            for c in &all {
                if s.ctors.contains(c) && s.ctors.len() > 1 {
                    let mut nc = s.ctors.clone();
                    nc.remove(c);
                    let has_succ_path =
                        nc.contains(&Ctor::SucRight) || nc.contains(&Ctor::CongSuc);
                    let has_refl =
                        nc.contains(&Ctor::Refl) || s.style == Style::Recursive;
                    if has_succ_path && has_refl {
                        out.push(LeqState {
                            style: s.style,
                            ctors: nc,
                        });
                    }
                }
            }

            // Flip style.
            let flipped = match s.style {
                Style::Data => Style::Recursive,
                Style::Recursive => Style::Data,
            };
            out.push(LeqState {
                style: flipped,
                ctors: s.ctors.clone(),
            });

            out
        }

        fn energy(&self, s: &Self::State) -> Vec<i64> {
            let blocked = mono_blockers(s);
            let k_haz = k_hazards(s);
            let ctor_count = s.ctors.len() as i64;
            let style_pref = match s.style {
                Style::Recursive => 0,
                Style::Data => 1,
            };
            vec![blocked, k_haz, ctor_count, style_pref]
        }

        fn describe(&self, s: &Self::State) -> String {
            let mut ctor_list: Vec<&str> = s
                .ctors
                .iter()
                .map(|c| match c {
                    Ctor::Refl => "≤-refl",
                    Ctor::SucRight => "≤-suc",
                    Ctor::LimRight => "≤-lim",
                    Ctor::LimBelow => "≤-lim-below",
                    Ctor::CongSuc => "≤-cong-suc",
                    Ctor::ZeroMin => "≤-zero",
                    Ctor::TransClosure => "≤-trans (closure)",
                })
                .collect();
            ctor_list.sort();
            format!(
                "{:?}-style {{ {} }}",
                s.style,
                ctor_list.join(", ")
            )
        }
    }

    /// Predict how many of our three target monotonicity lemmas are
    /// blocked under this axiomatisation.
    ///
    /// Targets:
    ///   M1. osuc-mono-≤ : x ≤ y → osuc x ≤ osuc y
    ///   M2. ⊕-mono-≤-right : x ≤ y → α ⊕ x ≤ α ⊕ y
    ///   M3. ≤-trans : transitivity (already worked in Phase 1.1, but
    ///       a poor axiomatisation can break it)
    fn mono_blockers(s: &LeqState) -> i64 {
        let mut blockers: i64 = 0;
        // M1
        if !mono_osuc_ok(s) {
            blockers += 1;
        }
        // M2
        if !mono_oplus_right_ok(s) {
            blockers += 1;
        }
        // M3
        if !trans_ok(s) {
            blockers += 1;
        }
        blockers
    }

    /// `osuc-mono-≤ : x ≤ y → osuc x ≤ osuc y` is OK iff:
    ///   * `CongSuc` is a constructor — trivial (apply it).
    ///   * style is `Recursive` — the equation
    ///     `osuc α ≤ osuc β = α ≤ β` makes it definitional, so
    ///     `osuc-mono-≤ p = p`.
    ///
    /// Pure data-style with `LimBelow` does NOT unblock this. Hand-
    /// trace: in the `≤-lim n q` case where `q : x ≤ f n` and the goal
    /// is `osuc x ≤ osuc (olim f)`, the natural moves all stall:
    ///   - `≤-suc → ≤-lim k`: needs `osuc x ≤ f k`; recursive call
    ///     produces `osuc x ≤ osuc (f n)`, off by one.
    ///   - `LimBelow`: requires `∀ k. f k ≤ osuc (olim f)` (which we
    ///     can produce), but that gives `olim f ≤ osuc (olim f)`, not
    ///     `osuc x ≤ osuc (olim f)`. We've lost the link to `x`.
    ///
    /// `LimBelow` is useful for *other* lemmas, but not this one.
    fn mono_osuc_ok(s: &LeqState) -> bool {
        if s.ctors.contains(&Ctor::CongSuc) {
            return true;
        }
        if s.style == Style::Recursive {
            return true;
        }
        false
    }

    /// `⊕-mono-≤-right : x ≤ y → α ⊕ x ≤ α ⊕ y`. Goes through iff
    /// either:
    ///   * Recursive style — the recursive `osuc α ⊕ x = osuc (α ⊕ x)`
    ///     and `olim f ⊕ x = olim (λ n → f n ⊕ x)` line up with the
    ///     `_≤_` recursion so the proof is structural;
    ///   * data-style with the recursive style fallback isn't
    ///     available; even `CongSuc` alone is insufficient because
    ///     the `olim f ⊕ -` case has the same `≤-lim` blocker as
    ///     `osuc-mono-≤`.
    ///
    /// Hand-trace omitted; same shape as `mono_osuc_ok`. `CongSuc`
    /// alone does NOT unblock `⊕-mono-≤-right`.
    fn mono_oplus_right_ok(s: &LeqState) -> bool {
        s.style == Style::Recursive
    }

    /// `≤-trans` is OK in Data style with `Refl + SucRight + LimRight`
    /// (the Phase-1.1 proof, structural on the right leg). Adding
    /// `LimBelow` doesn't break it. Recursive style has it for free.
    /// Removing both `SucRight` and `LimRight` would break it.
    fn trans_ok(s: &LeqState) -> bool {
        if s.style == Style::Recursive {
            return true;
        }
        s.ctors.contains(&Ctor::SucRight) && s.ctors.contains(&Ctor::LimRight)
    }

    /// K-elimination hazards under `--without-K`.
    ///
    /// Heuristic:
    ///   * `TransClosure` constructor: high risk — patterns like
    ///     `≤-trans-trans` can introduce reflexive equations the
    ///     K-free unifier rejects.
    ///   * `CongSuc` data constructor: medium risk — direct pattern
    ///     match on `osuc x ≤ osuc x` runs into the same issue that
    ///     blocked `<ᵇ-irrefl` in the Buchholz module.
    ///   * Recursive style with `≤-refl` as a constructor: low risk;
    ///     the recursive equation handles those cases definitionally.
    fn k_hazards(s: &LeqState) -> i64 {
        let mut h: i64 = 0;
        if s.ctors.contains(&Ctor::TransClosure) {
            h += 2;
        }
        if s.ctors.contains(&Ctor::CongSuc) && s.style == Style::Data {
            h += 1;
        }
        h
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn baseline_phase1_1_blocks_osuc_mono() {
            let p = BrouwerLeqProblem::default();
            let e = p.energy(&LeqState::phase1_1());
            // Should report ≥1 blocker (osuc-mono and ⊕-mono both
            // blocked under Refl/SucRight/LimRight).
            assert!(e[0] >= 1, "expected blockers, got {:?}", e);
        }

        #[test]
        fn recursive_style_unblocks_mono() {
            let p = BrouwerLeqProblem::default();
            let mut s = LeqState::phase1_1();
            s.style = Style::Recursive;
            let e = p.energy(&s);
            assert_eq!(e[0], 0, "recursive style should unblock all mono lemmas");
        }

        #[test]
        fn limbelow_alone_does_not_unblock_osuc_mono() {
            // Hand-traced: under `data + LimBelow`, the `≤-lim n q`
            // case of `osuc-mono-≤` still loses the `x` link
            // (LimBelow proves `olim f ≤ ?`, not `osuc x ≤ ?`).
            // Energy must still report at least the osuc-mono blocker.
            let p = BrouwerLeqProblem::default();
            let mut s = LeqState::phase1_1();
            s.ctors.insert(Ctor::LimBelow);
            let e = p.energy(&s);
            assert!(
                e[0] >= 1,
                "LimBelow alone shouldn't unblock osuc-mono in data style; got {:?}",
                e
            );
        }

        #[test]
        fn cong_suc_unblocks_osuc_but_not_oplus() {
            // `≤-cong-suc` makes `osuc-mono-≤` trivial but
            // `⊕-mono-≤-right` still has the limit-on-the-inside
            // blocker. Recursive style unblocks both.
            let p = BrouwerLeqProblem::default();
            let mut s = LeqState::phase1_1();
            s.ctors.insert(Ctor::CongSuc);
            let e = p.energy(&s);
            assert_eq!(
                e[0], 1,
                "CongSuc alone leaves ⊕-mono blocked; got {:?}",
                e
            );
        }

        #[test]
        fn anneal_finds_zero_blocker_state() {
            let p = BrouwerLeqProblem::default();
            let cfg = AnnealConfig {
                max_iterations: 200,
                initial_temp: 4.0,
                cooling: 0.99,
                seed: 42,
                restarts: 4,
            };
            let result = anneal(&p, &cfg);
            assert_eq!(
                result.best_energy[0], 0,
                "annealer should find a zero-blocker state; best={:?} energy={:?}",
                result.best, result.best_energy
            );
        }
    }
}
