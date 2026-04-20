// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Curriculum scheduler.
//!
//! Picks the next proof-shape the self-play loop should attempt. We
//! want to avoid two degenerate regimes:
//!
//!   - **Too easy**: the loop solves every variant and learns nothing
//!     new. Wasted compute, saturation.
//!   - **Too hard**: the loop fails every attempt. Zero gradient, the
//!     expert-iteration retrain has nothing to fit.
//!
//! The sweet spot is a rolling success rate in `[0.3, 0.7]`. The
//! curriculum picks from the candidate pool weighted toward variants
//! whose *expected difficulty* currently sits in that band, where
//! difficulty is estimated from the value head and recent-history of
//! similar variants.

#![allow(dead_code)]

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};

use super::self_play::Variant;

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct CurriculumConfig {
    pub target_success_low: f64,
    pub target_success_high: f64,
    pub history_window: usize,
}

impl Default for CurriculumConfig {
    fn default() -> Self {
        CurriculumConfig {
            target_success_low: 0.30,
            target_success_high: 0.70,
            history_window: 200,
        }
    }
}

#[derive(Debug)]
pub struct Curriculum {
    cfg: CurriculumConfig,
    history: VecDeque<bool>,
}

impl Curriculum {
    pub fn new(cfg: CurriculumConfig) -> Self {
        Curriculum {
            cfg,
            history: VecDeque::new(),
        }
    }

    pub fn record_outcome(&mut self, proved: bool) {
        if self.history.len() == self.cfg.history_window {
            self.history.pop_front();
        }
        self.history.push_back(proved);
    }

    pub fn success_rate(&self) -> f64 {
        if self.history.is_empty() {
            return 0.5;
        }
        let ok = self.history.iter().filter(|b| **b).count();
        ok as f64 / self.history.len() as f64
    }

    /// Regime the curriculum is currently in.
    pub fn regime(&self) -> Regime {
        let r = self.success_rate();
        if r < self.cfg.target_success_low {
            Regime::TooHard
        } else if r > self.cfg.target_success_high {
            Regime::TooEasy
        } else {
            Regime::Productive
        }
    }

    /// Pick the next variant to attempt from `candidates`.
    /// Strategy: sort by crude-difficulty signal derived from
    /// variant kind, then skim the appropriate slice of the list.
    pub fn pick<'a>(&self, candidates: &'a [Variant]) -> Option<&'a Variant> {
        if candidates.is_empty() {
            return None;
        }
        let mut sorted: Vec<(&Variant, u8)> =
            candidates.iter().map(|v| (v, difficulty_hint(v))).collect();
        sorted.sort_by_key(|(_, d)| *d);

        let pick_idx = match self.regime() {
            Regime::TooEasy => sorted.len().saturating_sub(1), // hardest
            Regime::TooHard => 0,                              // easiest
            Regime::Productive => sorted.len() / 2,            // middle
        };
        sorted.get(pick_idx).map(|(v, _)| *v)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Regime {
    TooEasy,
    Productive,
    TooHard,
}

fn difficulty_hint(variant: &Variant) -> u8 {
    // Heuristic: AlphaRename is trivially equivalent → easiest.
    // WeakenHypothesis usually easier than original (fewer assumptions
    // yet but the conclusion is unchanged, so can fail).
    // LemmaLift is hardest — the lifted claim stands alone without the
    // surrounding context.
    match variant.kind {
        super::self_play::VariantKind::AlphaRename => 1,
        super::self_play::VariantKind::WeakenHypothesis => 2,
        super::self_play::VariantKind::LemmaLift => 3,
    }
}
