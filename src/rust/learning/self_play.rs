// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Self-play corpus generator.
//!
//! Given a successful proof, produce variant lemmas that are likely
//! provable but stylistically different. Three cheap, principled
//! transforms:
//!
//!   1. **Universal-intro swap** — replace a bound variable with a
//!      fresh one (alpha-renaming). Trivially provable; acts as a
//!      sanity-check example in training.
//!   2. **Weaken hypothesis** — drop a conjunct from an assumption.
//!      Often still provable; when it isn't, the *failure* is the
//!      training signal.
//!   3. **Lemma-lift** — promote an intermediate proof-script
//!      judgement to a standalone goal. Almost certainly provable
//!      (by the same tail of the original script).
//!
//! The generator does NOT call the prover itself — it only emits
//! candidate lemmas. The self-learning daemon then runs the MCTS
//! searcher on each; whichever are provable become new training
//! data.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

use crate::core::{Goal, ProofState, Tactic, Term};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VariantKind {
    AlphaRename,
    WeakenHypothesis,
    LemmaLift,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Variant {
    pub kind: VariantKind,
    pub state: ProofState,
    pub rationale: String,
}

pub struct SelfPlayGenerator {
    pub alpha_counter: usize,
}

impl SelfPlayGenerator {
    pub fn new() -> Self {
        SelfPlayGenerator { alpha_counter: 0 }
    }

    /// Emit all variants derivable from one proven ProofState.
    pub fn emit_variants(&mut self, proven: &ProofState) -> Vec<Variant> {
        let mut out = Vec::new();
        if let Some(v) = self.alpha_rename(proven) {
            out.push(v);
        }
        out.extend(self.weaken_hypotheses(proven));
        out.extend(self.lemma_lifts(proven));
        out
    }

    fn alpha_rename(&mut self, state: &ProofState) -> Option<Variant> {
        self.alpha_counter += 1;
        let goal = state.goals.first()?;
        let renamed = rename_binders(&goal.target, self.alpha_counter);
        if renamed == goal.target {
            return None;
        }
        let mut new_state = state.clone();
        if let Some(g) = new_state.goals.first_mut() {
            g.target = renamed;
        }
        Some(Variant {
            kind: VariantKind::AlphaRename,
            state: new_state,
            rationale: format!(
                "alpha-renamed bound variables (cycle {})",
                self.alpha_counter
            ),
        })
    }

    fn weaken_hypotheses(&self, state: &ProofState) -> Vec<Variant> {
        let mut variants = Vec::new();
        let Some(goal) = state.goals.first() else {
            return variants;
        };
        for (i, _) in goal.hypotheses.iter().enumerate() {
            let mut new_state = state.clone();
            if let Some(g) = new_state.goals.first_mut() {
                g.hypotheses.remove(i);
            }
            variants.push(Variant {
                kind: VariantKind::WeakenHypothesis,
                state: new_state,
                rationale: format!("dropped hypothesis #{}", i),
            });
        }
        variants
    }

    fn lemma_lifts(&self, state: &ProofState) -> Vec<Variant> {
        let mut variants = Vec::new();
        for (i, tactic) in state.proof_script.iter().enumerate() {
            if let Some(claim) = extract_claim(tactic) {
                let mut lifted = state.clone();
                lifted.goals = vec![Goal {
                    id: format!("lifted_lemma_{}", i),
                    target: claim,
                    hypotheses: vec![],
                }];
                lifted.proof_script.clear();
                variants.push(Variant {
                    kind: VariantKind::LemmaLift,
                    state: lifted,
                    rationale: format!("lifted intermediate claim at step {}", i),
                });
            }
        }
        variants
    }
}

impl Default for SelfPlayGenerator {
    fn default() -> Self {
        Self::new()
    }
}

fn rename_binders(term: &Term, seed: usize) -> Term {
    match term {
        Term::Var(name) => Term::Var(format!("{}_{}", name, seed)),
        Term::App { func, args } => Term::App {
            func: Box::new(rename_binders(func, seed)),
            args: args.iter().map(|a| rename_binders(a, seed)).collect(),
        },
        Term::Lambda {
            param,
            param_type,
            body,
        } => Term::Lambda {
            param: format!("{}_{}", param, seed),
            param_type: param_type
                .as_ref()
                .map(|t| Box::new(rename_binders(t, seed))),
            body: Box::new(rename_binders(body, seed)),
        },
        Term::Pi {
            param,
            param_type,
            body,
        } => Term::Pi {
            param: format!("{}_{}", param, seed),
            param_type: Box::new(rename_binders(param_type, seed)),
            body: Box::new(rename_binders(body, seed)),
        },
        other => other.clone(),
    }
}

fn extract_claim(tactic: &Tactic) -> Option<Term> {
    match tactic {
        // `Exact(term)` asserts a candidate proof term, which is
        // effectively a lemma's content.
        Tactic::Exact(term) => Some(term.clone()),
        // `Cases(term)` and `Induction(term)` split on `term`, which
        // is a claim worth lifting as a lemma.
        Tactic::Cases(term) => Some(term.clone()),
        Tactic::Induction(term) => Some(term.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Hypothesis;

    fn triv_state() -> ProofState {
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Pi {
                param: "x".to_string(),
                param_type: Box::new(Term::Const("Nat".to_string())),
                body: Box::new(Term::Var("x".to_string())),
            },
            hypotheses: vec![Hypothesis {
                name: "h0".to_string(),
                ty: Term::Const("P".to_string()),
                body: None,
            }],
        });
        s
    }

    #[test]
    fn alpha_rename_produces_new_binder() {
        let mut gen = SelfPlayGenerator::new();
        let v = gen.alpha_rename(&triv_state()).unwrap();
        match &v.state.goals[0].target {
            Term::Pi { param, .. } => assert!(param.starts_with("x_")),
            _ => panic!("expected Pi"),
        }
    }

    #[test]
    fn weaken_drops_one_hypothesis() {
        let gen = SelfPlayGenerator::new();
        let v = &gen.weaken_hypotheses(&triv_state())[0];
        assert!(v.state.goals[0].hypotheses.is_empty());
    }
}
