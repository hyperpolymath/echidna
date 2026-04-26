// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! MetaController — coordinates prover backends with coprocessor backends.
//!
//! Where `ProverRouter` (in `router.rs`) selects a prover for a goal based
//! on goal aspects + GNN guidance, `MetaController` extends the routing
//! domain to the *cross-product* (prover × coprocessor × goal-aspect).
//! It owns the seam where a proof attempt may legitimately decompose into
//! mixed prover and coprocessor work: factor the modulus first (Math
//! coprocessor), then hand a smaller obligation to the SMT prover.
//!
//! Phase 0 ships the routing scaffold and a single integration: any prover
//! goal whose aspects include `arithmetic.factorisation` is allowed to
//! consult the Math coprocessor for a factorisation oracle before
//! prover dispatch.  More integrations are added per backend in Phases 1-5
//! (each new prover declares which coprocessor ops it can use), and the
//! Pareto / Bayesian-timeout extension to multi-modal compute lands in
//! Phase 7.
//!
//! The controller is intentionally lightweight — it composes existing
//! `ProverRouter`, the trust pipeline in `dispatch.rs`, and the new
//! `CoprocessorFactory`.  No new long-lived state is introduced here.

use std::collections::HashMap;
use std::sync::Arc;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::coprocessor::{
    Coprocessor, CoprocessorFactory, CoprocessorKind, CoprocessorOp, CoprocessorOutcome,
};
use crate::provers::ProverKind;

use super::AgenticGoal;

/// What `MetaController` decides for a goal: which prover, plus which
/// coprocessor ops (if any) to run as preconditions.
///
/// `Plan` is consumed by the existing `dispatch.rs` pipeline: coprocessor
/// preconditions run first, their outcomes attach to the goal as
/// `precondition_evidence`, and then the prover runs with the augmented
/// state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Plan {
    /// Prover to invoke.
    pub prover: ProverKind,

    /// Optional coprocessor preconditions.  Each entry is run before the
    /// prover dispatch; its outcome is recorded as evidence and may be
    /// substituted into the proof obligation.
    pub coprocessor_preconditions: Vec<Precondition>,
}

/// A single coprocessor op scheduled before a prover attempt.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Precondition {
    /// Which coprocessor handles this op.
    pub kind: CoprocessorKind,

    /// The op itself.
    pub op: CoprocessorOp,

    /// Which goal aspect this precondition serves — used by the trust
    /// pipeline to attribute confidence.
    pub aspect: String,
}

/// MetaController state.  Holds the live coprocessor registry and a
/// per-aspect routing table.
///
/// Coprocessor registry is populated at construction time; the
/// `aspect_to_coprocessor_op` table is also static for Phase 0 and grows
/// per backend in later phases.
pub struct MetaController {
    /// Live coprocessor backends, keyed by kind.  `Arc` so a single
    /// instance can be shared across concurrent goal evaluations without
    /// requiring `&mut`.
    coprocessors: HashMap<CoprocessorKind, Arc<dyn Coprocessor>>,

    /// Per-aspect mapping: which coprocessor op (if any) helps with goals
    /// carrying this aspect.  Populated from the static seed table.
    aspect_routing: RwLock<HashMap<String, Vec<AspectHint>>>,
}

/// One entry in the aspect routing table.
#[derive(Debug, Clone)]
struct AspectHint {
    kind: CoprocessorKind,
    /// Op template — payload fields filled at dispatch time from goal
    /// metadata.  Phase 0 carries the static template; richer
    /// substitution comes in Phase 7.
    op_template: CoprocessorOp,
}

impl Default for MetaController {
    fn default() -> Self {
        Self::new()
    }
}

impl MetaController {
    /// Construct a new controller with all natively-available coprocessors
    /// pre-registered.  Phase 0 has only `Math`; Phase 6 adds the rest.
    pub fn new() -> Self {
        let mut coprocessors: HashMap<CoprocessorKind, Arc<dyn Coprocessor>> =
            HashMap::new();
        if let Some(math) = CoprocessorFactory::native(CoprocessorKind::Math) {
            coprocessors.insert(CoprocessorKind::Math, Arc::from(math));
        }

        // Static aspect → coprocessor seed mapping.  Each entry is a
        // template; Phase 0 covers the obvious arithmetic hooks.
        let mut routing: HashMap<String, Vec<AspectHint>> = HashMap::new();

        // Number-theory aspects → Math coprocessor.
        routing.insert(
            "arithmetic.factorisation".to_string(),
            vec![AspectHint {
                kind: CoprocessorKind::Math,
                // Template filled in at dispatch time.
                op_template: CoprocessorOp::BigIntFactor { n: String::new() },
            }],
        );
        routing.insert(
            "arithmetic.primality".to_string(),
            vec![AspectHint {
                kind: CoprocessorKind::Math,
                op_template: CoprocessorOp::BigIntIsProbablePrime { n: String::new() },
            }],
        );
        routing.insert(
            "arithmetic.modular_inverse".to_string(),
            vec![AspectHint {
                kind: CoprocessorKind::Math,
                op_template: CoprocessorOp::BigIntModInverse {
                    a: String::new(),
                    modulus: String::new(),
                },
            }],
        );

        MetaController {
            coprocessors,
            aspect_routing: RwLock::new(routing),
        }
    }

    /// Number of coprocessor backends currently registered.  Useful for
    /// tests + diagnostics.
    pub fn num_coprocessors(&self) -> usize {
        self.coprocessors.len()
    }

    /// Plan a goal: pick a prover and any coprocessor preconditions.
    /// Phase 0 uses a simple rule: for each aspect on the goal, look up
    /// hints in the routing table and queue them all.  Phase 7 will replace
    /// this with a Pareto frontier + Bayesian-timeout solver.
    pub async fn plan(&self, goal: &AgenticGoal) -> Plan {
        let routing = self.aspect_routing.read().await;
        let mut preconditions = Vec::new();
        for aspect in &goal.aspects {
            if let Some(hints) = routing.get(aspect) {
                for hint in hints {
                    preconditions.push(Precondition {
                        kind: hint.kind,
                        op: hint.op_template.clone(),
                        aspect: aspect.clone(),
                    });
                }
            }
        }

        Plan {
            prover: goal.preferred_prover.unwrap_or(ProverKind::Z3),
            coprocessor_preconditions: preconditions,
        }
    }

    /// Run the coprocessor preconditions in a `Plan`.  Returns one
    /// outcome per precondition, in the same order.  Bridge / op failures
    /// are captured as `CoprocessorOutcome::Failure` so callers see them
    /// without losing the rest of the batch.
    pub async fn run_preconditions(
        &self,
        plan: &Plan,
    ) -> Result<Vec<CoprocessorOutcome>> {
        let mut out = Vec::with_capacity(plan.coprocessor_preconditions.len());
        for pre in &plan.coprocessor_preconditions {
            match self.coprocessors.get(&pre.kind) {
                Some(backend) => match backend.dispatch(pre.op.clone()).await {
                    Ok(o) => out.push(o),
                    Err(e) => out.push(CoprocessorOutcome::Failure(e.to_string())),
                },
                None => out.push(CoprocessorOutcome::Failure(format!(
                    "no backend registered for {:?}",
                    pre.kind
                ))),
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};

    fn dummy_goal(aspects: Vec<&str>) -> AgenticGoal {
        AgenticGoal {
            goal: Goal {
                id: "test".to_string(),
                target: Term::Const("true".to_string()),
                hypotheses: vec![],
            },
            priority: super::super::Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: Some(ProverKind::Z3),
            aspects: aspects.into_iter().map(String::from).collect(),
            parent: None,
        }
    }

    #[tokio::test]
    async fn meta_controller_registers_math() {
        let mc = MetaController::new();
        assert_eq!(mc.num_coprocessors(), 1);
    }

    #[tokio::test]
    async fn plan_picks_up_arithmetic_factorisation_hint() {
        let mc = MetaController::new();
        let g = dummy_goal(vec!["arithmetic.factorisation"]);
        let plan = mc.plan(&g).await;
        assert_eq!(plan.prover, ProverKind::Z3);
        assert_eq!(plan.coprocessor_preconditions.len(), 1);
        assert_eq!(
            plan.coprocessor_preconditions[0].kind,
            CoprocessorKind::Math
        );
    }

    #[tokio::test]
    async fn plan_no_aspect_no_precondition() {
        let mc = MetaController::new();
        let g = dummy_goal(vec![]);
        let plan = mc.plan(&g).await;
        assert!(plan.coprocessor_preconditions.is_empty());
    }
}
