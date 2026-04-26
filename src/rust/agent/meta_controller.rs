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
//! Phase 0 shipped the routing scaffold and a single integration (Math).
//! Phase 6A/6B added 9 more coprocessor backends but the controller still
//! only knew about Math.  **Phase 7** (this revision) wires:
//!
//! - **Full coprocessor registry** — all 11 native backends are pre-
//!   registered at `new()`; routing can dispatch to any of them.
//! - **Broad aspect taxonomy** — ~22 aspect → coprocessor-op mappings
//!   covering arithmetic / linalg / crypto / physics / signal / IO /
//!   visualisation / hardware.
//! - **Pareto + Bayesian routing** — when multiple prover candidates fit
//!   a goal, score each via `verification::pareto::ParetoFrontier` using
//!   stats from `verification::statistics::StatisticsTracker` (per-tuple
//!   Bayesian timeout estimation, success rate from prior attempts).
//! - **Outcome recording** — `record_outcome` flows results back to the
//!   stats tracker so subsequent plans converge toward what works.
//!
//! StatisticsTracker integration is *optional* (`Option<Arc<RwLock<…>>>`)
//! so MetaController stays usable in tests and in early bring-up where no
//! prior attempts exist yet.

use std::collections::HashMap;
use std::sync::Arc;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::coprocessor::{
    Coprocessor, CoprocessorFactory, CoprocessorKind, CoprocessorOp, CoprocessorOutcome,
};
use crate::provers::ProverKind;
use crate::verification::confidence::TrustLevel;
use crate::verification::pareto::{ParetoFrontier, ProofCandidate, ProofObjective};
use crate::verification::statistics::StatisticsTracker;

use super::AgenticGoal;

/// What `MetaController` decides for a goal: which prover, plus which
/// coprocessor ops (if any) to run as preconditions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Plan {
    /// Prover to invoke.
    pub prover: ProverKind,

    /// Optional coprocessor preconditions.  Each entry is run before the
    /// prover dispatch; its outcome is recorded as evidence and may be
    /// substituted into the proof obligation.
    pub coprocessor_preconditions: Vec<Precondition>,

    /// Bayesian-estimated timeout (ms) for this plan, derived from prior
    /// (prover, aspect) attempts in the StatisticsTracker.  When stats
    /// are unavailable or sparse, falls back to the caller's default.
    pub estimated_timeout_ms: u64,

    /// Why MetaController picked this plan.  Human-readable diagnostic
    /// for the trust pipeline + supervisor logs.  Pareto vs heuristic
    /// vs explicit preference is captured here.
    pub rationale: String,
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

/// One entry in the aspect routing table.
#[derive(Debug, Clone)]
struct AspectHint {
    kind: CoprocessorKind,
    op_template: CoprocessorOp,
}

/// MetaController state: live coprocessor registry + per-aspect routing
/// table + optional stats tracker for Bayesian routing.
pub struct MetaController {
    coprocessors: HashMap<CoprocessorKind, Arc<dyn Coprocessor>>,
    aspect_routing: RwLock<HashMap<String, Vec<AspectHint>>>,
    stats: Option<Arc<RwLock<StatisticsTracker>>>,
}

impl Default for MetaController {
    fn default() -> Self {
        Self::new()
    }
}

impl MetaController {
    /// Construct a controller with all natively-available coprocessors
    /// pre-registered + the broad aspect taxonomy seeded.  No stats
    /// tracker by default — call `with_stats` to plug one in.
    pub fn new() -> Self {
        let coprocessors = Self::register_native_coprocessors();
        let routing = Self::seed_aspect_routing();
        MetaController {
            coprocessors,
            aspect_routing: RwLock::new(routing),
            stats: None,
        }
    }

    /// Plug a shared `StatisticsTracker` into the controller.  Once set,
    /// `plan_with_pareto` consults stats for ranking and
    /// `record_outcome` flows results back to it.  The tracker is shared
    /// (Arc<RwLock<…>>) so multiple controller instances or external
    /// callers can read/write the same body of evidence.
    pub fn with_stats(mut self, stats: Arc<RwLock<StatisticsTracker>>) -> Self {
        self.stats = Some(stats);
        self
    }

    /// Number of coprocessor backends currently registered.
    pub fn num_coprocessors(&self) -> usize {
        self.coprocessors.len()
    }

    /// Number of aspect → coprocessor routings currently in the table.
    pub async fn num_aspect_routings(&self) -> usize {
        self.aspect_routing.read().await.len()
    }

    // ── Construction helpers ─────────────────────────────────────────────

    /// Register every native coprocessor that `CoprocessorFactory` knows
    /// about.  FLINT is feature-gated — it only appears with `--features flint`.
    fn register_native_coprocessors() -> HashMap<CoprocessorKind, Arc<dyn Coprocessor>> {
        // Iterate the kinds we know exist and ask the factory for each.
        // Factory returns None for unavailable backends (FlintMath without
        // the feature) — those are silently skipped.
        let kinds: &[CoprocessorKind] = &[
            CoprocessorKind::Math,
            CoprocessorKind::Vector,
            CoprocessorKind::Tensor,
            CoprocessorKind::Crypto,
            CoprocessorKind::Physics,
            CoprocessorKind::FlintMath,
            CoprocessorKind::Dsp,
            CoprocessorKind::Io,
            CoprocessorKind::Graphics,
            CoprocessorKind::Audio,
            CoprocessorKind::Fpga,
        ];
        let mut out: HashMap<CoprocessorKind, Arc<dyn Coprocessor>> = HashMap::new();
        for &k in kinds {
            if let Some(backend) = CoprocessorFactory::native(k) {
                out.insert(k, Arc::from(backend));
            }
        }
        out
    }

    /// Seed the aspect → coprocessor-op mapping.  Phase 7 covers the
    /// obvious hooks across all 11 coprocessor kinds.  Each entry is a
    /// template; payload fields are filled at dispatch time from goal
    /// metadata (a future refinement — currently templates carry empty
    /// payloads, callers customise via `Precondition` directly).
    fn seed_aspect_routing() -> HashMap<String, Vec<AspectHint>> {
        let mut r: HashMap<String, Vec<AspectHint>> = HashMap::new();

        // ── Number theory / arithmetic ───────────────────────────────────
        r.insert(
            "arithmetic.factorisation".into(),
            vec![hint_template(CoprocessorKind::Math, CoprocessorOp::BigIntFactor { n: String::new() })],
        );
        r.insert(
            "arithmetic.primality".into(),
            vec![hint_template(CoprocessorKind::Math, CoprocessorOp::BigIntIsProbablePrime { n: String::new() })],
        );
        r.insert(
            "arithmetic.modular_inverse".into(),
            vec![hint_template(
                CoprocessorKind::Math,
                CoprocessorOp::BigIntModInverse { a: String::new(), modulus: String::new() },
            )],
        );
        r.insert(
            "arithmetic.gcd".into(),
            vec![hint_template(CoprocessorKind::Math, CoprocessorOp::BigIntGcd { a: String::new(), b: String::new() })],
        );
        r.insert(
            "arithmetic.modexp".into(),
            vec![hint_template(
                CoprocessorKind::Math,
                CoprocessorOp::BigIntModExp {
                    base: String::new(),
                    exp: String::new(),
                    modulus: String::new(),
                },
            )],
        );

        // ── Polynomial algebra (FLINT) ───────────────────────────────────
        r.insert(
            "algebra.polynomial.gcd".into(),
            vec![hint_template(
                CoprocessorKind::FlintMath,
                CoprocessorOp::FlintPolyGcd { f: String::new(), g: String::new() },
            )],
        );
        r.insert(
            "algebra.polynomial.product".into(),
            vec![hint_template(
                CoprocessorKind::FlintMath,
                CoprocessorOp::FlintPolyMul { f: String::new(), g: String::new() },
            )],
        );

        // ── Linear algebra (Vector + Tensor) ─────────────────────────────
        r.insert(
            "linear_algebra.dot".into(),
            vec![hint_template(CoprocessorKind::Vector, CoprocessorOp::VectorDot { a: vec![], b: vec![] })],
        );
        r.insert(
            "linear_algebra.norm".into(),
            vec![hint_template(CoprocessorKind::Vector, CoprocessorOp::VectorNorm { a: vec![] })],
        );
        r.insert(
            "linear_algebra.matmul".into(),
            vec![hint_template(CoprocessorKind::Tensor, CoprocessorOp::TensorMatMul { a: vec![], b: vec![] })],
        );
        r.insert(
            "linear_algebra.determinant".into(),
            vec![hint_template(CoprocessorKind::Tensor, CoprocessorOp::TensorDeterminant { a: vec![] })],
        );

        // ── Crypto ───────────────────────────────────────────────────────
        r.insert(
            "crypto.hash.sha256".into(),
            vec![hint_template(CoprocessorKind::Crypto, CoprocessorOp::CryptoSha256 { bytes: vec![] })],
        );
        r.insert(
            "crypto.hash.blake3".into(),
            vec![hint_template(CoprocessorKind::Crypto, CoprocessorOp::CryptoBlake3 { bytes: vec![] })],
        );
        r.insert(
            "crypto.signature.ed25519_verify".into(),
            vec![hint_template(
                CoprocessorKind::Crypto,
                CoprocessorOp::CryptoEd25519Verify {
                    public_key: vec![],
                    signature: vec![],
                    message: vec![],
                },
            )],
        );

        // ── Physics ──────────────────────────────────────────────────────
        r.insert(
            "physics.ode.step".into(),
            vec![hint_template(
                CoprocessorKind::Physics,
                CoprocessorOp::PhysicsRk4Step {
                    kernel: String::new(),
                    params: vec![],
                    x: vec![],
                    dt: 0.0,
                },
            )],
        );
        r.insert(
            "physics.energy.harmonic".into(),
            vec![hint_template(
                CoprocessorKind::Physics,
                CoprocessorOp::PhysicsHarmonicEnergy { x: 0.0, p: 0.0, omega: 0.0 },
            )],
        );

        // ── Signal processing ────────────────────────────────────────────
        r.insert(
            "signal.fft".into(),
            vec![hint_template(CoprocessorKind::Dsp, CoprocessorOp::DspFft { samples: vec![] })],
        );
        r.insert(
            "signal.window.hann".into(),
            vec![hint_template(CoprocessorKind::Dsp, CoprocessorOp::DspHannWindow { samples: vec![] })],
        );

        // ── IO / artefact handling ───────────────────────────────────────
        r.insert(
            "io.file.hash".into(),
            vec![hint_template(CoprocessorKind::Io, CoprocessorOp::IoSha256OfFile { path: String::new() })],
        );
        r.insert(
            "io.file.line_count".into(),
            vec![hint_template(CoprocessorKind::Io, CoprocessorOp::IoLineCount { path: String::new() })],
        );

        // ── Visualisation ────────────────────────────────────────────────
        r.insert(
            "visualisation.proof_graph".into(),
            vec![hint_template(
                CoprocessorKind::Graphics,
                CoprocessorOp::GraphicsProofGraphSvg { nodes: vec![], edges: vec![] },
            )],
        );

        // ── Audio ────────────────────────────────────────────────────────
        r.insert(
            "audio.completion_chime".into(),
            vec![hint_template(
                CoprocessorKind::Audio,
                CoprocessorOp::AudioCompletionChime { sample_rate: 44_100 },
            )],
        );

        // ── Hardware verification ────────────────────────────────────────
        r.insert(
            "hardware.verilog.synth".into(),
            vec![hint_template(
                CoprocessorKind::Fpga,
                CoprocessorOp::FpgaYosysSynth {
                    verilog: String::new(),
                    top_module: String::new(),
                },
            )],
        );

        r
    }

    // ── Planning ─────────────────────────────────────────────────────────

    /// Plan a goal: pick a prover and any coprocessor preconditions.
    /// Simple rule (Phase 0 carry-over): for each aspect on the goal,
    /// look up hints in the routing table and queue them all.  No Pareto
    /// scoring — `plan_with_pareto` does that when the caller has multiple
    /// prover candidates.
    pub async fn plan(&self, goal: &AgenticGoal) -> Plan {
        let preconditions = self.preconditions_for_goal(goal).await;
        let prover = goal.preferred_prover.unwrap_or(ProverKind::Z3);
        let estimated_timeout_ms = self.estimate_timeout(prover, goal, 30_000).await;
        Plan {
            prover,
            coprocessor_preconditions: preconditions,
            estimated_timeout_ms,
            rationale: format!(
                "preferred_prover={:?}, no Pareto candidates",
                prover
            ),
        }
    }

    /// Plan a goal across multiple candidate provers, scoring via Pareto
    /// over (proof_time_ms, trust_level, memory, steps) using historical
    /// stats.  Picks the candidate with the lowest weighted-rank score on
    /// the Pareto frontier.  Falls back to the goal's preferred_prover (or
    /// Z3) when stats are absent or empty.
    ///
    /// `default_trust` is the trust level assigned to candidates with no
    /// stats history — Tier 2 (basic, single prover) is a sane default.
    pub async fn plan_with_pareto(
        &self,
        goal: &AgenticGoal,
        candidate_provers: &[ProverKind],
        default_timeout_ms: u64,
        default_trust: TrustLevel,
    ) -> Plan {
        if candidate_provers.is_empty() {
            return self.plan(goal).await;
        }

        // Build ProofCandidate per provider, populating from stats where
        // available.
        let domain = primary_domain(goal);
        let mut candidates: Vec<ProofCandidate> = Vec::with_capacity(candidate_provers.len());
        let stats_guard = if let Some(s) = &self.stats {
            Some(s.read().await)
        } else {
            None
        };
        for &p in candidate_provers {
            let mean_time_ms = stats_guard
                .as_ref()
                .and_then(|s| s.get_stats(p, &domain))
                .and_then(|d| d.mean_time_ms())
                .map(|f| f as u64)
                .unwrap_or(default_timeout_ms);
            candidates.push(ProofCandidate {
                id: format!("{:?}", p),
                objectives: ProofObjective {
                    proof_time_ms: mean_time_ms,
                    trust_level: default_trust,
                    // Approximate memory + steps with placeholder values
                    // Phase 8 will track these in StatisticsTracker too.
                    memory_bytes: 0,
                    proof_steps: 0,
                },
                is_pareto_optimal: false,
            });
        }
        let frontier = ParetoFrontier::compute(&mut candidates);
        // Among the Pareto frontier, pick the one with shortest predicted
        // time (weighted_rank with strong time weight).
        let ranked = ParetoFrontier::weighted_rank(&candidates, 1.0, 0.5, 0.0, 0.0);
        let chosen_idx = ranked
            .iter()
            .find(|(i, _)| frontier.contains(i))
            .map(|(i, _)| *i)
            .unwrap_or(0);
        let chosen = candidate_provers[chosen_idx];
        drop(stats_guard);

        let preconditions = self.preconditions_for_goal(goal).await;
        let estimated_timeout_ms = self.estimate_timeout(chosen, goal, default_timeout_ms).await;

        Plan {
            prover: chosen,
            coprocessor_preconditions: preconditions,
            estimated_timeout_ms,
            rationale: format!(
                "pareto over {} candidates → {:?} (frontier size {}, domain {})",
                candidate_provers.len(),
                chosen,
                frontier.len(),
                domain
            ),
        }
    }

    // ── Execution + outcome recording ────────────────────────────────────

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

    /// Record the outcome of a Plan dispatch into the stats tracker so
    /// future planning converges toward what works.  No-op when the
    /// controller has no stats tracker plugged in.
    pub async fn record_outcome(
        &self,
        plan: &Plan,
        goal: &AgenticGoal,
        outcome: PlanOutcome,
        elapsed_ms: u64,
    ) {
        let Some(stats) = &self.stats else { return };
        let domain = primary_domain(goal);
        let mut s = stats.write().await;
        match outcome {
            PlanOutcome::Success => s.record_success(plan.prover, &domain, elapsed_ms),
            PlanOutcome::Timeout => s.record_timeout(plan.prover, &domain),
            PlanOutcome::Failure => s.record_failure(plan.prover, &domain),
        }
    }

    // ── Internals ────────────────────────────────────────────────────────

    async fn preconditions_for_goal(&self, goal: &AgenticGoal) -> Vec<Precondition> {
        let routing = self.aspect_routing.read().await;
        let mut out = Vec::new();
        for aspect in &goal.aspects {
            if let Some(hints) = routing.get(aspect) {
                for hint in hints {
                    // Only emit a precondition if the backend is actually
                    // registered.  FLINT may be unavailable without the
                    // feature flag, in which case the routing table still
                    // names it but the controller routes around.
                    if self.coprocessors.contains_key(&hint.kind) {
                        out.push(Precondition {
                            kind: hint.kind,
                            op: hint.op_template.clone(),
                            aspect: aspect.clone(),
                        });
                    }
                }
            }
        }
        out
    }

    async fn estimate_timeout(
        &self,
        prover: ProverKind,
        goal: &AgenticGoal,
        default_ms: u64,
    ) -> u64 {
        let Some(stats) = &self.stats else { return default_ms };
        let s = stats.read().await;
        s.estimate_timeout(prover, &primary_domain(goal), default_ms)
    }
}

/// Outcome flavour passed to `record_outcome`.
#[derive(Debug, Clone, Copy)]
pub enum PlanOutcome {
    Success,
    Timeout,
    Failure,
}

/// Pick a stable domain key for a goal — used for stats keying.  We use
/// the first aspect (lexicographically? no — order-as-given so the user
/// can prioritise).  Empty aspect list → "unspecified".
fn primary_domain(goal: &AgenticGoal) -> String {
    goal.aspects
        .first()
        .cloned()
        .unwrap_or_else(|| "unspecified".to_string())
}

fn hint_template(kind: CoprocessorKind, op_template: CoprocessorOp) -> AspectHint {
    AspectHint { kind, op_template }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};
    use crate::verification::confidence::TrustLevel;

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
    async fn registers_all_native_coprocessors() {
        let mc = MetaController::new();
        // 10 always-on (Math, Vector, Tensor, Crypto, Physics, Dsp, Io,
        // Graphics, Audio, Fpga) + 1 feature-gated (FlintMath).
        // Without --features flint we expect 10; with it, 11.
        let n = mc.num_coprocessors();
        assert!(
            n == 10 || n == 11,
            "expected 10 (no flint) or 11 (with flint), got {n}"
        );
    }

    #[tokio::test]
    async fn aspect_routing_covers_each_kind_at_least_once() {
        let mc = MetaController::new();
        // Spot-check one aspect per kind (excluding FlintMath which is
        // feature-gated; if absent its hints are filtered out).
        let cases = [
            ("arithmetic.factorisation", CoprocessorKind::Math),
            ("linear_algebra.dot", CoprocessorKind::Vector),
            ("linear_algebra.matmul", CoprocessorKind::Tensor),
            ("crypto.hash.sha256", CoprocessorKind::Crypto),
            ("physics.ode.step", CoprocessorKind::Physics),
            ("signal.fft", CoprocessorKind::Dsp),
            ("io.file.hash", CoprocessorKind::Io),
            ("visualisation.proof_graph", CoprocessorKind::Graphics),
            ("audio.completion_chime", CoprocessorKind::Audio),
            ("hardware.verilog.synth", CoprocessorKind::Fpga),
        ];
        for (aspect, expected_kind) in cases {
            let g = dummy_goal(vec![aspect]);
            let plan = mc.plan(&g).await;
            assert!(
                plan.coprocessor_preconditions.iter().any(|p| p.kind == expected_kind),
                "aspect {aspect} → {:?} not found in preconditions {:?}",
                expected_kind,
                plan.coprocessor_preconditions
            );
        }
    }

    #[tokio::test]
    async fn plan_with_pareto_picks_from_candidates() {
        let mc = MetaController::new();
        let g = dummy_goal(vec!["arithmetic.factorisation"]);
        let candidates = [ProverKind::Z3, ProverKind::CVC5];
        let plan = mc
            .plan_with_pareto(&g, &candidates, 30_000, TrustLevel::Level2)
            .await;
        assert!(candidates.contains(&plan.prover), "chose {:?}", plan.prover);
        assert!(plan.rationale.contains("pareto"));
        // Should still pick up the Math precondition for the aspect.
        assert!(plan.coprocessor_preconditions.iter().any(|p| p.kind == CoprocessorKind::Math));
    }

    #[tokio::test]
    async fn plan_with_pareto_falls_back_when_no_candidates() {
        let mc = MetaController::new();
        let g = dummy_goal(vec![]);
        let plan = mc.plan_with_pareto(&g, &[], 30_000, TrustLevel::Level2).await;
        assert_eq!(plan.prover, ProverKind::Z3);
    }

    #[tokio::test]
    async fn record_outcome_with_no_stats_is_noop() {
        let mc = MetaController::new();
        let g = dummy_goal(vec!["arithmetic.factorisation"]);
        let plan = mc.plan(&g).await;
        // Should not panic / error even though stats is None.
        mc.record_outcome(&plan, &g, PlanOutcome::Success, 1234).await;
    }

    #[tokio::test]
    async fn record_outcome_updates_stats_when_present() {
        let stats = Arc::new(RwLock::new(StatisticsTracker::new()));
        let mc = MetaController::new().with_stats(stats.clone());
        let g = dummy_goal(vec!["arithmetic.factorisation"]);
        let plan = mc.plan(&g).await;

        mc.record_outcome(&plan, &g, PlanOutcome::Success, 500).await;
        mc.record_outcome(&plan, &g, PlanOutcome::Success, 700).await;
        mc.record_outcome(&plan, &g, PlanOutcome::Failure, 0).await;

        let s = stats.read().await;
        let entry = s
            .get_stats(plan.prover, "arithmetic.factorisation")
            .expect("stats entry exists after recording");
        assert_eq!(entry.success_rate(), 2.0 / 3.0);
        assert!(entry.mean_time_ms().is_some());
    }

    #[tokio::test]
    async fn estimate_timeout_uses_stats_when_present() {
        let stats = Arc::new(RwLock::new(StatisticsTracker::new()));
        // Pre-populate: ten 100 ms successes so the Bayesian estimate
        // should land near 100 + a few sigma, well below default 30s.
        {
            let mut s = stats.write().await;
            for _ in 0..10 {
                s.record_success(ProverKind::Z3, "arithmetic.gcd", 100);
            }
        }
        let mc = MetaController::new().with_stats(stats);
        let g = dummy_goal(vec!["arithmetic.gcd"]);
        let plan = mc.plan(&g).await;
        // With ten 100 ms successes, estimated timeout should be < 5 s.
        assert!(
            plan.estimated_timeout_ms < 5_000,
            "estimated timeout was {} ms (expected < 5000)",
            plan.estimated_timeout_ms
        );
    }

    #[tokio::test]
    async fn flint_aspect_hint_filtered_when_backend_absent() {
        // Without --features flint, FlintMath is not registered.  An
        // aspect routed only to FlintMath should produce no precondition.
        let mc = MetaController::new();
        let g = dummy_goal(vec!["algebra.polynomial.gcd"]);
        let plan = mc.plan(&g).await;
        if !mc.coprocessors.contains_key(&CoprocessorKind::FlintMath) {
            // Without the feature, expect zero preconditions for this aspect.
            assert!(
                plan.coprocessor_preconditions.is_empty(),
                "FlintMath absent — expected zero preconditions, got {:?}",
                plan.coprocessor_preconditions
            );
        } else {
            assert!(plan.coprocessor_preconditions.iter().any(|p| p.kind == CoprocessorKind::FlintMath));
        }
    }
}
