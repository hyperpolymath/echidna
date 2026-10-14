// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Unified result arbitration — the single entry point that turns a set
//! of per-prover [`ProverOutcome`]s for the *same* goal into one
//! arbitrated verdict.
//!
//! This is the wiring layer the 4-mechanism arbitration stack was
//! missing: [`super::portfolio::PortfolioSolver::reconcile`],
//! [`super::bayesian_arbiter::BayesianArbiter`],
//! [`super::dempster_shafer::DempsterShaferArbiter`] and
//! [`super::pareto_arbiter::ParetoArbiter`] each define their own input
//! type and none was reachable from the dispatch path, which
//! re-implemented a boolean all-must-agree check inline. The
//! [`ResultArbiter`] here adapts [`ProverOutcome`] into each mechanism's
//! input, delegates verdict fusion to the policy-selected mechanism, and
//! reports disagreement instead of silently collapsing it.
//!
//! Semantics relative to the old inline check:
//! - `Timeout` / `InvalidInput` / `UnsupportedFeature` / errors are
//!   *no-information*, not disagreement. A prover that timed out no
//!   longer vetoes two provers that proved the goal.
//! - A genuine `Proved`-vs-`NoProofFound` split is surfaced as
//!   `needs_review` with both camps named, never flattened to
//!   `verified = false`.
//! - `InconsistentPremises` from any prover sets `suspect_premises`
//!   (and `needs_review`): an unqualified PROVED over inconsistent
//!   premises is epistemically worthless.
//!
//! # Fidelity level (ECH-05)
//!
//! Agreement between backends says nothing about whether they proved
//! the *same* statement: N re-proofs of N lexically aligned statements
//! are N warrants for N propositions. Each [`ProverAttempt`] therefore
//! carries [`FidelityEvidence`] that its formal statement denotes the
//! source claim, and [`ArbitratedVerdict::level`] grades the fused
//! verdict by that evidence ([`fidelity_level`]):
//!
//! - `Belief` if the verdict needs review, rests on a retracted backend
//!   ([`ResultArbiter::retract`]), or any attempt carries
//!   [`FidelityEvidence::None`]; also when no attempt was fused.
//! - `Sound` only if every fused attempt carries a
//!   [`FidelityEvidence::KernelTranslation`] and all of them name the
//!   same exchange-layer `term_hash`.
//! - `Epi` if every fused attempt is a kernel translation or a
//!   [`FidelityEvidence::DeclaredCorrespondence`] with at least one
//!   consequence test and zero failures, and the kernel translations
//!   agree on the term.
//! - `Belief` otherwise — in particular when two kernel translations
//!   name different terms (a synonym collision).
//!
//! The level sits on top of the numeric fusion, which is unchanged:
//! `tests/arbitration_regression_test.rs` replays the pre-ECH-05 numbers.
//! The Idris2 statement of the levels is `src/abi/EchidnaABI/Arbitration.idr`.

use serde::{Deserialize, Serialize};

use super::bayesian_arbiter::{BayesianArbiter, PosteriorVerdict, ProverEvidence, Verdict};
use super::dempster_shafer::{
    proven_mass, refuted_mass, ArbiterError, BeliefPlausibility, DempsterShaferArbiter,
    MassFunction,
};
use super::pareto_arbiter::{AttemptOutcome, ParetoArbiter};
use super::portfolio::{PortfolioConfidence, PortfolioSolver, SolverResult};
use crate::exchange::ExchangeFormat;
use crate::provers::outcome::ProverOutcome;
use crate::provers::ProverKind;

/// Evidence that a backend's formal statement denotes the source claim.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FidelityEvidence {
    /// The statement was translated through the exchange layer and the
    /// translation was checked by `checked_by`'s kernel. `term_hash`
    /// names the exchange-layer term (see [`crate::exchange::term_hash`]).
    KernelTranslation {
        format: ExchangeFormat,
        checked_by: ProverKind,
        term_hash: String,
    },
    /// A declared correspondence (e.g. a synonym-table alignment) that
    /// was checked by consequence testing: `failures` of
    /// `consequence_tests` consequences of the source claim were not
    /// consequences of the formal statement, or vice versa.
    DeclaredCorrespondence {
        consequence_tests: u32,
        failures: u32,
    },
    /// No evidence beyond the goal the backend was handed (lexical
    /// alignment at best). Caps the arbitrated level at `Belief`.
    #[default]
    None,
}

/// How far an arbitrated verdict is warranted for the source claim.
/// Ordered `Belief < Epi < Sound`.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub enum EpistemicLevel {
    /// Agreement without a fidelity map to the source claim.
    #[default]
    Belief,
    /// Every fused attempt has fidelity evidence, not all of it a
    /// kernel-checked translation.
    Epi,
    /// Every fused attempt is a kernel-checked translation to one
    /// exchange-layer term.
    Sound,
}

/// One prover's contribution to arbitration: which backend ran, what it
/// concluded, how long it took, and the evidence that its statement is
/// the source claim.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverAttempt {
    pub prover: ProverKind,
    pub outcome: ProverOutcome,
    pub elapsed_ms: u64,
    #[serde(default)]
    pub fidelity: FidelityEvidence,
}

impl ProverAttempt {
    /// An attempt with no fidelity evidence.
    pub fn new(prover: ProverKind, outcome: ProverOutcome, elapsed_ms: u64) -> Self {
        Self {
            prover,
            outcome,
            elapsed_ms,
            fidelity: FidelityEvidence::None,
        }
    }

    pub fn with_fidelity(mut self, fidelity: FidelityEvidence) -> Self {
        self.fidelity = fidelity;
        self
    }
}

/// Which fusion mechanism decides the verdict.
///
/// See "Guide: Picking an arbitration mechanism" in `docs/wikis/Guides.md`.
#[derive(Debug, Clone, Copy, PartialEq, Default, Serialize, Deserialize)]
#[serde(tag = "mechanism", rename_all = "snake_case")]
pub enum ArbitrationPolicy {
    /// Categorical agreement via [`PortfolioSolver::reconcile`]: any
    /// conclusive disagreement yields no verdict + `needs_review`. The
    /// conservative default for the trust pipeline.
    #[default]
    Portfolio,
    /// Log-odds posterior over calibrated per-prover likelihoods.
    /// Produces a probability distribution; disagreement still flags
    /// `needs_review` but a verdict is always ranked.
    Bayesian { prior_p_true: f64 },
    /// Dempster-Shafer belief-mass combination; refuses to arbitrate
    /// (verdict `Unknown`, `needs_review`) when conflict mass k > 0.95.
    DempsterShafer,
}

/// The arbitrated verdict over all submitted attempts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArbitratedVerdict {
    /// Winning categorical verdict under the configured policy.
    pub verdict: Verdict,
    /// `Some(true)` proven, `Some(false)` refuted, `None` inconclusive.
    pub verified: Option<bool>,
    /// Categorical agreement summary (always portfolio-derived, even
    /// under Bayesian/DS policies, so consumers get a stable field).
    pub confidence: PortfolioConfidence,
    /// Provers whose conclusive verdict matches `verdict`.
    pub agreeing: Vec<ProverKind>,
    /// Provers whose conclusive verdict opposes `verdict`.
    pub disagreeing: Vec<ProverKind>,
    /// Provers that produced no information (timeout, bad input, error).
    pub inconclusive: Vec<ProverKind>,
    /// True on conclusive disagreement, all-inconclusive input,
    /// Dempster-Shafer high conflict, or suspect premises.
    pub needs_review: bool,
    /// Policy-specific conflict metric in [0, 1]: disagreement ratio
    /// (portfolio), normalised Shannon entropy (Bayesian), or conflict
    /// mass k (Dempster-Shafer).
    pub conflict: f64,
    /// Any prover reported `InconsistentPremises`.
    pub suspect_premises: bool,
    /// Populated under `ArbitrationPolicy::Bayesian`.
    pub posterior: Option<PosteriorVerdict>,
    /// Populated under `ArbitrationPolicy::DempsterShafer` when
    /// combination succeeded.
    pub belief: Option<BeliefPlausibility>,
    /// Pareto-preferred attempt among the agreeing provers (currently
    /// latency-driven — axiom cost and certificate size are not yet
    /// threaded to this layer).
    pub recommended: Option<ProverKind>,
    /// The policy that produced this verdict.
    pub policy: ArbitrationPolicy,
    /// How far `verdict` is warranted for the source claim, from the
    /// attempts' fidelity evidence (see [`fidelity_level`]).
    #[serde(default)]
    pub level: EpistemicLevel,
    /// Retracted backends among the fused attempts; non-empty forces
    /// `level` to `Belief`.
    #[serde(default)]
    pub retracted: Vec<ProverKind>,
    /// The exchange-layer term hash all fused attempts share; set only
    /// when `level` is `Sound`.
    #[serde(default)]
    pub warranted_term: Option<String>,
}

/// Map a rich prover outcome onto the arbitration verdict frame.
///
/// `NoProofFound` maps to `Refuted`, matching both the SMT reading
/// ("sat reply to the negation" = counterexample) and the previous
/// cross-check behaviour where a completed non-verification counted
/// against agreement. `InconsistentPremises` carries no directional
/// information — it is surfaced via `suspect_premises` instead.
pub fn outcome_to_verdict(outcome: &ProverOutcome) -> Verdict {
    match outcome {
        ProverOutcome::Proved { .. } => Verdict::Proven,
        ProverOutcome::NoProofFound { .. } => Verdict::Refuted,
        ProverOutcome::Timeout { .. } => Verdict::Timeout,
        ProverOutcome::InvalidInput { .. }
        | ProverOutcome::UnsupportedFeature { .. }
        | ProverOutcome::InconsistentPremises { .. } => Verdict::Unknown,
        ProverOutcome::ProverError { .. } | ProverOutcome::SystemError { .. } => Verdict::Error,
    }
}

/// The ECH-05 levelling policy (see the module docs). `attempts` is the
/// whole arbitration input, `fused` the attempts whose verdict was fused
/// into the winning one, and `blocked` is true when the verdict needs
/// review or rests on a retracted backend. Returns the level and, at
/// `Sound`, the shared term hash.
///
/// Mirrors `level` in `src/abi/EchidnaABI/Arbitration.idr` (by review; no
/// test ties the two).
pub fn fidelity_level(
    attempts: &[ProverAttempt],
    fused: &[&ProverAttempt],
    blocked: bool,
) -> (EpistemicLevel, Option<String>) {
    if blocked
        || fused.is_empty()
        || attempts
            .iter()
            .any(|a| a.fidelity == FidelityEvidence::None)
    {
        return (EpistemicLevel::Belief, None);
    }

    let mut term: Option<&str> = None;
    let mut all_kernel = true;
    for a in fused {
        match &a.fidelity {
            FidelityEvidence::KernelTranslation { term_hash, .. } => {
                if term_hash.is_empty() || term.is_some_and(|t| t != term_hash) {
                    return (EpistemicLevel::Belief, None);
                }
                term = Some(term_hash);
            },
            FidelityEvidence::DeclaredCorrespondence {
                consequence_tests,
                failures,
            } => {
                if *consequence_tests == 0 || *failures > 0 {
                    return (EpistemicLevel::Belief, None);
                }
                all_kernel = false;
            },
            FidelityEvidence::None => return (EpistemicLevel::Belief, None),
        }
    }

    if all_kernel {
        (EpistemicLevel::Sound, term.map(str::to_owned))
    } else {
        (EpistemicLevel::Epi, None)
    }
}

/// Policy-driven result arbiter. Construct once per dispatch with the
/// configured policy and the per-prover timeout (used by the
/// Dempster-Shafer mass helpers to discount near-timeout verdicts).
#[derive(Debug, Clone)]
pub struct ResultArbiter {
    policy: ArbitrationPolicy,
    timeout_ms: u64,
    retracted: Vec<ProverKind>,
}

impl ResultArbiter {
    pub fn new(policy: ArbitrationPolicy, timeout_ms: u64) -> Self {
        Self {
            policy,
            timeout_ms,
            retracted: Vec::new(),
        }
    }

    /// Mark `prover` unsound. Every later verdict that fuses one of its
    /// attempts drops to `Belief`; verdicts that do not rest on it keep
    /// their level. The numeric fusion still counts its vote — drop the
    /// attempt and re-arbitrate to fuse without it.
    pub fn retract(&mut self, prover: ProverKind) {
        if !self.retracted.contains(&prover) {
            self.retracted.push(prover);
        }
    }

    /// Backends marked unsound via [`Self::retract`].
    pub fn retracted(&self) -> &[ProverKind] {
        &self.retracted
    }

    /// Arbitrate a set of attempts on the same goal into one verdict.
    pub fn arbitrate(&self, attempts: &[ProverAttempt]) -> ArbitratedVerdict {
        let suspect_premises = attempts
            .iter()
            .any(|a| matches!(a.outcome, ProverOutcome::InconsistentPremises { .. }));

        // Categorical layer — always computed so `confidence` and the
        // agreement partition are stable across policies.
        let solver_results: Vec<SolverResult> = attempts
            .iter()
            .map(|a| SolverResult {
                prover: a.prover,
                verified: match outcome_to_verdict(&a.outcome) {
                    Verdict::Proven => Some(true),
                    Verdict::Refuted => Some(false),
                    _ => None,
                },
                time_ms: a.elapsed_ms,
                has_certificate: false,
                error: match &a.outcome {
                    ProverOutcome::ProverError { detail, .. }
                    | ProverOutcome::SystemError { detail } => Some(detail.clone()),
                    _ => None,
                },
            })
            .collect();
        let categorical = PortfolioSolver::with_defaults().reconcile(&solver_results);

        // Policy layer — fuse the verdict.
        let (verdict, verified, conflict, posterior, belief, policy_needs_review) = match self
            .policy
        {
            ArbitrationPolicy::Portfolio => {
                let verdict = match categorical.verified {
                    Some(true) => Verdict::Proven,
                    Some(false) => Verdict::Refuted,
                    None if matches!(categorical.confidence, PortfolioConfidence::AllTimedOut) => {
                        Verdict::Timeout
                    },
                    None => Verdict::Unknown,
                };
                let conclusive =
                    categorical.agreeing_solvers.len() + categorical.disagreeing_solvers.len();
                let conflict = if conclusive == 0 {
                    0.0
                } else {
                    categorical.disagreeing_solvers.len() as f64 / conclusive as f64
                };
                (
                    verdict,
                    categorical.verified,
                    conflict,
                    None,
                    None,
                    categorical.needs_review,
                )
            },
            ArbitrationPolicy::Bayesian { prior_p_true } => {
                let evidence: Vec<ProverEvidence> = attempts
                    .iter()
                    .map(|a| ProverEvidence {
                        prover: a.prover,
                        verdict: outcome_to_verdict(&a.outcome),
                        time_ms: a.elapsed_ms,
                        confidence_self_reported: None,
                    })
                    .collect();
                let post = BayesianArbiter::new(prior_p_true).combine(&evidence);
                let verdict = post.winning;
                let verified = match verdict {
                    Verdict::Proven => Some(true),
                    Verdict::Refuted => Some(false),
                    _ => None,
                };
                // Normalise 3-outcome entropy to [0, 1].
                let conflict = (post.entropy_bits / 3f64.log2()).clamp(0.0, 1.0);
                let needs_review = !categorical.disagreeing_solvers.is_empty()
                    || matches!(
                        verdict,
                        Verdict::Unknown | Verdict::Timeout | Verdict::Error
                    );
                (verdict, verified, conflict, Some(post), None, needs_review)
            },
            ArbitrationPolicy::DempsterShafer => {
                let mut ds = DempsterShaferArbiter::new();
                for a in attempts {
                    let mass = match outcome_to_verdict(&a.outcome) {
                        Verdict::Proven => proven_mass(a.elapsed_ms, self.timeout_ms),
                        Verdict::Refuted => refuted_mass(a.elapsed_ms, self.timeout_ms),
                        _ => MassFunction::ignorance(),
                    };
                    ds.submit(a.prover, mass);
                }
                match ds.combine_all() {
                    Ok(bp) => {
                        let (verdict, verified) = if bp.belief_proven > bp.belief_refuted
                            && bp.belief_proven > 0.5
                        {
                            (Verdict::Proven, Some(true))
                        } else if bp.belief_refuted > bp.belief_proven && bp.belief_refuted > 0.5 {
                            (Verdict::Refuted, Some(false))
                        } else {
                            (Verdict::Unknown, None)
                        };
                        let conflict = bp.conflict_k.clamp(0.0, 1.0);
                        let needs_review =
                            !categorical.disagreeing_solvers.is_empty() || verified.is_none();
                        (verdict, verified, conflict, None, Some(bp), needs_review)
                    },
                    Err(ArbiterError::HighConflict(k)) => {
                        (Verdict::Unknown, None, k.clamp(0.0, 1.0), None, None, true)
                    },
                    Err(_) => (Verdict::Unknown, None, 0.0, None, None, true),
                }
            },
        };

        // Agreement partition relative to the winning verdict.
        let mut agreeing = Vec::new();
        let mut disagreeing = Vec::new();
        let mut inconclusive = Vec::new();
        for a in attempts {
            match (outcome_to_verdict(&a.outcome), verdict) {
                (Verdict::Proven, Verdict::Proven) | (Verdict::Refuted, Verdict::Refuted) => {
                    agreeing.push(a.prover)
                },
                (Verdict::Proven, Verdict::Refuted) | (Verdict::Refuted, Verdict::Proven) => {
                    disagreeing.push(a.prover)
                },
                (Verdict::Proven | Verdict::Refuted, _) => {
                    // No winning conclusive verdict — conclusive attempts
                    // that couldn't be fused count as disagreement camps.
                    disagreeing.push(a.prover)
                },
                _ => inconclusive.push(a.prover),
            }
        }

        // Pareto refinement: among the agreeing attempts, prefer the
        // non-dominated one (latency-driven until axiom cost and
        // certificate size are threaded through).
        let winning_outcomes: Vec<AttemptOutcome> = attempts
            .iter()
            .filter(|a| agreeing.contains(&a.prover))
            .map(|a| AttemptOutcome {
                prover: a.prover,
                verdict,
                confidence: 1.0,
                latency_ms: a.elapsed_ms,
                axiom_cost: 0,
                certificate_size_bytes: 0,
            })
            .collect();
        let recommended = ParetoArbiter::new()
            .arbitrate(&winning_outcomes)
            .recommended
            .map(|o| o.prover);

        // Fidelity level over the fused attempts — the ones whose
        // conclusive verdict is the winning one.
        let needs_review = policy_needs_review || suspect_premises;
        let fused: Vec<&ProverAttempt> = attempts
            .iter()
            .filter(|a| {
                matches!(verdict, Verdict::Proven | Verdict::Refuted)
                    && outcome_to_verdict(&a.outcome) == verdict
            })
            .collect();
        let mut retracted: Vec<ProverKind> = Vec::new();
        for a in &fused {
            if self.retracted.contains(&a.prover) && !retracted.contains(&a.prover) {
                retracted.push(a.prover);
            }
        }
        let (level, warranted_term) =
            fidelity_level(attempts, &fused, needs_review || !retracted.is_empty());

        ArbitratedVerdict {
            verdict,
            verified,
            confidence: categorical.confidence,
            agreeing,
            disagreeing,
            inconclusive,
            needs_review,
            conflict,
            suspect_premises,
            posterior,
            belief,
            recommended,
            policy: self.policy,
            level,
            retracted,
            warranted_term,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn proved(prover: ProverKind, elapsed_ms: u64) -> ProverAttempt {
        ProverAttempt::new(prover, ProverOutcome::Proved { elapsed_ms }, elapsed_ms)
    }

    fn no_proof(prover: ProverKind, elapsed_ms: u64) -> ProverAttempt {
        ProverAttempt::new(
            prover,
            ProverOutcome::NoProofFound {
                elapsed_ms,
                reason: None,
            },
            elapsed_ms,
        )
    }

    fn timeout(prover: ProverKind) -> ProverAttempt {
        ProverAttempt::new(prover, ProverOutcome::Timeout { limit_secs: 300 }, 300_000)
    }

    fn arbiter(policy: ArbitrationPolicy) -> ResultArbiter {
        ResultArbiter::new(policy, 300_000)
    }

    #[test]
    fn unanimous_proven_is_cross_checked() {
        let v = arbiter(ArbitrationPolicy::Portfolio).arbitrate(&[
            proved(ProverKind::Z3, 100),
            proved(ProverKind::CVC5, 200),
            proved(ProverKind::Vampire, 400),
        ]);
        assert_eq!(v.verdict, Verdict::Proven);
        assert_eq!(v.verified, Some(true));
        assert_eq!(v.confidence, PortfolioConfidence::CrossChecked);
        assert_eq!(v.agreeing.len(), 3);
        assert!(v.disagreeing.is_empty());
        assert!(!v.needs_review);
        assert_eq!(v.conflict, 0.0);
    }

    #[test]
    fn proven_vs_refuted_conflict_is_flagged_not_flattened() {
        let v = arbiter(ArbitrationPolicy::Portfolio)
            .arbitrate(&[proved(ProverKind::Z3, 100), no_proof(ProverKind::CVC5, 200)]);
        assert_eq!(v.verified, None, "disagreement must not yield a verdict");
        assert!(v.needs_review);
        assert_eq!(v.confidence, PortfolioConfidence::Inconclusive);
        // Both camps are named, neither silently dropped.
        assert_eq!(v.agreeing.len() + v.disagreeing.len(), 2);
        assert!(v.conflict > 0.0);
    }

    #[test]
    fn timeout_is_no_information_not_disagreement() {
        let v = arbiter(ArbitrationPolicy::Portfolio).arbitrate(&[
            proved(ProverKind::Z3, 100),
            proved(ProverKind::CVC5, 200),
            timeout(ProverKind::Vampire),
        ]);
        assert_eq!(v.verified, Some(true));
        assert_eq!(v.confidence, PortfolioConfidence::CrossChecked);
        assert_eq!(v.inconclusive, vec![ProverKind::Vampire]);
        assert!(!v.needs_review);
    }

    #[test]
    fn all_timed_out_needs_review() {
        let v = arbiter(ArbitrationPolicy::Portfolio)
            .arbitrate(&[timeout(ProverKind::Z3), timeout(ProverKind::CVC5)]);
        assert_eq!(v.verdict, Verdict::Timeout);
        assert_eq!(v.verified, None);
        assert!(v.needs_review);
        assert_eq!(v.confidence, PortfolioConfidence::AllTimedOut);
    }

    #[test]
    fn inconsistent_premises_taints_the_verdict() {
        let v = arbiter(ArbitrationPolicy::Portfolio).arbitrate(&[
            proved(ProverKind::Z3, 100),
            ProverAttempt::new(
                ProverKind::CVC5,
                ProverOutcome::InconsistentPremises { detail: None },
                50,
            ),
        ]);
        assert!(v.suspect_premises);
        assert!(v.needs_review, "suspect premises must force review");
    }

    #[test]
    fn bayesian_policy_ranks_a_verdict_under_disagreement() {
        let v = arbiter(ArbitrationPolicy::Bayesian { prior_p_true: 0.5 })
            .arbitrate(&[proved(ProverKind::Z3, 100), no_proof(ProverKind::Coq, 200)]);
        // Coq's higher default precision should outweigh Z3.
        assert_eq!(v.verdict, Verdict::Refuted);
        assert!(v.needs_review, "disagreement still flags review");
        assert!(v.posterior.is_some());
        assert!(v.conflict > 0.0, "entropy should be non-zero on a 1-vs-1");
    }

    #[test]
    fn dempster_shafer_high_conflict_refuses_to_arbitrate() {
        // Fast, near-certain, opposed singletons -> conflict trips.
        let v = arbiter(ArbitrationPolicy::DempsterShafer).arbitrate(&[
            proved(ProverKind::Z3, 100),
            no_proof(ProverKind::Coq, 100),
            proved(ProverKind::Lean, 100),
            no_proof(ProverKind::Agda, 100),
        ]);
        assert_eq!(v.verified, None);
        assert!(v.needs_review);
        assert!(v.conflict > 0.5);
    }

    #[test]
    fn dempster_shafer_agreement_yields_high_belief() {
        let v = arbiter(ArbitrationPolicy::DempsterShafer)
            .arbitrate(&[proved(ProverKind::Z3, 100), proved(ProverKind::CVC5, 200)]);
        assert_eq!(v.verified, Some(true));
        let bp = v.belief.expect("belief populated under DS policy");
        assert!(bp.belief_proven > 0.9);
        assert!(!v.needs_review);
    }

    #[test]
    fn pareto_recommendation_prefers_fastest_agreeing_prover() {
        let v = arbiter(ArbitrationPolicy::Portfolio).arbitrate(&[
            proved(ProverKind::Vampire, 5_000),
            proved(ProverKind::Z3, 120),
            proved(ProverKind::CVC5, 900),
        ]);
        assert_eq!(v.recommended, Some(ProverKind::Z3));
    }

    #[test]
    fn empty_attempts_are_inconclusive() {
        let v = arbiter(ArbitrationPolicy::Portfolio).arbitrate(&[]);
        assert_eq!(v.verified, None);
        assert!(v.needs_review);
    }

    #[test]
    fn arbitrated_verdict_round_trips_serde() {
        let v = arbiter(ArbitrationPolicy::Portfolio)
            .arbitrate(&[proved(ProverKind::Z3, 100), no_proof(ProverKind::CVC5, 200)]);
        let json = serde_json::to_string(&v).unwrap();
        let back: ArbitratedVerdict = serde_json::from_str(&json).unwrap();
        assert_eq!(back.verified, v.verified);
        assert_eq!(back.needs_review, v.needs_review);
    }

    // --- ECH-05 fidelity level -------------------------------------------

    fn kernel(term_hash: &str) -> FidelityEvidence {
        FidelityEvidence::KernelTranslation {
            format: ExchangeFormat::Dedukti,
            checked_by: ProverKind::Dedukti,
            term_hash: term_hash.into(),
        }
    }

    fn correspondence(consequence_tests: u32, failures: u32) -> FidelityEvidence {
        FidelityEvidence::DeclaredCorrespondence {
            consequence_tests,
            failures,
        }
    }

    fn level_of(attempts: &[ProverAttempt]) -> ArbitratedVerdict {
        arbiter(ArbitrationPolicy::Portfolio).arbitrate(attempts)
    }

    #[test]
    fn no_fidelity_evidence_is_belief() {
        let v = level_of(&[proved(ProverKind::Z3, 100), proved(ProverKind::CVC5, 200)]);
        assert_eq!(v.confidence, PortfolioConfidence::CrossChecked);
        assert_eq!(v.level, EpistemicLevel::Belief);
        assert_eq!(v.warranted_term, None);
    }

    #[test]
    fn kernel_translations_to_one_term_are_sound() {
        let v = level_of(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            proved(ProverKind::Isabelle, 1_200).with_fidelity(kernel("h1")),
        ]);
        assert_eq!(v.level, EpistemicLevel::Sound);
        assert_eq!(v.warranted_term.as_deref(), Some("h1"));
    }

    #[test]
    fn kernel_translations_to_different_terms_are_belief() {
        let v = level_of(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            proved(ProverKind::Isabelle, 1_200).with_fidelity(kernel("h2")),
        ]);
        assert_eq!(v.verified, Some(true), "numeric fusion is untouched");
        assert_eq!(v.level, EpistemicLevel::Belief);
    }

    #[test]
    fn empty_term_hash_is_not_a_certificate() {
        let v = level_of(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("")),
            proved(ProverKind::Isabelle, 1_200).with_fidelity(kernel("")),
        ]);
        assert_eq!(v.level, EpistemicLevel::Belief);
    }

    #[test]
    fn tested_correspondence_without_failures_is_epi() {
        let v = level_of(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            proved(ProverKind::Coq, 1_100).with_fidelity(correspondence(12, 0)),
        ]);
        assert_eq!(v.level, EpistemicLevel::Epi);
        assert_eq!(v.warranted_term, None);
    }

    #[test]
    fn failed_or_untested_correspondence_is_belief() {
        for evidence in [correspondence(12, 1), correspondence(0, 0)] {
            let v = level_of(&[
                proved(ProverKind::Lean, 900).with_fidelity(correspondence(12, 0)),
                proved(ProverKind::Coq, 1_100).with_fidelity(evidence),
            ]);
            assert_eq!(v.level, EpistemicLevel::Belief);
        }
    }

    #[test]
    fn any_attempt_without_evidence_caps_at_belief() {
        // The timed-out attempt is not fused, but it carries no evidence.
        let v = level_of(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            proved(ProverKind::Isabelle, 1_200).with_fidelity(kernel("h1")),
            timeout(ProverKind::Vampire),
        ]);
        assert_eq!(v.verified, Some(true));
        assert_eq!(v.level, EpistemicLevel::Belief);
    }

    #[test]
    fn a_verdict_needing_review_is_belief() {
        let v = arbiter(ArbitrationPolicy::Bayesian { prior_p_true: 0.5 }).arbitrate(&[
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            no_proof(ProverKind::Coq, 200).with_fidelity(kernel("h1")),
        ]);
        assert!(v.needs_review);
        assert_eq!(v.level, EpistemicLevel::Belief);
    }

    #[test]
    fn retracting_a_fused_backend_lowers_the_level() {
        let attempts = [
            proved(ProverKind::Lean, 900).with_fidelity(kernel("h1")),
            proved(ProverKind::Isabelle, 1_200).with_fidelity(kernel("h1")),
        ];
        let mut a = arbiter(ArbitrationPolicy::Portfolio);
        assert_eq!(a.arbitrate(&attempts).level, EpistemicLevel::Sound);

        a.retract(ProverKind::Lean);
        a.retract(ProverKind::Lean);
        assert_eq!(a.retracted(), &[ProverKind::Lean]);
        let v = a.arbitrate(&attempts);
        assert_eq!(v.level, EpistemicLevel::Belief);
        assert_eq!(v.retracted, vec![ProverKind::Lean]);
        assert_eq!(v.verified, Some(true), "numeric fusion is untouched");
    }

    #[test]
    fn levels_are_ordered() {
        assert!(EpistemicLevel::Belief < EpistemicLevel::Epi);
        assert!(EpistemicLevel::Epi < EpistemicLevel::Sound);
    }

    #[test]
    fn pre_ech05_json_reads_back_at_belief() {
        let attempt: ProverAttempt = serde_json::from_str(
            r#"{"prover":"Z3","outcome":{"status":"PROVED","elapsed_ms":5},"elapsed_ms":5}"#,
        )
        .unwrap();
        assert_eq!(attempt.fidelity, FidelityEvidence::None);

        let v = level_of(&[proved(ProverKind::Z3, 100)]);
        let mut json = serde_json::to_value(&v).unwrap();
        let obj = json.as_object_mut().unwrap();
        for k in ["level", "retracted", "warranted_term"] {
            obj.remove(k);
        }
        let back: ArbitratedVerdict = serde_json::from_value(json).unwrap();
        assert_eq!(back.level, EpistemicLevel::Belief);
        assert!(back.retracted.is_empty());
    }
}
