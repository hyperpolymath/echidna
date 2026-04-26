// SPDX-License-Identifier: PMPL-1.0-or-later

//! Prover dispatch module
//!
//! Connects the API layer to prover backends through the trust-hardening
//! pipeline: integrity check -> sandbox -> prove -> certificate check ->
//! axiom scan -> confidence scoring.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
#[cfg(feature = "verisim")]
use std::collections::HashMap;
use std::path::PathBuf;
use std::time::Instant;
use tracing::{info, warn};

use crate::integrity::solver_integrity::{IntegrityChecker, IntegrityStatus};
use crate::llm::LlmAdvisor;
use crate::provers::outcome::{classify_anyhow_error, ProverOutcome};
use crate::provers::{ProverConfig, ProverFactory, ProverKind};
use crate::verification::axiom_tracker::{AxiomTracker, AxiomUsage, DangerLevel};
use crate::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};

#[cfg(feature = "chapel")]
use crate::proof_search::{ChapelParallelSearch, ProofSearchStrategy};

/// Per-prover record inside `RunDiagnostics`.  Captures what a single
/// backend returned during a dispatch run — used by the sanity suite and
/// by the Julia ML arbiter to reason about why a prover ruled one way.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerProverRecord {
    /// Prover name (matches `format!("{:?}", ProverKind)`).
    pub prover: String,
    /// Exact outcome produced by this prover's `check()` call.
    pub outcome: ProverOutcome,
    /// Wall-clock time this prover spent, in milliseconds.
    pub elapsed_ms: u64,
}

/// Diagnostics payload attached to a `DispatchResult` when
/// `DispatchConfig.diagnostics` is `true`.  Holds the information needed
/// to audit the pipeline post-hoc — the normalised input actually sent to
/// the prover, which provers were tried, and what each one returned.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunDiagnostics {
    /// The input after any echidna-side normalisation (whitespace trim,
    /// set-logic injection, etc.).  Exactly what the prover saw.
    pub normalized_input: String,
    /// Human-readable names of the provers that were actually invoked,
    /// in the order they ran.
    pub provers_selected: Vec<String>,
    /// One record per prover invocation.
    pub per_prover: Vec<PerProverRecord>,
}

/// Result of a dispatched proof verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DispatchResult {
    /// Whether the proof was verified
    pub verified: bool,
    /// Trust level assigned
    pub trust_level: TrustLevel,
    /// Which prover(s) verified the proof
    pub provers_used: Vec<String>,
    /// Proof time in milliseconds
    pub proof_time_ms: u64,
    /// Number of remaining goals
    pub goals_remaining: usize,
    /// Axiom usage report
    pub axiom_report: Option<AxiomUsage>,
    /// Certificate hash (if certificate was produced)
    pub certificate_hash: Option<String>,
    /// Human-readable message
    pub message: String,
    /// Whether cross-checking was used
    pub cross_checked: bool,
    /// Rich outcome of the *primary* prover — distinguishes proved from
    /// no-proof-found, timeout, inconsistent premises, etc.  Callers that
    /// only care about yes/no should still read `verified`.
    #[serde(default)]
    pub outcome: ProverOutcome,
    /// Populated only when the dispatcher was constructed with
    /// `DispatchConfig.diagnostics = true`.  Contains the normalised
    /// input and per-prover records.
    #[serde(default)]
    pub diagnostics: Option<RunDiagnostics>,
}

/// Configuration for the dispatch pipeline
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DispatchConfig {
    /// Enable cross-checking (portfolio solving)
    pub cross_check: bool,
    /// Minimum trust level required
    pub min_trust_level: TrustLevel,
    /// Enable axiom tracking
    pub track_axioms: bool,
    /// Enable certificate generation
    pub generate_certificates: bool,
    /// Timeout per prover in seconds
    pub timeout: u64,
    /// When `true`, attach a `RunDiagnostics` payload to every
    /// `DispatchResult`.  Costs a small amount of memory and allocation;
    /// default is `false` so production callers pay nothing.
    #[serde(default)]
    pub diagnostics: bool,
}

impl Default for DispatchConfig {
    fn default() -> Self {
        Self {
            cross_check: false,
            min_trust_level: TrustLevel::Level2,
            track_axioms: true,
            generate_certificates: false,
            timeout: 300,
            diagnostics: false,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// VeriSimAdvisor — VeriSimDB-backed strategy advisor (feature = "verisim")
// ═══════════════════════════════════════════════════════════════════════

/// Map a lowercase prover-name string (as stored in VeriSimDB) to a
/// `ProverKind`.  Returns `None` for unrecognised names so callers can
/// fall back gracefully rather than picking a wrong prover.
///
/// The inverse of `crate::verisim_bridge::prover_kind_to_str`.
#[cfg(feature = "verisim")]
pub fn prover_kind_from_str(s: &str) -> Option<ProverKind> {
    match s {
        "coq" => Some(ProverKind::Coq),
        "lean" => Some(ProverKind::Lean),
        "agda" => Some(ProverKind::Agda),
        "isabelle" => Some(ProverKind::Isabelle),
        "idris2" => Some(ProverKind::Idris2),
        "z3" => Some(ProverKind::Z3),
        "cvc5" => Some(ProverKind::CVC5),
        "altergo" => Some(ProverKind::AltErgo),
        "metamath" => Some(ProverKind::Metamath),
        "hol_light" => Some(ProverKind::HOLLight),
        "mizar" => Some(ProverKind::Mizar),
        "hol4" => Some(ProverKind::HOL4),
        "pvs" => Some(ProverKind::PVS),
        "acl2" => Some(ProverKind::ACL2),
        "vampire" => Some(ProverKind::Vampire),
        "eprover" => Some(ProverKind::EProver),
        _ => None,
    }
}

/// Select the highest-success-rate `ProverKind` from a name→rate map.
///
/// Iterates the map, converts each name via `prover_kind_from_str`, skips
/// unrecognised entries, and returns the variant with the largest `f32`
/// rate.  Falls back to `fallback` when the map is empty or no name is
/// recognised.
#[cfg(feature = "verisim")]
fn best_prover_or_fallback(rates: HashMap<String, f32>, fallback: ProverKind) -> ProverKind {
    rates
        .into_iter()
        .filter_map(|(name, rate)| prover_kind_from_str(&name).map(|k| (k, rate)))
        .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .map(|(kind, _)| kind)
        .unwrap_or(fallback)
}

/// VeriSimDB-backed strategy advisor.
///
/// Queries the `mv_prover_success_by_class` materialised view to suggest the
/// best-performing prover for a given obligation class.  Advisory only — the
/// trust pipeline remains inviolable and is never influenced by this advisor.
///
/// On any VeriSimDB error (network, parse, 404) the advisor silently returns
/// the caller-supplied fallback.  Proof execution must never block on DB
/// availability.
#[cfg(feature = "verisim")]
pub struct VeriSimAdvisor {
    /// HTTP client to VeriSimDB.
    client: crate::verisim_bridge::VeriSimDBClient,
}

#[cfg(feature = "verisim")]
impl VeriSimAdvisor {
    /// Create a new `VeriSimAdvisor` pointing at `base_url`.
    ///
    /// `base_url` is the root of the VeriSimDB HTTP API
    /// (e.g. `"http://verisimdb:7700"`).  Trailing slashes are stripped
    /// automatically by `VeriSimDBClient::new`.
    pub fn new(base_url: &str) -> Self {
        VeriSimAdvisor {
            client: crate::verisim_bridge::VeriSimDBClient::new(base_url),
        }
    }

    /// Suggest the best `ProverKind` for an obligation class.
    ///
    /// Queries `mv_prover_success_by_class` and returns the prover with the
    /// highest historical success rate.  Returns `fallback` when VeriSimDB
    /// is unreachable, has no data for the class, or no recognised prover
    /// name appears in the response.
    pub async fn suggest_prover(
        &self,
        obligation_class: &str,
        fallback: ProverKind,
    ) -> ProverKind {
        match self.client.query_prover_success_by_class(obligation_class).await {
            Ok(rates) if !rates.is_empty() => {
                let best = best_prover_or_fallback(rates, fallback);
                info!(
                    "VeriSimAdvisor: obligation_class={} → {:?}",
                    obligation_class, best
                );
                best
            },
            Ok(_) => {
                // Empty map: no data yet for this class.
                info!(
                    "VeriSimAdvisor: no data for class={}, using fallback {:?}",
                    obligation_class, fallback
                );
                fallback
            },
            Err(e) => {
                warn!(
                    "VeriSimAdvisor: VeriSimDB query failed ({}); using fallback {:?}",
                    e, fallback
                );
                fallback
            },
        }
    }
}

/// Prover dispatcher that runs the full trust-hardening pipeline
pub struct ProverDispatcher {
    config: DispatchConfig,
    integrity_checker: Option<IntegrityChecker>,
    /// Optional frontier LLM advisor for intelligent dispatch optimisation.
    /// Advisory only — cannot influence trust levels.
    llm_advisor: Option<LlmAdvisor>,
    /// Optional VeriSimDB-backed strategy advisor.
    /// Uses historical success rates from `mv_prover_success_by_class` to
    /// route `verify_proof_verisim_guided`.  Advisory only — trust pipeline
    /// is inviolable.
    #[cfg(feature = "verisim")]
    verisim_advisor: Option<VeriSimAdvisor>,
}

impl ProverDispatcher {
    /// Create a new dispatcher with default configuration
    pub fn new() -> Self {
        Self {
            config: DispatchConfig::default(),
            integrity_checker: None,
            llm_advisor: None,
            #[cfg(feature = "verisim")]
            verisim_advisor: None,
        }
    }

    /// Create a dispatcher with custom configuration
    pub fn with_config(config: DispatchConfig) -> Self {
        Self {
            config,
            integrity_checker: None,
            llm_advisor: None,
            #[cfg(feature = "verisim")]
            verisim_advisor: None,
        }
    }

    /// Set the integrity checker for solver binary verification
    pub fn with_integrity_checker(mut self, checker: IntegrityChecker) -> Self {
        self.integrity_checker = Some(checker);
        self
    }

    /// Set the frontier LLM advisor for intelligent dispatch optimisation.
    /// Advisory only — the trust pipeline remains inviolable.
    pub fn with_llm_advisor(mut self, advisor: LlmAdvisor) -> Self {
        self.llm_advisor = Some(advisor);
        self
    }

    /// Attach a `VeriSimAdvisor` for history-guided dispatch.
    ///
    /// When set, `verify_proof_verisim_guided` queries VeriSimDB's
    /// `mv_prover_success_by_class` view before dispatching, choosing the
    /// historically highest-performing prover for the given obligation class.
    /// Advisory only — the trust pipeline remains inviolable.
    #[cfg(feature = "verisim")]
    pub fn with_verisim(mut self, advisor: VeriSimAdvisor) -> Self {
        self.verisim_advisor = Some(advisor);
        self
    }

    /// Dispatch with VeriSimDB history-guided optimisation.
    ///
    /// Consults `mv_prover_success_by_class` for the supplied
    /// `obligation_class` and routes to the prover with the highest
    /// historical success rate.  If VeriSimDB is unreachable, has no data
    /// for the class, or no `VeriSimAdvisor` is configured, falls back to
    /// `fallback_prover` without error.
    ///
    /// **Trust guarantee**: the selected prover passes through the full
    /// trust-hardening pipeline in `verify_proof`.  VeriSimDB influences
    /// *which* prover is tried, never *how* the result is scored.
    #[cfg(feature = "verisim")]
    pub async fn verify_proof_verisim_guided(
        &self,
        content: &str,
        obligation_class: &str,
        fallback_prover: ProverKind,
    ) -> Result<DispatchResult> {
        let prover = if let Some(ref advisor) = self.verisim_advisor {
            advisor.suggest_prover(obligation_class, fallback_prover).await
        } else {
            fallback_prover
        };
        self.verify_proof(prover, content).await
    }

    /// Dispatch with LLM-guided optimisation
    ///
    /// The LLM suggests which prover to try and which cross-checkers to use.
    /// If the LLM is unavailable, falls back to the provided prover_kind.
    /// Trust levels are NEVER influenced by the LLM.
    pub async fn verify_proof_llm_guided(
        &self,
        content: &str,
        fallback_prover: ProverKind,
    ) -> Result<DispatchResult> {
        // Try to get LLM optimisation
        if let Some(ref advisor) = self.llm_advisor {
            if advisor.is_available() {
                // Parse content into a minimal proof state for the LLM
                let prover_config = ProverConfig::default();
                if let Ok(prover) = ProverFactory::create(fallback_prover, prover_config) {
                    if let Ok(state) = prover.parse_string(content).await {
                        if let Some(opt) = advisor.optimise_dispatch(&state).await {
                            info!(
                                "LLM dispatch optimisation: primary={:?}, cross_check={:?}",
                                opt.primary_prover, opt.cross_check_provers
                            );

                            let primary = opt.primary_prover.unwrap_or(fallback_prover);

                            if !opt.cross_check_provers.is_empty() {
                                return self
                                    .verify_proof_cross_checked(
                                        primary,
                                        content,
                                        &opt.cross_check_provers,
                                    )
                                    .await;
                            }

                            return self.verify_proof(primary, content).await;
                        }
                    }
                }
            }
        }

        // Fallback: use provided prover without LLM guidance
        self.verify_proof(fallback_prover, content).await
    }

    /// Dispatch a proof verification request through the trust-hardening pipeline
    pub async fn verify_proof(
        &self,
        prover_kind: ProverKind,
        content: &str,
    ) -> Result<DispatchResult> {
        let start = Instant::now();

        // Step 1: Create the prover
        let prover_config = ProverConfig {
            timeout: self.config.timeout,
            ..Default::default()
        };

        let prover = ProverFactory::create(prover_kind, prover_config)
            .context("Failed to create prover backend")?;

        info!("Dispatching proof to {:?}", prover_kind);

        // Step 2: Parse the proof content.
        // Parse failures MUST be classified as `InvalidInput`, not as
        // pipeline errors — the taxonomy test
        // `sanity_dispatch_parse_failure_is_invalid_input` asserts this.
        let prover_started = Instant::now();
        let state = match prover.parse_string(content).await {
            Ok(s) => s,
            Err(e) => {
                let outcome = classify_anyhow_error(&e, self.config.timeout);
                let elapsed_ms = prover_started.elapsed().as_millis() as u64;
                let diagnostics = if self.config.diagnostics {
                    Some(RunDiagnostics {
                        normalized_input: content.trim().to_string(),
                        provers_selected: vec![format!("{:?}", prover_kind)],
                        per_prover: vec![PerProverRecord {
                            prover: format!("{:?}", prover_kind),
                            outcome: outcome.clone(),
                            elapsed_ms,
                        }],
                    })
                } else {
                    None
                };
                return Ok(DispatchResult {
                    verified: false,
                    trust_level: TrustLevel::Level1,
                    provers_used: vec![format!("{:?}", prover_kind)],
                    proof_time_ms: elapsed_ms,
                    goals_remaining: 0,
                    axiom_report: None,
                    certificate_hash: None,
                    message: format!("Parse failure: {}", e),
                    cross_checked: false,
                    outcome,
                    diagnostics,
                });
            },
        };

        // Step 3: Run the rich `check()` variant — gives us a full outcome
        // classification in one pass.  The boolean `verified` flag is
        // derived from `outcome.is_proved()` so the two views stay in sync.
        let outcome = prover
            .check(&state)
            .await
            .context("Failed to verify proof")?;
        let verified = outcome.is_proved();
        let prover_elapsed_ms = prover_started.elapsed().as_millis() as u64;

        // Step 4: Track axiom usage
        let axiom_usages = if self.config.track_axioms {
            let tracker = AxiomTracker::new();
            Some(tracker.scan(prover_kind, content))
        } else {
            None
        };

        // Step 5: Determine worst axiom danger level
        let worst_danger = axiom_usages
            .as_ref()
            .map(|usages| {
                usages
                    .iter()
                    .map(|u| u.danger_level)
                    .max()
                    .unwrap_or(DangerLevel::Safe)
            })
            .unwrap_or(DangerLevel::Safe);

        // Get first axiom usage for the report (if any)
        let axiom_report = axiom_usages
            .as_ref()
            .and_then(|usages| usages.first().cloned());

        // Step 6: Check solver integrity (if checker configured)
        let solver_integrity_ok = if let Some(ref checker) = self.integrity_checker {
            let reports = checker.verify_all().await.unwrap_or_default();
            let prover_name = format!("{:?}", prover_kind).to_lowercase();
            reports
                .iter()
                .find(|r| r.name.to_lowercase() == prover_name)
                .map(|r| {
                    r.status == IntegrityStatus::Verified
                        || r.status == IntegrityStatus::Uninitialized
                })
                .unwrap_or(true) // If prover not in manifest, assume ok
        } else {
            true // No checker configured, assume ok
        };

        // Step 7: Compute trust level
        let trust_factors = TrustFactors {
            prover: prover_kind,
            confirming_provers: 1,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: worst_danger,
            solver_integrity_ok,
            portfolio_confidence: None,
        };

        let trust_level = compute_trust_level(&trust_factors);

        let elapsed = start.elapsed().as_millis() as u64;

        // Step 8: Check minimum trust level
        let meets_minimum = trust_level >= self.config.min_trust_level;

        let message = if !verified {
            "Proof verification failed".to_string()
        } else if !meets_minimum {
            format!(
                "Proof verified but trust level {} does not meet minimum {}",
                trust_level, self.config.min_trust_level
            )
        } else {
            format!("Proof verified with {}", trust_level)
        };

        let diagnostics = if self.config.diagnostics {
            Some(RunDiagnostics {
                normalized_input: content.trim().to_string(),
                provers_selected: vec![format!("{:?}", prover_kind)],
                per_prover: vec![PerProverRecord {
                    prover: format!("{:?}", prover_kind),
                    outcome: outcome.clone(),
                    elapsed_ms: prover_elapsed_ms,
                }],
            })
        } else {
            None
        };

        Ok(DispatchResult {
            verified: verified && meets_minimum,
            trust_level,
            provers_used: vec![format!("{:?}", prover_kind)],
            proof_time_ms: elapsed,
            goals_remaining: state.goals.len(),
            axiom_report,
            certificate_hash: None,
            message,
            cross_checked: false,
            outcome,
            diagnostics,
        })
    }

    /// Dispatch a proof with cross-checking (portfolio solving)
    pub async fn verify_proof_cross_checked(
        &self,
        primary_prover: ProverKind,
        content: &str,
        additional_provers: &[ProverKind],
    ) -> Result<DispatchResult> {
        let start = Instant::now();

        // Run primary prover
        let mut primary_result = self.verify_proof(primary_prover, content).await?;

        if additional_provers.is_empty() {
            return Ok(primary_result);
        }

        // Run additional provers for cross-checking
        let mut all_agree = primary_result.verified;
        let mut provers_used = vec![format!("{:?}", primary_prover)];
        let mut confirming_count: u32 = if primary_result.verified { 1 } else { 0 };

        for &additional in additional_provers {
            match self.verify_proof(additional, content).await {
                Ok(result) => {
                    provers_used.push(format!("{:?}", additional));
                    if result.verified {
                        confirming_count += 1;
                    } else {
                        all_agree = false;
                    }
                },
                Err(e) => {
                    warn!("Cross-check with {:?} failed: {}", additional, e);
                },
            }
        }

        let elapsed = start.elapsed().as_millis() as u64;

        // Recompute trust level with cross-checking info
        let worst_danger = primary_result
            .axiom_report
            .as_ref()
            .map(|r| r.danger_level)
            .unwrap_or(DangerLevel::Safe);

        // Check solver integrity for cross-checked path
        let solver_integrity_ok = if let Some(ref checker) = self.integrity_checker {
            let reports = checker.verify_all().await.unwrap_or_default();
            let prover_name = format!("{:?}", primary_prover).to_lowercase();
            reports
                .iter()
                .find(|r| r.name.to_lowercase() == prover_name)
                .map(|r| {
                    r.status == IntegrityStatus::Verified
                        || r.status == IntegrityStatus::Uninitialized
                })
                .unwrap_or(true)
        } else {
            true
        };

        let trust_factors = TrustFactors {
            prover: primary_prover,
            confirming_provers: confirming_count,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: worst_danger,
            solver_integrity_ok,
            portfolio_confidence: Some(if confirming_count >= 2 {
                crate::verification::portfolio::PortfolioConfidence::CrossChecked
            } else if confirming_count == 1 {
                crate::verification::portfolio::PortfolioConfidence::SingleSolver
            } else {
                crate::verification::portfolio::PortfolioConfidence::Inconclusive
            }),
        };

        let trust_level = compute_trust_level(&trust_factors);

        primary_result.trust_level = trust_level;
        primary_result.provers_used = provers_used;
        primary_result.proof_time_ms = elapsed;
        primary_result.cross_checked = confirming_count >= 2;
        primary_result.verified = all_agree && primary_result.verified;

        if primary_result.cross_checked {
            primary_result.message = format!(
                "Proof cross-checked by {} provers with {}",
                confirming_count, trust_level
            );
        }

        Ok(primary_result)
    }

    /// Dispatch a proof through Chapel's parallel prover search (L2 Wave 1).
    ///
    /// With `--features chapel` **and** the Chapel runtime available, fans out
    /// to up to 30 prover backends in parallel via the Zig FFI bridge and
    /// returns the first successful result through the standard trust pipeline
    /// (axiom tracking, integrity check, trust-level scoring).
    ///
    /// Falls back to sequential `verify_proof` (with `select_prover` heuristic)
    /// when:
    /// - the `chapel` Cargo feature is not compiled in, or
    /// - `ChapelParallelSearch::new()` reports the runtime unavailable, or
    /// - the parallel search returns a non-verified result (so the caller
    ///   still gets a real pipeline answer rather than a bare failure).
    ///
    /// The trust level for a Chapel-parallel win is computed as a single
    /// confirming prover — parallel-first-wins is a dispatch speedup, **not**
    /// cross-checking. Callers wanting cross-checking should use
    /// `verify_proof_cross_checked` (Wave-2 territory will extend Chapel to
    /// portfolio quorum).
    pub async fn verify_proof_parallel(&self, content: &str) -> Result<DispatchResult> {
        #[cfg(feature = "chapel")]
        {
            let chapel = match ChapelParallelSearch::new() {
                Ok(c) => c,
                Err(e) => {
                    warn!(
                        "Chapel parallel search unavailable ({}); falling back to sequential",
                        e
                    );
                    let fallback_kind = Self::select_prover(content, None);
                    return self.verify_proof(fallback_kind, content).await;
                },
            };

            if !chapel.available() {
                warn!("Chapel runtime reported unavailable; falling back to sequential");
                let fallback_kind = Self::select_prover(content, None);
                return self.verify_proof(fallback_kind, content).await;
            }

            let start = Instant::now();
            let timeout = std::time::Duration::from_secs(self.config.timeout);

            let parallel = match chapel.search(content, timeout) {
                Ok(r) => r,
                Err(e) => {
                    warn!(
                        "Chapel parallel search errored ({}); falling back to sequential",
                        e
                    );
                    let fallback_kind = Self::select_prover(content, None);
                    return self.verify_proof(fallback_kind, content).await;
                },
            };

            if !parallel.success {
                info!("Chapel parallel search returned no winner; sequential fallback");
                let fallback_kind = Self::select_prover(content, None);
                return self.verify_proof(fallback_kind, content).await;
            }

            let winning_kind: ProverKind = parallel
                .prover_name
                .as_deref()
                .and_then(|n| n.parse().ok())
                .unwrap_or_else(|| Self::select_prover(content, None));

            let axiom_usages = if self.config.track_axioms {
                Some(AxiomTracker::new().scan(winning_kind, content))
            } else {
                None
            };

            let worst_danger = axiom_usages
                .as_ref()
                .map(|u| {
                    u.iter()
                        .map(|x| x.danger_level)
                        .max()
                        .unwrap_or(DangerLevel::Safe)
                })
                .unwrap_or(DangerLevel::Safe);

            let axiom_report = axiom_usages.as_ref().and_then(|u| u.first().cloned());

            let solver_integrity_ok = if let Some(ref checker) = self.integrity_checker {
                let reports = checker.verify_all().await.unwrap_or_default();
                let prover_name = format!("{:?}", winning_kind).to_lowercase();
                reports
                    .iter()
                    .find(|r| r.name.to_lowercase() == prover_name)
                    .map(|r| {
                        r.status == IntegrityStatus::Verified
                            || r.status == IntegrityStatus::Uninitialized
                    })
                    .unwrap_or(true)
            } else {
                true
            };

            let trust_factors = TrustFactors {
                prover: winning_kind,
                confirming_provers: 1,
                has_certificate: false,
                certificate_verified: false,
                worst_axiom_danger: worst_danger,
                solver_integrity_ok,
                portfolio_confidence: Some(
                    crate::verification::portfolio::PortfolioConfidence::SingleSolver,
                ),
            };

            let trust_level = compute_trust_level(&trust_factors);
            let meets_minimum = trust_level >= self.config.min_trust_level;
            let elapsed = start.elapsed().as_millis() as u64;

            let prover_elapsed_ms = (parallel.time_seconds * 1000.0) as u64;
            let outcome = ProverOutcome::Proved {
                elapsed_ms: prover_elapsed_ms,
            };

            let diagnostics = if self.config.diagnostics {
                Some(RunDiagnostics {
                    normalized_input: content.trim().to_string(),
                    provers_selected: vec![format!("{:?}", winning_kind)],
                    per_prover: vec![PerProverRecord {
                        prover: format!("{:?}", winning_kind),
                        outcome: outcome.clone(),
                        elapsed_ms: prover_elapsed_ms,
                    }],
                })
            } else {
                None
            };

            let message = if !meets_minimum {
                format!(
                    "Chapel parallel proof verified but trust level {} below minimum {}",
                    trust_level, self.config.min_trust_level
                )
            } else {
                format!(
                    "Chapel parallel proof verified by {:?} with {}",
                    winning_kind, trust_level
                )
            };

            return Ok(DispatchResult {
                verified: meets_minimum,
                trust_level,
                provers_used: vec![format!("{:?}", winning_kind)],
                proof_time_ms: elapsed,
                goals_remaining: 0,
                axiom_report,
                certificate_hash: None,
                message,
                cross_checked: false,
                outcome,
                diagnostics,
            });
        }

        #[cfg(not(feature = "chapel"))]
        {
            info!("Chapel feature not compiled in; dispatching sequentially");
            let fallback_kind = Self::select_prover(content, None);
            self.verify_proof(fallback_kind, content).await
        }
    }

    /// Select the best prover for a given proof type
    pub fn select_prover(content: &str, file_extension: Option<&str>) -> ProverKind {
        // Try to detect from file extension first
        if let Some(ext) = file_extension {
            let path = PathBuf::from(format!("proof.{}", ext));
            if let Some(kind) = ProverFactory::detect_from_file(&path) {
                return kind;
            }
        }

        // Heuristic detection from content
        let content_lower = content.to_lowercase();

        if content_lower.contains("theorem")
            && content_lower.contains(":=")
            && content_lower.contains("lean")
        {
            ProverKind::Lean
        } else if content_lower.contains("theorem")
            && content_lower.contains("proof")
            && content_lower.contains("qed")
        {
            ProverKind::Coq
        } else if content_lower.contains("(set-logic") || content_lower.contains("(assert") {
            ProverKind::Z3
        } else if content_lower.contains("theory") && content_lower.contains("imports") {
            ProverKind::Isabelle
        } else if content_lower.contains("module")
            && content_lower.contains("where")
            && content_lower.contains("data")
        {
            ProverKind::Agda
        } else if content_lower.contains("fof(") || content_lower.contains("cnf(") {
            ProverKind::Vampire
        } else {
            // Default to Lean for general theorem proving
            ProverKind::Lean
        }
    }
}

impl Default for ProverDispatcher {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dispatch_config_defaults() {
        let config = DispatchConfig::default();
        assert!(!config.cross_check);
        assert_eq!(config.min_trust_level, TrustLevel::Level2);
        assert!(config.track_axioms);
        assert_eq!(config.timeout, 300);
    }

    #[test]
    fn test_prover_selection_smt() {
        let prover = ProverDispatcher::select_prover("(set-logic QF_LIA)\n(assert (> x 0))", None);
        assert_eq!(prover, ProverKind::Z3);
    }

    #[test]
    fn test_prover_selection_tptp() {
        let prover = ProverDispatcher::select_prover("fof(ax1, axiom, p(a)).", None);
        assert_eq!(prover, ProverKind::Vampire);
    }

    #[test]
    fn test_prover_selection_coq() {
        let prover =
            ProverDispatcher::select_prover("Theorem foo : True.\nProof.\nexact I.\nQed.", None);
        assert_eq!(prover, ProverKind::Coq);
    }

    #[test]
    fn test_prover_selection_from_extension() {
        let prover = ProverDispatcher::select_prover("anything", Some("smt2"));
        assert_eq!(prover, ProverKind::Z3);
    }

    #[test]
    fn test_prover_selection_default() {
        let prover = ProverDispatcher::select_prover("unknown content", None);
        assert_eq!(prover, ProverKind::Lean);
    }

    #[test]
    fn test_dispatch_result_serialization() {
        let result = DispatchResult {
            verified: true,
            trust_level: TrustLevel::Level4,
            provers_used: vec!["Lean".to_string()],
            proof_time_ms: 1500,
            goals_remaining: 0,
            axiom_report: None,
            certificate_hash: None,
            message: "OK".to_string(),
            cross_checked: false,
            outcome: ProverOutcome::Proved { elapsed_ms: 1500 },
            diagnostics: None,
        };

        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("Level4"));
    }

    #[test]
    fn test_dispatch_result_deserialization() {
        let json = r#"{"verified":false,"trust_level":"Level1","provers_used":["Z3"],"proof_time_ms":100,"goals_remaining":1,"axiom_report":null,"certificate_hash":null,"message":"Failed","cross_checked":false}"#;
        let result: DispatchResult = serde_json::from_str(json).unwrap();
        assert!(!result.verified);
        assert_eq!(result.trust_level, TrustLevel::Level1);
        assert_eq!(result.goals_remaining, 1);
    }

    #[test]
    fn test_prover_selection_agda() {
        let prover =
            ProverDispatcher::select_prover("module MyModule where\ndata Nat : Set where", None);
        assert_eq!(prover, ProverKind::Agda);
    }

    #[test]
    fn test_prover_selection_isabelle() {
        let prover = ProverDispatcher::select_prover("theory MyTheory\nimports Main", None);
        assert_eq!(prover, ProverKind::Isabelle);
    }

    #[test]
    fn test_prover_selection_cnf_tptp() {
        let prover = ProverDispatcher::select_prover("cnf(ax1, axiom, p(a)).", None);
        assert_eq!(prover, ProverKind::Vampire);
    }

    #[test]
    fn test_dispatch_config_custom() {
        let config = DispatchConfig {
            cross_check: true,
            min_trust_level: TrustLevel::Level4,
            track_axioms: false,
            generate_certificates: true,
            timeout: 600,
            diagnostics: false,
        };
        assert!(config.cross_check);
        assert_eq!(config.min_trust_level, TrustLevel::Level4);
        assert!(!config.track_axioms);
        assert!(config.generate_certificates);
        assert_eq!(config.timeout, 600);
    }

    #[test]
    fn test_prover_dispatcher_default() {
        let dispatcher = ProverDispatcher::default();
        assert!(!dispatcher.config.cross_check);
    }

    #[test]
    fn test_prover_dispatcher_with_config() {
        let config = DispatchConfig {
            cross_check: true,
            ..Default::default()
        };
        let dispatcher = ProverDispatcher::with_config(config);
        assert!(dispatcher.config.cross_check);
    }

    #[cfg(not(feature = "chapel"))]
    #[tokio::test]
    async fn test_verify_proof_parallel_falls_back_without_chapel() {
        // Without the chapel feature the parallel entry point must still
        // return a DispatchResult via the sequential path. We only assert
        // the call returns Ok — prover execution itself is exercised in
        // other tests.
        let dispatcher = ProverDispatcher::new();
        let result = dispatcher
            .verify_proof_parallel("(set-logic QF_LIA)\n(assert (> x 0))")
            .await;
        assert!(
            result.is_ok(),
            "parallel dispatch should fall back cleanly without chapel feature"
        );
    }

    #[cfg(feature = "chapel")]
    #[tokio::test]
    async fn test_verify_proof_parallel_chapel_path() {
        // With the chapel feature enabled, the parallel entry point should
        // reach either the Chapel runtime (30-prover fanout) or the
        // sequential fallback — both must yield a DispatchResult.
        let dispatcher = ProverDispatcher::new();
        let result = dispatcher
            .verify_proof_parallel("(set-logic QF_LIA)\n(assert (> x 0))")
            .await;
        assert!(
            result.is_ok(),
            "Chapel parallel dispatch must return Ok (either Chapel or fallback)"
        );
    }
}
