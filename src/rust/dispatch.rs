// SPDX-License-Identifier: PMPL-1.0-or-later

//! Prover dispatch module
//!
//! Connects the API layer to prover backends through the trust-hardening
//! pipeline: integrity check -> sandbox -> prove -> certificate check ->
//! axiom scan -> confidence scoring.

use anyhow::{Context, Result};
use chrono::Utc;
use serde::{Deserialize, Serialize};
#[cfg(feature = "verisim")]
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use tracing::{info, warn};

use crate::diagnostics::{HealthStatus, DegradationMode, CircuitBreakerStateSnapshot, ProverHealth};
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
    /// Optional VeriSimDB writer for closing the learning loop.
    /// When set, every `verify_proof()` exit fires a fire-and-forget
    /// `record_proof_attempt` so historical outcomes accumulate in the
    /// `proof_attempts` table that backs `mv_prover_success_by_class`.
    /// A writer outage cannot affect the trust pipeline — failures are
    /// logged at warn level and dropped.
    #[cfg(feature = "verisim")]
    verisim_writer: Option<crate::verisim_bridge::VeriSimDBClient>,
    /// Health monitoring for all provers and system components
    health_status: Arc<Mutex<HealthStatus>>,
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
            #[cfg(feature = "verisim")]
            verisim_writer: None,
            health_status: Arc::new(Mutex::new(HealthStatus::new())),
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
            #[cfg(feature = "verisim")]
            verisim_writer: None,
            health_status: Arc::new(Mutex::new(HealthStatus::new())),
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

    /// Attach a VeriSimDB writer that records every proof attempt.
    ///
    /// `base_url` is the same VeriSimDB endpoint used by `VeriSimAdvisor`
    /// (e.g. `"http://verisimdb:7700"`).  Once attached, `verify_proof()`
    /// fires `record_proof_attempt` as a `tokio::spawn` fire-and-forget at
    /// every exit (parse failure or final result), populating the table that
    /// `mv_prover_success_by_class` reads from.  This closes the loop
    /// `attempt → table → MV → VeriSimAdvisor → next dispatch`.
    ///
    /// **Trust guarantee**: the writer runs detached. A VeriSimDB outage,
    /// network partition, or 5xx response can never block, fail, or alter
    /// a dispatch result; failures are logged at warn level and dropped.
    #[cfg(feature = "verisim")]
    pub fn with_verisim_writer(mut self, base_url: &str) -> Self {
        self.verisim_writer = Some(crate::verisim_bridge::VeriSimDBClient::new(base_url));
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
        // Thread the class to the inner so the recorded ProofAttempt is
        // attributed to the right obligation_class — otherwise the very
        // statistics this dispatch consults would be polluted with
        // "unknown" rows.
        self.verify_proof_with_class(prover, content, Some(obligation_class)).await
    }

    /// Get current health status snapshot
    pub fn health_status(&self) -> HealthStatus {
        let mut health = self.health_status.lock().unwrap().clone();
        health.compute_degradation_mode();
        health
    }

    /// Update prover health metrics after a proof attempt
    pub fn record_prover_result(&self, prover_kind: ProverKind, outcome: &ProverOutcome, latency_ms: u64) {
        let mut health = self.health_status.lock().unwrap();
        let prover_name = format!("{:?}", prover_kind);

        let entry = health
            .prover_health
            .entry(prover_name.clone())
            .or_insert_with(|| ProverHealth {
                name: prover_name,
                is_available: true,
                circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                last_successful_proof: None,
                consecutive_failures: 0,
                avg_latency_ms: 0.0,
                success_rate: 0.5,
                total_invocations: 0,
                total_failures: 0,
            });

        entry.total_invocations += 1;
        entry.avg_latency_ms = (entry.avg_latency_ms * 0.8) + (latency_ms as f64 * 0.2); // EMA

        match outcome {
            ProverOutcome::Proved { .. } => {
                entry.consecutive_failures = 0;
                entry.last_successful_proof = Some(Utc::now());
                entry.is_available = true;
                entry.success_rate = (entry.success_rate * 0.9) + (1.0 * 0.1);
            }
            ProverOutcome::Timeout { .. } | ProverOutcome::ProverError { .. } | ProverOutcome::SystemError { .. } => {
                entry.consecutive_failures += 1;
                entry.total_failures += 1;
                if entry.consecutive_failures >= 3 {
                    entry.is_available = false;
                }
                entry.success_rate *= 0.9;
            }
            _ => {
                entry.total_failures += 1;
                entry.success_rate = (entry.success_rate * 0.95) + (0.0 * 0.05);
            }
        }

        entry.success_rate = entry.success_rate.clamp(0.0, 1.0);
        health.compute_degradation_mode();
    }

    /// Get current system degradation mode
    pub fn degradation_mode(&self) -> DegradationMode {
        self.health_status().system_degradation
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

    /// Dispatch a proof verification request through the trust-hardening pipeline.
    ///
    /// Public entry point. Records dispatch attempts in VeriSimDB (when
    /// `feature = "verisim"` and a writer is attached) with `obligation_class`
    /// = `"unknown"`, since the public API does not carry class metadata.
    /// Callers that *do* know the class (`verify_proof_verisim_guided`,
    /// future LLM-guided dispatch with classification) should call
    /// `verify_proof_with_class` directly.
    pub async fn verify_proof(
        &self,
        prover_kind: ProverKind,
        content: &str,
    ) -> Result<DispatchResult> {
        self.verify_proof_with_class(prover_kind, content, None).await
    }

    /// Inner dispatch implementation that takes an optional `obligation_class`
    /// for VeriSimDB attribution. Crate-private — public callers go through
    /// `verify_proof` (no class) or `verify_proof_verisim_guided` (class
    /// already known).
    pub(crate) async fn verify_proof_with_class(
        &self,
        prover_kind: ProverKind,
        content: &str,
        #[cfg_attr(not(feature = "verisim"), allow(unused_variables))]
        obligation_class: Option<&str>,
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
                self.record_prover_result(prover_kind, &outcome, elapsed_ms);
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
                #[cfg(feature = "verisim")]
                self.spawn_record_attempt(
                    prover_kind,
                    None,
                    &outcome,
                    elapsed_ms,
                    obligation_class,
                );
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
        self.record_prover_result(prover_kind, &outcome, prover_elapsed_ms);

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

        #[cfg(feature = "verisim")]
        self.spawn_record_attempt(
            prover_kind,
            state.goals.first(),
            &outcome,
            prover_elapsed_ms,
            obligation_class,
        );

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

    /// Fire a `record_proof_attempt` to VeriSimDB without blocking dispatch.
    ///
    /// No-op when `verisim_writer` is unset.  HTTP errors from VeriSimDB are
    /// logged at warn level and swallowed — the trust pipeline must never
    /// depend on the writer succeeding.  Must be called from inside a tokio
    /// runtime (the dispatch entry points are async, so this always holds).
    #[cfg(feature = "verisim")]
    fn spawn_record_attempt(
        &self,
        prover_kind: ProverKind,
        goal: Option<&crate::core::Goal>,
        outcome: &ProverOutcome,
        duration_ms: u64,
        obligation_class: Option<&str>,
    ) {
        let Some(writer) = self.verisim_writer.as_ref() else {
            return;
        };
        let attempt =
            build_proof_attempt(prover_kind, goal, outcome, duration_ms, obligation_class);
        let writer = writer.clone();
        tokio::spawn(async move {
            if let Err(e) = writer.record_proof_attempt(&attempt).await {
                warn!("VeriSim record_proof_attempt failed: {}", e);
            }
        });
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

        // CosineOnly = "use cosine for premise selection instead of GNN" — independent of
        // multi-prover cross-checking.  Only ReadOnly / Minimal (genuinely degraded, few provers
        // available) should skip cross-checking.
        let degradation = self.degradation_mode();
        match degradation {
            DegradationMode::ReadOnly | DegradationMode::Minimal => {
                return Ok(primary_result);
            }
            _ => {}
        }

        // Filter cross-checkers by health status and degradation mode
        let max_cross_checkers = match degradation {
            DegradationMode::Normal | DegradationMode::CosineOnly => additional_provers.len(),
            DegradationMode::IncreasingFallback => std::cmp::max(5, additional_provers.len() / 2),
            _ => 0, // ReadOnly / Minimal already returned above
        };

        let available_cross_checkers: Vec<ProverKind> = {
            let health = self.health_status.lock().unwrap();
            additional_provers
                .iter()
                .filter(|p| {
                    let prover_name = format!("{p:?}");
                    health
                        .prover_health
                        .get(&prover_name)
                        .is_none_or(|h| h.is_available)
                })
                .take(max_cross_checkers)
                .copied()
                .collect()
        };

        // Run additional provers for cross-checking
        let mut all_agree = primary_result.verified;
        let mut provers_used = vec![format!("{:?}", primary_prover)];
        let mut confirming_count: u32 = if primary_result.verified { 1 } else { 0 };

        for &additional in available_cross_checkers.iter() {
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

        // cross_checked = "we ran at least 2 provers for consistency" — independent of
        // whether any prover confirmed the proof.  Trust level reflects confirming_count.
        let cross_checked = provers_used.len() >= 2;

        primary_result.trust_level = trust_level;
        primary_result.provers_used = provers_used;
        primary_result.proof_time_ms = elapsed;
        primary_result.cross_checked = cross_checked;
        primary_result.verified = all_agree && primary_result.verified;

        if cross_checked {
            primary_result.message = format!(
                "Proof cross-checked by {} prover(s) with {}",
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

/// Build a `ProofAttempt` row for VeriSimDB from a dispatch outcome.
///
/// `obligation_id` uses `proof_encoding::goal_identity` so the same goal
/// produces the same hash across provers, which is what
/// `mv_prover_success_by_class` depends on for cross-prover comparison.
/// When `goal` is `None` (e.g. parse failure with no parsed state) the
/// id falls back to the literal string `"unknown"`.
#[cfg(feature = "verisim")]
fn build_proof_attempt(
    prover_kind: ProverKind,
    goal: Option<&crate::core::Goal>,
    outcome: &ProverOutcome,
    duration_ms: u64,
    obligation_class: Option<&str>,
) -> crate::verisim_bridge::ProofAttempt {
    use crate::verisim_bridge::{prover_kind_to_str, ProofAttempt};

    let now = chrono::Utc::now();
    let obligation_id = goal
        .map(|g| crate::proof_encoding::goal_identity("dispatch", g))
        .unwrap_or_else(|| "unknown".to_string());
    let claim = goal.map(|g| g.target.to_string()).unwrap_or_default();
    let outcome_str = match outcome {
        ProverOutcome::Proved { .. } => "success",
        ProverOutcome::Timeout { .. } => "timeout",
        ProverOutcome::NoProofFound { .. }
        | ProverOutcome::InvalidInput { .. }
        | ProverOutcome::InconsistentPremises { .. }
        | ProverOutcome::ProverError { .. } => "failure",
        ProverOutcome::UnsupportedFeature { .. } | ProverOutcome::SystemError { .. } => "unknown",
    };
    let confidence = if matches!(outcome, ProverOutcome::Proved { .. }) {
        1.0
    } else {
        0.0
    };
    let started_at = now - chrono::Duration::milliseconds(duration_ms as i64);

    ProofAttempt {
        attempt_id: uuid::Uuid::new_v4().to_string(),
        obligation_id,
        repo: String::new(),
        file: String::new(),
        claim,
        obligation_class: obligation_class.unwrap_or("unknown").to_string(),
        prover_used: prover_kind_to_str(prover_kind).to_string(),
        outcome: outcome_str.to_string(),
        duration_ms,
        confidence,
        parent_attempt_id: None,
        strategy_tag: "dispatch".to_string(),
        started_at: started_at.to_rfc3339(),
        completed_at: now.to_rfc3339(),
        prover_output: String::new(),
        error_message: None,
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

    // ----- VeriSim writer wiring ------------------------------------------

    #[cfg(feature = "verisim")]
    #[test]
    fn test_with_verisim_writer_attaches_client() {
        // The builder must set the `verisim_writer` field so subsequent
        // dispatch calls can fire `record_proof_attempt`. We can't exercise
        // the spawn path without a live VeriSimDB, but we can confirm the
        // writer is wired.
        let dispatcher = ProverDispatcher::new().with_verisim_writer("http://127.0.0.1:7700");
        assert!(
            dispatcher.verisim_writer.is_some(),
            "with_verisim_writer must populate the verisim_writer field"
        );
    }

    #[cfg(feature = "verisim")]
    #[test]
    fn test_build_proof_attempt_proved_outcome() {
        use crate::core::{Goal, Term};

        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Const("True".to_string()),
            hypotheses: vec![],
        };
        let outcome = ProverOutcome::Proved { elapsed_ms: 42 };

        let attempt =
            build_proof_attempt(ProverKind::Z3, Some(&goal), &outcome, 42, Some("smoke"));

        assert_eq!(attempt.outcome, "success");
        assert_eq!(attempt.confidence, 1.0);
        assert_eq!(attempt.obligation_class, "smoke");
        assert_eq!(attempt.prover_used, "z3");
        assert_eq!(attempt.duration_ms, 42);
        assert_eq!(attempt.strategy_tag, "dispatch");
        assert!(
            !attempt.obligation_id.is_empty() && attempt.obligation_id != "unknown",
            "obligation_id must be a real goal_identity hash"
        );
    }

    #[cfg(feature = "verisim")]
    #[test]
    fn test_build_proof_attempt_outcome_mapping() {
        use crate::core::{Goal, Term};

        let goal = Goal {
            id: "g0".to_string(),
            target: Term::Const("False".to_string()),
            hypotheses: vec![],
        };

        let cases: Vec<(ProverOutcome, &str)> = vec![
            (
                ProverOutcome::NoProofFound {
                    elapsed_ms: 10,
                    reason: None,
                },
                "failure",
            ),
            (
                ProverOutcome::InvalidInput {
                    reason: "syntax".to_string(),
                    location: None,
                },
                "failure",
            ),
            (ProverOutcome::Timeout { limit_secs: 30 }, "timeout"),
            (
                ProverOutcome::UnsupportedFeature {
                    feature: "uf".to_string(),
                },
                "unknown",
            ),
            (
                ProverOutcome::SystemError {
                    detail: "io".to_string(),
                },
                "unknown",
            ),
        ];

        for (outcome, expected) in cases {
            let a = build_proof_attempt(ProverKind::Z3, Some(&goal), &outcome, 10, None);
            assert_eq!(
                a.outcome, expected,
                "outcome {:?} should map to '{}'",
                outcome, expected
            );
            assert_eq!(a.confidence, 0.0, "non-Proved outcomes get confidence 0.0");
        }
    }

    #[cfg(feature = "verisim")]
    #[test]
    fn test_build_proof_attempt_no_goal_uses_unknown_id() {
        // Parse-failure path passes goal=None. Must still produce a valid
        // ProofAttempt rather than panicking.
        let outcome = ProverOutcome::InvalidInput {
            reason: "bad".to_string(),
            location: None,
        };
        let attempt = build_proof_attempt(ProverKind::Coq, None, &outcome, 1, None);
        assert_eq!(attempt.obligation_id, "unknown");
        assert_eq!(attempt.claim, "");
        assert_eq!(attempt.obligation_class, "unknown");
    }

    #[cfg(feature = "verisim")]
    #[tokio::test]
    async fn test_verify_proof_with_class_threads_class_to_inner() {
        // The inner accepts an obligation_class which gets attributed to the
        // ProofAttempt row. We can't observe the row without VeriSimDB, but we
        // can confirm the call typechecks and returns Ok end-to-end.
        let dispatcher = ProverDispatcher::new();
        let result = dispatcher
            .verify_proof_with_class(
                ProverKind::Z3,
                "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)",
                Some("smoke-test"),
            )
            .await;
        assert!(
            result.is_ok(),
            "verify_proof_with_class must complete with Some(class)"
        );
    }

    #[cfg(feature = "verisim")]
    #[tokio::test]
    async fn test_verify_proof_with_unreachable_writer_still_returns_ok() {
        // Spawning a record to an unreachable VeriSimDB must NOT block or
        // fail dispatch. The dispatch result must come back even though the
        // background HTTP write will eventually time out and warn.
        let dispatcher = ProverDispatcher::new().with_verisim_writer("http://127.0.0.1:1");
        let result = dispatcher
            .verify_proof(
                ProverKind::Z3,
                "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)",
            )
            .await;
        assert!(
            result.is_ok(),
            "dispatch must complete even with unreachable VeriSim writer"
        );
    }
}
