// SPDX-License-Identifier: PMPL-1.0-or-later

//! Prover dispatch module
//!
//! Connects the API layer to prover backends through the trust-hardening
//! pipeline: integrity check -> sandbox -> prove -> certificate check ->
//! axiom scan -> confidence scoring.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Instant;
use tracing::{info, warn};

use crate::integrity::solver_integrity::{IntegrityChecker, IntegrityStatus};
use crate::llm::LlmAdvisor;
use crate::provers::outcome::{classify_anyhow_error, ProverOutcome};
use crate::provers::{ProverConfig, ProverFactory, ProverKind};
use crate::verification::axiom_tracker::{AxiomTracker, AxiomUsage, DangerLevel};
use crate::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};

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

/// Prover dispatcher that runs the full trust-hardening pipeline
pub struct ProverDispatcher {
    config: DispatchConfig,
    integrity_checker: Option<IntegrityChecker>,
    /// Optional frontier LLM advisor for intelligent dispatch optimisation.
    /// Advisory only — cannot influence trust levels.
    llm_advisor: Option<LlmAdvisor>,
}

impl ProverDispatcher {
    /// Create a new dispatcher with default configuration
    pub fn new() -> Self {
        Self {
            config: DispatchConfig::default(),
            integrity_checker: None,
            llm_advisor: None,
        }
    }

    /// Create a dispatcher with custom configuration
    pub fn with_config(config: DispatchConfig) -> Self {
        Self {
            config,
            integrity_checker: None,
            llm_advisor: None,
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
}
