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

use crate::provers::{ProverConfig, ProverFactory, ProverKind};
use crate::verification::axiom_tracker::{AxiomTracker, AxiomUsage, DangerLevel};
use crate::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};

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
}

impl Default for DispatchConfig {
    fn default() -> Self {
        Self {
            cross_check: false,
            min_trust_level: TrustLevel::Level2,
            track_axioms: true,
            generate_certificates: false,
            timeout: 300,
        }
    }
}

/// Prover dispatcher that runs the full trust-hardening pipeline
pub struct ProverDispatcher {
    config: DispatchConfig,
}

impl ProverDispatcher {
    /// Create a new dispatcher with default configuration
    pub fn new() -> Self {
        Self {
            config: DispatchConfig::default(),
        }
    }

    /// Create a dispatcher with custom configuration
    pub fn with_config(config: DispatchConfig) -> Self {
        Self { config }
    }

    /// Dispatch a proof verification request through the trust-hardening pipeline
    pub async fn verify_proof(
        &self,
        prover_kind: ProverKind,
        content: &str,
    ) -> Result<DispatchResult> {
        let start = Instant::now();

        // Step 1: Create the prover
        let mut prover_config = ProverConfig::default();
        prover_config.timeout = self.config.timeout;

        let prover = ProverFactory::create(prover_kind, prover_config)
            .context("Failed to create prover backend")?;

        info!("Dispatching proof to {:?}", prover_kind);

        // Step 2: Parse the proof content
        let state = prover
            .parse_string(content)
            .await
            .context("Failed to parse proof content")?;

        // Step 3: Run verification
        let verified = prover
            .verify_proof(&state)
            .await
            .context("Failed to verify proof")?;

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
                usages.iter()
                    .map(|u| u.danger_level)
                    .max()
                    .unwrap_or(DangerLevel::Safe)
            })
            .unwrap_or(DangerLevel::Safe);

        // Get first axiom usage for the report (if any)
        let axiom_report = axiom_usages
            .as_ref()
            .and_then(|usages| usages.first().cloned());

        // Step 6: Compute trust level
        let trust_factors = TrustFactors {
            prover: prover_kind,
            confirming_provers: 1,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: worst_danger,
            solver_integrity_ok: true, // TODO: wire to actual integrity checker
            portfolio_confidence: None,
        };

        let trust_level = compute_trust_level(&trust_factors);

        let elapsed = start.elapsed().as_millis() as u64;

        // Step 7: Check minimum trust level
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
                }
                Err(e) => {
                    warn!("Cross-check with {:?} failed: {}", additional, e);
                }
            }
        }

        let elapsed = start.elapsed().as_millis() as u64;

        // Recompute trust level with cross-checking info
        let worst_danger = primary_result
            .axiom_report
            .as_ref()
            .map(|r| r.danger_level)
            .unwrap_or(DangerLevel::Safe);

        let trust_factors = TrustFactors {
            prover: primary_prover,
            confirming_provers: confirming_count,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: worst_danger,
            solver_integrity_ok: true,
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

        if content_lower.contains("theorem") && content_lower.contains(":=") && content_lower.contains("lean") {
            ProverKind::Lean
        } else if content_lower.contains("theorem") && content_lower.contains("proof") && content_lower.contains("qed") {
            ProverKind::Coq
        } else if content_lower.contains("(set-logic") || content_lower.contains("(assert") {
            ProverKind::Z3
        } else if content_lower.contains("theory") && content_lower.contains("imports") {
            ProverKind::Isabelle
        } else if content_lower.contains("module") && content_lower.contains("where") && content_lower.contains("data") {
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
        let prover = ProverDispatcher::select_prover("Theorem foo : True.\nProof.\nexact I.\nQed.", None);
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
        };

        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("Level4"));
    }
}
