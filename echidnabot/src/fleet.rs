// SPDX-License-Identifier: PMPL-1.0-or-later
//! Integration with gitbot-fleet shared context
//!
//! This module enables echidnabot to participate in the gitbot-fleet
//! orchestration, sharing findings and coordinating with other bots.

use gitbot_shared_context::{BotId, Context, Finding, Severity};
use std::path::PathBuf;
use uuid::Uuid;

use crate::dispatcher::{ProofResult, ProofStatus};
use crate::error::Result;

/// Fleet integration wrapper for echidnabot
pub struct FleetIntegration {
    /// Shared context for the current analysis session
    context: Context,
}

impl FleetIntegration {
    /// Create a new fleet integration for a repository
    pub fn new(repo_name: &str, repo_path: impl Into<PathBuf>) -> Self {
        let mut context = Context::new(repo_name, repo_path);

        // Register echidnabot in the fleet
        context.register_bot(BotId::Echidnabot);

        Self { context }
    }

    /// Start echidnabot's execution
    pub fn start(&mut self) -> Result<()> {
        self.context
            .start_bot(BotId::Echidnabot)
            .map_err(|e| crate::error::Error::Fleet(e.to_string()))
    }

    /// Record a proof verification result as a finding
    pub fn add_proof_result(
        &mut self,
        file_path: &str,
        theorem_name: &str,
        prover_name: &str,
        result: &ProofResult,
    ) {
        let finding = match result.status {
            ProofStatus::Verified => {
                // Successful verification - informational finding
                Finding::new(
                    BotId::Echidnabot,
                    "ECHIDNA-VERIFY-001",
                    Severity::Info,
                    &format!("Theorem '{}' verified successfully using {}", theorem_name, prover_name),
                )
                .with_rule_name("Formal Verification Success")
                .with_category("formal-verification")
                .with_file(PathBuf::from(file_path))
                .with_suggestion("Proof is formally verified")
            }
            ProofStatus::Failed => {
                // Proof verification failed - error severity (blocks release)
                Finding::new(
                    BotId::Echidnabot,
                    "ECHIDNA-VERIFY-002",
                    Severity::Error,
                    &format!(
                        "Theorem '{}' failed verification: {}",
                        theorem_name, result.message
                    ),
                )
                .with_rule_name("Formal Verification Failed")
                .with_category("formal-verification")
                .with_file(PathBuf::from(file_path))
                .with_suggestion("Review the proof and ensure all lemmas are correct")
            }
            ProofStatus::Timeout => {
                // Timeout - warning severity
                Finding::new(
                    BotId::Echidnabot,
                    "ECHIDNA-VERIFY-003",
                    Severity::Warning,
                    &format!(
                        "Theorem '{}' verification timed out after {}ms",
                        theorem_name, result.duration_ms
                    ),
                )
                .with_rule_name("Formal Verification Timeout")
                .with_category("formal-verification")
                .with_file(PathBuf::from(file_path))
                .with_suggestion("Consider simplifying the proof or increasing timeout")
            }
            ProofStatus::Error => {
                // Error during verification - error severity
                Finding::new(
                    BotId::Echidnabot,
                    "ECHIDNA-VERIFY-004",
                    Severity::Error,
                    &format!(
                        "Verification error for theorem '{}': {}",
                        theorem_name, result.message
                    ),
                )
                .with_rule_name("Formal Verification Error")
                .with_category("formal-verification")
                .with_file(PathBuf::from(file_path))
                .with_suggestion("Check prover configuration and logs")
            }
            ProofStatus::Unknown => {
                // Unknown status - warning severity
                Finding::new(
                    BotId::Echidnabot,
                    "ECHIDNA-VERIFY-005",
                    Severity::Warning,
                    &format!(
                        "Unable to determine status for theorem '{}': {}",
                        theorem_name, result.message
                    ),
                )
                .with_rule_name("Formal Verification Unknown Status")
                .with_category("formal-verification")
                .with_file(PathBuf::from(file_path))
                .with_suggestion("Check prover availability and configuration")
            }
        };

        self.context.add_finding(finding);
    }

    /// Complete echidnabot's execution
    pub fn complete(
        &mut self,
        findings_count: usize,
        errors_count: usize,
        files_analyzed: usize,
    ) -> Result<()> {
        self.context
            .complete_bot(BotId::Echidnabot, findings_count, errors_count, files_analyzed)
            .map_err(|e| crate::error::Error::Fleet(e.to_string()))
    }

    /// Mark execution as failed
    pub fn fail(&mut self, error: &str) -> Result<()> {
        self.context
            .fail_bot(BotId::Echidnabot, error)
            .map_err(|e| crate::error::Error::Fleet(e.to_string()))
    }

    /// Get the underlying context for storage/serialization
    pub fn context(&self) -> &Context {
        &self.context
    }

    /// Get mutable context reference
    pub fn context_mut(&mut self) -> &mut Context {
        &mut self.context
    }

    /// Get all findings from this session
    pub fn findings(&self) -> Vec<&Finding> {
        self.context.findings_from(BotId::Echidnabot)
    }

    /// Check if any critical errors were found (blocks release)
    pub fn has_critical_errors(&self) -> bool {
        self.context
            .findings_from(BotId::Echidnabot)
            .iter()
            .any(|f| f.severity.blocks_release())
    }

    /// Get session ID
    pub fn session_id(&self) -> Uuid {
        self.context.session_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fleet_integration_creation() {
        let integration = FleetIntegration::new("test-repo", "/tmp/test");
        assert_eq!(integration.context().repo_name, "test-repo");
    }

    #[test]
    fn test_add_verified_proof() {
        let mut integration = FleetIntegration::new("test-repo", "/tmp/test");
        let result = ProofResult {
            status: ProofStatus::Verified,
            message: "OK".to_string(),
            prover_output: "Proof completed".to_string(),
            duration_ms: 1500,
            artifacts: vec![],
        };

        integration.add_proof_result("src/main.v", "plus_comm", "Coq", &result);
        let findings = integration.findings();

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].severity, Severity::Info);
        assert!(!findings[0].severity.blocks_release());
    }

    #[test]
    fn test_add_failed_proof() {
        let mut integration = FleetIntegration::new("test-repo", "/tmp/test");
        let result = ProofResult {
            status: ProofStatus::Failed,
            message: "Type mismatch in hypothesis".to_string(),
            prover_output: "Error details...".to_string(),
            duration_ms: 500,
            artifacts: vec![],
        };

        integration.add_proof_result("src/theorem.lean", "bad_theorem", "Lean", &result);
        let findings = integration.findings();

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].severity, Severity::Error);
        assert!(findings[0].severity.blocks_release());
    }

    #[test]
    fn test_has_critical_errors() {
        let mut integration = FleetIntegration::new("test-repo", "/tmp/test");

        // Add a verified proof - no critical errors
        let valid_result = ProofResult {
            status: ProofStatus::Verified,
            message: "OK".to_string(),
            prover_output: "Proof completed".to_string(),
            duration_ms: 2000,
            artifacts: vec![],
        };
        integration.add_proof_result("src/valid.agda", "valid_theorem", "Agda", &valid_result);
        assert!(!integration.has_critical_errors());

        // Add a failed proof - now has critical errors
        let invalid_result = ProofResult {
            status: ProofStatus::Failed,
            message: "Proof obligation not discharged".to_string(),
            prover_output: "Failed".to_string(),
            duration_ms: 1000,
            artifacts: vec![],
        };
        integration.add_proof_result("src/invalid.thy", "bad_theorem", "Isabelle", &invalid_result);
        assert!(integration.has_critical_errors());
    }
}

