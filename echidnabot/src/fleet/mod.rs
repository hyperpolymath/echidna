// SPDX-License-Identifier: PMPL-1.0-or-later
//! Fleet integration for gitbot-fleet coordination
//!
//! This module provides the bridge between echidnabot and the gitbot-fleet
//! shared-context coordination layer. It handles:
//!
//! - Registering echidnabot as a Tier 1 Verifier
//! - Publishing findings after proof verification
//! - Coordinating with other bots in the fleet
//! - Consuming findings from rhodibot (if needed)

use crate::error::{Error, Result};
use crate::scheduler::{JobResult, ProofJob};
use gitbot_shared_context::{BotId, Context, ContextStorage, Finding, Severity};
use std::path::PathBuf;
use tracing::{debug, info, warn};

/// Fleet coordinator for echidnabot
pub struct FleetCoordinator {
    /// Shared context (if connected to fleet)
    context: Option<Context>,
}

impl FleetCoordinator {
    /// Create a new fleet coordinator (not yet connected)
    pub fn new() -> Self {
        Self { context: None }
    }

    /// Connect to fleet for a repository analysis session
    ///
    /// This creates a shared context and registers echidnabot as a Tier 1 Verifier.
    pub fn connect(&mut self, repo_name: &str, repo_path: impl Into<PathBuf>) -> Result<()> {
        info!("Connecting to gitbot-fleet for repo: {}", repo_name);

        let mut ctx = Context::new(repo_name, repo_path);
        ctx.register_all_bots();

        // Mark echidnabot as started
        ctx.start_bot(BotId::Echidnabot)
            .map_err(|e| Error::Internal(format!("Failed to start bot: {}", e)))?;

        self.context = Some(ctx);
        Ok(())
    }

    /// Disconnect from fleet (mark echidnabot as complete)
    pub fn disconnect(&mut self, findings_count: usize, errors_count: usize, files_analyzed: usize) -> Result<()> {
        if let Some(ref mut ctx) = self.context {
            info!("Disconnecting from gitbot-fleet (findings: {}, errors: {}, files: {})",
                  findings_count, errors_count, files_analyzed);

            ctx.complete_bot(BotId::Echidnabot, findings_count, errors_count, files_analyzed)
                .map_err(|e| Error::Internal(format!("Failed to complete bot: {}", e)))?;

            // Persist context to ~/.gitbot-fleet/sessions/<session_id>.json so the
            // fleet-coordinator and other bots can pick up echidnabot findings after
            // this bot's process has exited. Persistence failure is logged but does
            // NOT fail disconnect — losing a session log is less bad than crashing
            // a running bot. Callers that need strict durability should call the
            // persistence API directly.
            match ContextStorage::default() {
                Ok(storage) => match storage.save_context(ctx) {
                    Ok(path) => info!(path = %path.display(), "Persisted session context"),
                    Err(e) => warn!("Failed to persist session context: {}", e),
                },
                Err(e) => warn!("Failed to open session storage: {}", e),
            }
        }

        self.context = None;
        Ok(())
    }

    /// Publish a finding from a proof job result
    pub fn publish_finding(&mut self, job: &ProofJob, result: &JobResult) -> Result<()> {
        if let Some(ref mut ctx) = self.context {
            debug!("Publishing finding for job: {}", job.id);

            // Determine severity based on result
            let severity = if result.success {
                Severity::Info // Successful proof verification
            } else if !result.failed_files.is_empty() {
                Severity::Error // Proof failed
            } else {
                Severity::Warning // Other issues
            };

            // Create finding for each failed file
            for failed_file in &result.failed_files {
                let finding = Finding::new(
                    BotId::Echidnabot,
                    "PROOF-VERIFICATION",
                    severity,
                    &result.message,
                )
                .with_rule_name("Formal Proof Verification")
                .with_category("verification")
                .with_file(PathBuf::from(failed_file))
                .with_suggestion(&format!(
                    "Proof verification failed for {}. Check prover output:\n{}",
                    failed_file, result.prover_output
                ))
                .with_metadata(serde_json::json!({
                    "job_id": job.id.to_string(),
                    "prover": format!("{:?}", job.prover),
                    "duration_ms": result.duration_ms,
                    "commit_sha": job.commit_sha,
                }));

                ctx.add_finding(finding);
            }

            // Also publish successful verifications as Info findings
            if result.success {
                for verified_file in &result.verified_files {
                    let finding = Finding::new(
                        BotId::Echidnabot,
                        "PROOF-VERIFIED",
                        Severity::Info,
                        &format!("Proof successfully verified for {}", verified_file),
                    )
                    .with_rule_name("Formal Proof Verification - Success")
                    .with_category("verification")
                    .with_file(PathBuf::from(verified_file))
                    .with_metadata(serde_json::json!({
                        "job_id": job.id.to_string(),
                        "prover": format!("{:?}", job.prover),
                        "duration_ms": result.duration_ms,
                        "commit_sha": job.commit_sha,
                    }));

                    ctx.add_finding(finding);
                }
            }

            Ok(())
        } else {
            // Not connected to fleet - skip publishing
            debug!("Not connected to fleet, skipping finding publication");
            Ok(())
        }
    }

    /// Get current context (for inspection)
    pub fn context(&self) -> Option<&Context> {
        self.context.as_ref()
    }

    /// Check if connected to fleet
    pub fn is_connected(&self) -> bool {
        self.context.is_some()
    }

    /// Get session ID (if connected)
    pub fn session_id(&self) -> Option<uuid::Uuid> {
        self.context.as_ref().map(|ctx| ctx.session_id)
    }
}

impl Default for FleetCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatcher::ProverKind;
    use crate::scheduler::JobId;
    use chrono::Utc;
    use uuid::Uuid;

    #[test]
    fn test_fleet_coordinator_lifecycle() {
        let mut coordinator = FleetCoordinator::new();
        assert!(!coordinator.is_connected());

        // Connect
        coordinator.connect("test-repo", "/tmp/test-repo").unwrap();
        assert!(coordinator.is_connected());
        assert!(coordinator.session_id().is_some());

        // Disconnect
        coordinator.disconnect(5, 2, 10).unwrap();
        assert!(!coordinator.is_connected());
    }

    #[test]
    fn test_publish_finding_success() {
        let mut coordinator = FleetCoordinator::new();
        coordinator.connect("test-repo", "/tmp/test-repo").unwrap();

        let job = ProofJob {
            id: JobId::new(),
            repo_id: Uuid::new_v4(),
            commit_sha: "abc123".to_string(),
            prover: ProverKind::Coq,
            file_paths: vec!["test.v".to_string()],
            status: crate::scheduler::JobStatus::Completed,
            priority: crate::scheduler::JobPriority::Normal,
            queued_at: Utc::now(),
            started_at: Some(Utc::now()),
            completed_at: Some(Utc::now()),
            result: None,
        };

        let result = JobResult {
            success: true,
            message: "Proof verified successfully".to_string(),
            prover_output: "All proofs passed".to_string(),
            duration_ms: 1234,
            verified_files: vec!["test.v".to_string()],
            failed_files: vec![],
        };

        coordinator.publish_finding(&job, &result).unwrap();

        // Should have 1 finding (success)
        let ctx = coordinator.context().unwrap();
        assert_eq!(ctx.findings.len(), 1);
        assert_eq!(ctx.findings.findings[0].severity, Severity::Info);
    }

    #[test]
    fn test_publish_finding_failure() {
        let mut coordinator = FleetCoordinator::new();
        coordinator.connect("test-repo", "/tmp/test-repo").unwrap();

        let job = ProofJob {
            id: JobId::new(),
            repo_id: Uuid::new_v4(),
            commit_sha: "abc123".to_string(),
            prover: ProverKind::Lean,
            file_paths: vec!["test.lean".to_string()],
            status: crate::scheduler::JobStatus::Failed,
            priority: crate::scheduler::JobPriority::High,
            queued_at: Utc::now(),
            started_at: Some(Utc::now()),
            completed_at: Some(Utc::now()),
            result: None,
        };

        let result = JobResult {
            success: false,
            message: "Proof verification failed".to_string(),
            prover_output: "Error: Theorem not proved".to_string(),
            duration_ms: 567,
            verified_files: vec![],
            failed_files: vec!["test.lean".to_string()],
        };

        coordinator.publish_finding(&job, &result).unwrap();

        // Should have 1 finding (error)
        let ctx = coordinator.context().unwrap();
        assert_eq!(ctx.findings.len(), 1);
        assert_eq!(ctx.findings.findings[0].severity, Severity::Error);
    }

    #[test]
    fn test_publish_without_connection() {
        let mut coordinator = FleetCoordinator::new();

        let job = ProofJob {
            id: JobId::new(),
            repo_id: Uuid::new_v4(),
            commit_sha: "abc123".to_string(),
            prover: ProverKind::Z3,
            file_paths: vec!["test.smt2".to_string()],
            status: crate::scheduler::JobStatus::Completed,
            priority: crate::scheduler::JobPriority::Normal,
            queued_at: Utc::now(),
            started_at: Some(Utc::now()),
            completed_at: Some(Utc::now()),
            result: None,
        };

        let result = JobResult {
            success: true,
            message: "Verified".to_string(),
            prover_output: "sat".to_string(),
            duration_ms: 100,
            verified_files: vec!["test.smt2".to_string()],
            failed_files: vec![],
        };

        // Should not error when not connected
        coordinator.publish_finding(&job, &result).unwrap();
    }
}
