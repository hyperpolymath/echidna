// SPDX-License-Identifier: PMPL-1.0-or-later
//! Result formatting bridge between dispatcher and bot modes
//!
//! This module converts ECHIDNA verification results into mode-specific
//! formatted output suitable for PR comments, check runs, and notifications.

use crate::dispatcher::{ProofResult, ProofStatus, ProverKind, TacticSuggestion};
use crate::modes::{BotMode, CheckStatus, FormattedResult};

/// Format a proof result according to the configured bot mode
pub fn format_proof_result(
    mode: BotMode,
    result: &ProofResult,
    prover: ProverKind,
    suggestions: Vec<TacticSuggestion>,
) -> FormattedResult {
    let success = result.status == ProofStatus::Verified;
    let prover_name = prover.display_name();

    // Convert tactic suggestions to strings
    let suggestion_strings: Vec<String> = suggestions
        .iter()
        .map(format_tactic_suggestion)
        .collect();

    mode.format_result(success, prover_name, &result.prover_output, suggestion_strings)
}

/// Format a tactic suggestion for display
fn format_tactic_suggestion(suggestion: &TacticSuggestion) -> String {
    let confidence_pct = (suggestion.confidence * 100.0) as u8;

    if let Some(ref explanation) = suggestion.explanation {
        format!(
            "• `{}` ({}% confidence) — {}",
            suggestion.tactic, confidence_pct, explanation
        )
    } else {
        format!("• `{}` ({}% confidence)", suggestion.tactic, confidence_pct)
    }
}

/// Generate a PR comment from a formatted result
pub fn generate_pr_comment(result: &FormattedResult, mode: BotMode) -> String {
    let mut comment = String::new();

    // Header with mode badge
    comment.push_str(&format!("## 🦔 echidnabot • Mode: **{}**\n\n", mode));

    // Summary line
    comment.push_str(&result.summary);
    comment.push_str("\n\n");

    // Details section (if mode shows details)
    if let Some(ref details) = result.details {
        comment.push_str("### 📋 Verification Output\n\n");
        comment.push_str("```\n");
        // Truncate long output
        let truncated = if details.len() > 2000 {
            format!("{}...\n\n(Output truncated, {} chars total)", &details[..2000], details.len())
        } else {
            details.clone()
        };
        comment.push_str(&truncated);
        comment.push_str("\n```\n\n");
    }

    // Tactic suggestions section (Advisor/Consultant modes)
    if !result.suggestions.is_empty() {
        comment.push_str("### 💡 Suggested Tactics\n\n");
        for suggestion in &result.suggestions {
            comment.push_str(suggestion);
            comment.push('\n');
        }
        comment.push('\n');
    }

    // Enforcement notice (Regulator mode)
    if result.should_block {
        comment.push_str("### 🚫 Merge Blocked\n\n");
        comment.push_str("This PR cannot be merged until all proofs pass verification.\n\n");
        comment.push_str("**Action required:** Fix the failing proof(s) and push an update.\n\n");
    }

    // Interactive prompt (Consultant mode)
    if mode.supports_interactive() {
        comment.push_str("---\n\n");
        comment.push_str("💬 **Ask me anything** about the proof state, dependencies, or verification history!\n");
    }

    comment
}

/// Generate a check run conclusion from a formatted result
pub fn check_run_conclusion(result: &FormattedResult) -> &'static str {
    match result.check_status {
        CheckStatus::Success => "success",
        CheckStatus::Failure => "failure",
        CheckStatus::Neutral => "neutral",
    }
}

/// Generate a check run summary from a formatted result
pub fn check_run_summary(result: &FormattedResult, mode: BotMode) -> String {
    let status_emoji = match result.check_status {
        CheckStatus::Success => "✅",
        CheckStatus::Failure => "❌",
        CheckStatus::Neutral => "⚠️",
    };

    let mut summary = format!("{} {}\n\n", status_emoji, result.summary);

    // Add mode-specific context
    match mode {
        BotMode::Verifier => {
            summary.push_str("*Running in Verifier mode: Silent pass/fail reporting*\n");
        }
        BotMode::Advisor => {
            summary.push_str("*Running in Advisor mode: Tactic suggestions enabled*\n");
        }
        BotMode::Consultant => {
            summary.push_str("*Running in Consultant mode: Interactive Q&A available*\n");
        }
        BotMode::Regulator => {
            summary.push_str("*Running in Regulator mode: Quality gate enforcement*\n");
            if result.should_block {
                summary.push_str("\n**⚠️ MERGE BLOCKED** — All proofs must pass before merging.\n");
            }
        }
    }

    summary
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_success_result() -> ProofResult {
        ProofResult {
            status: ProofStatus::Verified,
            message: "Proof complete".to_string(),
            prover_output: "All goals discharged successfully".to_string(),
            duration_ms: 150,
            artifacts: vec![],
        }
    }

    fn make_failure_result() -> ProofResult {
        ProofResult {
            status: ProofStatus::Failed,
            message: "Proof failed".to_string(),
            prover_output: "Error: Goal not discharged at line 42".to_string(),
            duration_ms: 80,
            artifacts: vec![],
        }
    }

    fn make_suggestions() -> Vec<TacticSuggestion> {
        vec![
            TacticSuggestion {
                tactic: "induction xs".to_string(),
                confidence: 0.85,
                explanation: Some("Try induction on list structure".to_string()),
            },
            TacticSuggestion {
                tactic: "rewrite app_assoc".to_string(),
                confidence: 0.72,
                explanation: None,
            },
        ]
    }

    #[test]
    fn test_format_success_verifier() {
        let result = make_success_result();
        let formatted = format_proof_result(BotMode::Verifier, &result, ProverKind::Coq, vec![]);

        assert_eq!(formatted.check_status, CheckStatus::Success);
        assert!(!formatted.should_block);
        assert!(formatted.details.is_none()); // Verifier doesn't show details
    }

    #[test]
    fn test_format_failure_advisor() {
        let result = make_failure_result();
        let suggestions = make_suggestions();
        let formatted = format_proof_result(BotMode::Advisor, &result, ProverKind::Coq, suggestions);

        assert_eq!(formatted.check_status, CheckStatus::Failure);
        assert!(!formatted.should_block); // Advisor doesn't block
        assert!(formatted.details.is_some()); // Advisor shows details
        assert_eq!(formatted.suggestions.len(), 2); // Advisor shows suggestions
    }

    #[test]
    fn test_format_failure_regulator() {
        let result = make_failure_result();
        let formatted = format_proof_result(BotMode::Regulator, &result, ProverKind::Lean, vec![]);

        assert_eq!(formatted.check_status, CheckStatus::Failure);
        assert!(formatted.should_block); // Regulator blocks merges
        assert!(formatted.summary.contains("BLOCKED"));
    }

    #[test]
    fn test_pr_comment_with_suggestions() {
        let result = make_failure_result();
        let suggestions = make_suggestions();
        let formatted = format_proof_result(BotMode::Advisor, &result, ProverKind::Coq, suggestions);
        let comment = generate_pr_comment(&formatted, BotMode::Advisor);

        assert!(comment.contains("echidnabot"));
        assert!(comment.contains("Advisor"));
        assert!(comment.contains("Suggested Tactics"));
        assert!(comment.contains("induction xs"));
        assert!(comment.contains("85% confidence"));
    }

    #[test]
    fn test_pr_comment_regulator_blocking() {
        let result = make_failure_result();
        let formatted = format_proof_result(BotMode::Regulator, &result, ProverKind::Coq, vec![]);
        let comment = generate_pr_comment(&formatted, BotMode::Regulator);

        assert!(comment.contains("Merge Blocked"));
        assert!(comment.contains("cannot be merged"));
    }

    #[test]
    fn test_pr_comment_consultant_interactive() {
        let result = make_success_result();
        let formatted = format_proof_result(BotMode::Consultant, &result, ProverKind::Agda, vec![]);
        let comment = generate_pr_comment(&formatted, BotMode::Consultant);

        assert!(comment.contains("Ask me anything"));
        assert!(comment.contains("Consultant"));
    }

    #[test]
    fn test_check_run_conclusions() {
        let success = make_success_result();
        let failure = make_failure_result();

        let success_formatted = format_proof_result(BotMode::Verifier, &success, ProverKind::Z3, vec![]);
        let failure_formatted = format_proof_result(BotMode::Verifier, &failure, ProverKind::Z3, vec![]);

        assert_eq!(check_run_conclusion(&success_formatted), "success");
        assert_eq!(check_run_conclusion(&failure_formatted), "failure");
    }
}
