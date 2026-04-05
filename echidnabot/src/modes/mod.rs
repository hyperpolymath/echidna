// SPDX-License-Identifier: PMPL-1.0-or-later
//! Bot operating modes for different verification workflows
//!
//! Echidnabot supports four operating modes that control how verification
//! results are reported and what actions are taken:
//!
//! - **Verifier**: Silent pass/fail reporting (minimal output)
//! - **Advisor**: Provides tactic suggestions on proof failures
//! - **Consultant**: Interactive Q&A about proof state
//! - **Regulator**: Blocks PR merges when proofs fail

use serde::{Deserialize, Serialize};
use std::fmt;

/// Bot operating mode
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BotMode {
    /// Silent pass/fail reporting
    /// Only reports verification success or failure with minimal details
    #[default]
    Verifier,

    /// Provides suggestions on failing proofs
    /// Uses ECHIDNA ML backend to suggest tactics when proofs fail
    Advisor,

    /// Interactive Q&A about proof state
    /// Can answer questions about proof state, dependencies, and verification history
    Consultant,

    /// Blocks merges on proof failures
    /// Enforces quality gates by preventing PR merges when proofs fail
    Regulator,
}

impl BotMode {
    /// Returns true if this mode should provide detailed failure output
    pub fn show_detailed_failures(&self) -> bool {
        match self {
            BotMode::Verifier => false,
            BotMode::Advisor | BotMode::Consultant | BotMode::Regulator => true,
        }
    }

    /// Returns true if this mode should suggest tactics on failures
    pub fn suggest_tactics(&self) -> bool {
        matches!(self, BotMode::Advisor | BotMode::Consultant)
    }

    /// Returns true if this mode should block PR merges on failure
    pub fn blocks_merges(&self) -> bool {
        matches!(self, BotMode::Regulator)
    }

    /// Returns true if this mode supports interactive Q&A
    pub fn supports_interactive(&self) -> bool {
        matches!(self, BotMode::Consultant)
    }

    /// Returns the severity level for check runs
    pub fn check_run_severity(&self) -> CheckSeverity {
        match self {
            BotMode::Verifier => CheckSeverity::Notice,
            BotMode::Advisor => CheckSeverity::Warning,
            BotMode::Consultant => CheckSeverity::Warning,
            BotMode::Regulator => CheckSeverity::Error,
        }
    }

    /// Returns the comment style for this mode
    pub fn comment_style(&self) -> CommentStyle {
        match self {
            BotMode::Verifier => CommentStyle::Minimal,
            BotMode::Advisor => CommentStyle::Detailed,
            BotMode::Consultant => CommentStyle::Interactive,
            BotMode::Regulator => CommentStyle::Enforcement,
        }
    }
}


impl fmt::Display for BotMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BotMode::Verifier => write!(f, "Verifier"),
            BotMode::Advisor => write!(f, "Advisor"),
            BotMode::Consultant => write!(f, "Consultant"),
            BotMode::Regulator => write!(f, "Regulator"),
        }
    }
}

/// Check run severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckSeverity {
    Notice,
    Warning,
    Error,
}

/// Comment presentation style
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentStyle {
    /// Minimal output (pass/fail only)
    Minimal,
    /// Detailed failure analysis with suggestions
    Detailed,
    /// Interactive Q&A format
    Interactive,
    /// Enforcement with merge blocking
    Enforcement,
}

/// Verification result formatted for a specific bot mode
#[derive(Debug, Clone)]
pub struct FormattedResult {
    /// Summary line
    pub summary: String,
    /// Detailed output (mode-dependent)
    pub details: Option<String>,
    /// Tactic suggestions (Advisor/Consultant modes only)
    pub suggestions: Vec<String>,
    /// Should block merge (Regulator mode only)
    pub should_block: bool,
    /// Check run status
    pub check_status: CheckStatus,
}

/// Check run status
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStatus {
    Success,
    Failure,
    Neutral,
}

impl BotMode {
    /// Format verification results according to this mode's style
    pub fn format_result(
        &self,
        success: bool,
        prover: &str,
        output: &str,
        suggestions: Vec<String>,
    ) -> FormattedResult {
        let summary = match self {
            BotMode::Verifier => {
                if success {
                    format!("✅ Proof verified ({prover})")
                } else {
                    format!("❌ Proof failed ({prover})")
                }
            }
            BotMode::Advisor => {
                if success {
                    format!("✅ Proof verified with {prover}")
                } else {
                    format!("❌ Proof failed with {prover} — Suggestions available")
                }
            }
            BotMode::Consultant => {
                if success {
                    format!("✅ Verified: {prover} completed successfully")
                } else {
                    format!("❌ Failed: {prover} — Ask me for details")
                }
            }
            BotMode::Regulator => {
                if success {
                    format!("✅ PASSED: {prover} verification")
                } else {
                    format!("🚫 BLOCKED: {prover} verification failed — Merge blocked")
                }
            }
        };

        let details = if self.show_detailed_failures() && !success {
            Some(output.to_string())
        } else {
            None
        };

        let filtered_suggestions = if self.suggest_tactics() {
            suggestions
        } else {
            vec![]
        };

        FormattedResult {
            summary,
            details,
            suggestions: filtered_suggestions,
            should_block: self.blocks_merges() && !success,
            check_status: if success {
                CheckStatus::Success
            } else {
                CheckStatus::Failure
            },
        }
    }
}

/// Parse a bot mode from a `.machine_readable/bot_directives/echidnabot.scm`
/// file content (legacy format supported by callers).
///
/// Looks for `(mode ...)` S-expression in the directive file.
/// Returns `BotMode::Verifier` (default) if parsing fails or mode not found.
pub fn parse_mode_from_directive(content: &str) -> BotMode {
    // Parse simple S-expression: (mode "verifier") or (mode verifier)
    let content_lower = content.to_lowercase();

    // Look for (mode ...) pattern
    if let Some(start) = content_lower.find("(mode") {
        let rest = &content_lower[start..];
        if let Some(end) = rest.find(')') {
            let mode_str = &rest[5..end].trim().trim_matches('"');
            return match *mode_str {
                "verifier" => BotMode::Verifier,
                "advisor" => BotMode::Advisor,
                "consultant" => BotMode::Consultant,
                "regulator" => BotMode::Regulator,
                _ => {
                    tracing::warn!(
                        "Unknown bot mode '{}' in directive, defaulting to Verifier",
                        mode_str
                    );
                    BotMode::Verifier
                }
            };
        }
    }

    BotMode::Verifier
}

/// Determine whether a proof check should be triggered based on mode and event.
///
/// - **Verifier** / **Advisor**: auto-trigger on PR open/update and push
/// - **Consultant**: only respond to explicit `@echidnabot check` mentions
/// - **Regulator**: auto-trigger on PR, check coverage on push
pub fn should_auto_trigger(mode: BotMode, _is_pr: bool) -> bool {
    match mode {
        BotMode::Verifier | BotMode::Advisor | BotMode::Regulator => true,
        BotMode::Consultant => {
            // Consultant mode does NOT auto-trigger -- only on explicit mention
            false
        }
    }
}

/// Check if a comment body contains an explicit echidnabot mention.
///
/// Looks for `@echidnabot check` or `@echidnabot verify` patterns.
pub fn is_explicit_mention(comment_body: &str) -> bool {
    let lower = comment_body.to_lowercase();
    lower.contains("@echidnabot check")
        || lower.contains("@echidnabot verify")
        || lower.contains("@echidnabot run")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verifier_mode_minimal() {
        let mode = BotMode::Verifier;
        assert!(!mode.show_detailed_failures());
        assert!(!mode.suggest_tactics());
        assert!(!mode.blocks_merges());
        assert_eq!(mode.comment_style(), CommentStyle::Minimal);
    }

    #[test]
    fn test_advisor_mode_suggestions() {
        let mode = BotMode::Advisor;
        assert!(mode.show_detailed_failures());
        assert!(mode.suggest_tactics());
        assert!(!mode.blocks_merges());
        assert_eq!(mode.comment_style(), CommentStyle::Detailed);
    }

    #[test]
    fn test_consultant_mode_interactive() {
        let mode = BotMode::Consultant;
        assert!(mode.show_detailed_failures());
        assert!(mode.suggest_tactics());
        assert!(!mode.blocks_merges());
        assert!(mode.supports_interactive());
        assert_eq!(mode.comment_style(), CommentStyle::Interactive);
    }

    #[test]
    fn test_regulator_mode_blocking() {
        let mode = BotMode::Regulator;
        assert!(mode.show_detailed_failures());
        assert!(!mode.suggest_tactics());
        assert!(mode.blocks_merges());
        assert_eq!(mode.comment_style(), CommentStyle::Enforcement);
        assert_eq!(mode.check_run_severity(), CheckSeverity::Error);
    }

    #[test]
    fn test_format_result_success() {
        let mode = BotMode::Advisor;
        let result = mode.format_result(
            true,
            "Coq",
            "Proof complete",
            vec!["tactic1".to_string()],
        );
        assert_eq!(result.check_status, CheckStatus::Success);
        assert!(!result.should_block);
    }

    #[test]
    fn test_format_result_failure_with_suggestions() {
        let mode = BotMode::Advisor;
        let suggestions = vec![
            "Try induction xs".to_string(),
            "Consider rewrite app_assoc".to_string(),
        ];
        let result = mode.format_result(false, "Coq", "Goal not discharged", suggestions.clone());
        assert_eq!(result.check_status, CheckStatus::Failure);
        assert_eq!(result.suggestions, suggestions);
        assert!(!result.should_block); // Advisor doesn't block
    }

    #[test]
    fn test_regulator_blocks_on_failure() {
        let mode = BotMode::Regulator;
        let result = mode.format_result(false, "Lean", "Proof failed", vec![]);
        assert_eq!(result.check_status, CheckStatus::Failure);
        assert!(result.should_block); // Regulator blocks merges
        assert!(result.summary.contains("BLOCKED"));
    }

    #[test]
    fn test_verifier_minimal_output() {
        let mode = BotMode::Verifier;
        let result = mode.format_result(false, "Agda", "Type error at line 42", vec![]);
        assert_eq!(result.check_status, CheckStatus::Failure);
        assert!(result.details.is_none()); // Verifier doesn't show details
        assert!(result.suggestions.is_empty());
        assert!(!result.should_block);
    }

    // =========================================================================
    // Mode resolver tests
    // =========================================================================

    #[test]
    fn test_parse_mode_verifier() {
        let content = r#"(echidnabot (mode "verifier"))"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Verifier);
    }

    #[test]
    fn test_parse_mode_advisor() {
        let content = r#"(echidnabot (mode "advisor"))"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Advisor);
    }

    #[test]
    fn test_parse_mode_consultant() {
        let content = r#"(mode consultant)"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Consultant);
    }

    #[test]
    fn test_parse_mode_regulator() {
        let content = r#"(mode "regulator")"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Regulator);
    }

    #[test]
    fn test_parse_mode_missing_defaults_to_verifier() {
        let content = r#"(echidnabot (provers "lean" "coq"))"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Verifier);
    }

    #[test]
    fn test_parse_mode_unknown_defaults_to_verifier() {
        let content = r#"(mode "unknown-mode")"#;
        assert_eq!(parse_mode_from_directive(content), BotMode::Verifier);
    }

    #[test]
    fn test_parse_mode_empty_content() {
        assert_eq!(parse_mode_from_directive(""), BotMode::Verifier);
    }

    #[test]
    fn test_should_auto_trigger_verifier() {
        assert!(should_auto_trigger(BotMode::Verifier, true));
        assert!(should_auto_trigger(BotMode::Verifier, false));
    }

    #[test]
    fn test_should_auto_trigger_advisor() {
        assert!(should_auto_trigger(BotMode::Advisor, true));
        assert!(should_auto_trigger(BotMode::Advisor, false));
    }

    #[test]
    fn test_should_not_auto_trigger_consultant() {
        assert!(!should_auto_trigger(BotMode::Consultant, true));
        assert!(!should_auto_trigger(BotMode::Consultant, false));
    }

    #[test]
    fn test_should_auto_trigger_regulator() {
        assert!(should_auto_trigger(BotMode::Regulator, true));
        assert!(should_auto_trigger(BotMode::Regulator, false));
    }

    #[test]
    fn test_is_explicit_mention() {
        assert!(is_explicit_mention("@echidnabot check this proof"));
        assert!(is_explicit_mention("Please @echidnabot verify"));
        assert!(is_explicit_mention("@echidnabot run"));
        assert!(!is_explicit_mention("echidnabot check")); // Missing @
        assert!(!is_explicit_mention("Hello world"));
    }
}
