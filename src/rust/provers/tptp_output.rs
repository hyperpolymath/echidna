// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Shared TPTP output parser for higher-order and first-order ATPs
//!
//! Parses SZS (Standard Zero Substitution) status lines produced by TPTP-compliant
//! provers including Leo-III, Satallax, Lash, agsyHOL, Vampire, E-Prover, etc.

use anyhow::Result;

/// Parse TPTP prover output for SZS status indicators
///
/// Returns `Ok(true)` if status indicates theorem proved (Theorem)
/// Returns `Ok(false)` if status indicates non-proof (CounterSatisfiable, Satisfiable, etc.)
/// Returns `Err` if output cannot be parsed or prover error detected
pub fn parse_szs_status(output: &str) -> Result<bool> {
    for line in output.lines() {
        let trimmed = line.trim();

        // Check for theorem proven
        if contains_szs_status(trimmed, &["Theorem"]) {
            return Ok(true);
        }

        // Check for non-proof statuses
        if contains_szs_status(
            trimmed,
            &[
                "CounterSatisfiable",
                "Satisfiable",
                "Unknown",
                "Timeout",
                "ResourceOut",
                "GaveUp",
            ],
        ) {
            return Ok(false);
        }

        // Errors and failures
        if contains_szs_status(trimmed, &["InternalError", "UserError", "OtherError"]) {
            return Err(anyhow::anyhow!("Prover error: {}", trimmed));
        }
    }

    Ok(false)
}

/// Check if a line contains a specific SZS status
fn contains_szs_status(line: &str, statuses: &[&str]) -> bool {
    for status in statuses {
        // Match both "SZS status <status>" and "% SZS status <status>"
        if line.contains(&format!("SZS status {}", status)) {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_szs_theorem() {
        let output = "% SZS status Theorem\n";
        assert!(parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_satisfiable() {
        let output = "% SZS status Satisfiable\n";
        assert!(!parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_unknown() {
        let output = "% SZS status Unknown\n";
        assert!(!parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_counter_satisfiable() {
        let output = "% SZS status CounterSatisfiable\n";
        assert!(!parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_with_output() {
        let output = r#"
% Some prover output
% More output
% SZS status Theorem
% Additional info
"#;
        assert!(parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_no_status() {
        let output = "some random output\nwithout status\n";
        assert!(!parse_szs_status(output).unwrap());
    }

    #[test]
    fn test_parse_szs_error() {
        let output = "% SZS status InternalError\n";
        assert!(parse_szs_status(output).is_err());
    }
}
