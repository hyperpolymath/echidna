// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Shared helpers for the connection-method prover family
//! (MleanCoP / ileanCoP / nanoCoP).
//!
//! These three Prolog-based backends share TPTP-shaped input,
//! SZS-marker output, and the same SWI-Prolog spawn pattern.  This
//! module factors out the common pieces so each backend file is a
//! thin wrapper.

#![allow(dead_code)]

use anyhow::Result;
use crate::core::ProofState;

/// Convert a `ProofState` into a TPTP fof-formatted input.
///
/// Same shape as `metitarski::to_tptp` but factored here so the
/// connection-method trio share a single serialiser.
pub(crate) fn to_tptp(state: &ProofState) -> String {
    let mut tptp = String::new();
    for (i, axiom) in state.context.axioms.iter().enumerate() {
        tptp.push_str(&format!("fof(axiom_{}, axiom, {}).\n", i, axiom));
    }
    for (i, def) in state.context.definitions.iter().enumerate() {
        tptp.push_str(&format!("fof(definition_{}, axiom, {}).\n", i, def));
    }
    if let Some(goal) = state.goals.first() {
        tptp.push_str(&format!("fof(conjecture, conjecture, {}).\n", goal.target));
    }
    tptp
}

/// Parse a connection-method prover's stdout for SZS markers and the
/// native "matrix proof found" signal that the leanCoP family emits.
///
/// Returns `Ok(true)` for theorem-status outputs, `Ok(false)` for
/// counter-satisfiable / refuted, and `Err` for inconclusive
/// (`GaveUp`, timeout, parse error).
pub(crate) fn parse_szs_or_native(output: &str) -> Result<bool> {
    let lower = output.to_ascii_lowercase();

    // SZS markers (TPTP convention).
    if lower.contains("szs status theorem") {
        return Ok(true);
    }
    if lower.contains("szs status countersatisfiable")
        || lower.contains("szs status counter-satisfiable")
        || lower.contains("szs status unsatisfiable")
    {
        return Ok(false);
    }
    if lower.contains("szs status gaveup") || lower.contains("szs status gave up") {
        return Err(anyhow::anyhow!(
            "Connection-method prover gave up: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ));
    }

    // Native leanCoP-family signals.
    if lower.contains("matrix proof found") || lower.contains("proof found") {
        return Ok(true);
    }
    if lower.contains("no proof") || lower.contains("not a theorem") {
        return Ok(false);
    }
    if lower.contains("error") || lower.contains("exception") {
        return Err(anyhow::anyhow!(
            "Connection-method prover error: {}",
            output.lines().take(10).collect::<Vec<_>>().join("\n")
        ));
    }

    Err(anyhow::anyhow!(
        "Connection-method prover output inconclusive: {}",
        output.lines().take(10).collect::<Vec<_>>().join("\n")
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};

    #[test]
    fn test_to_tptp_emits_axioms_and_conjecture() {
        let mut state = ProofState::default();
        state.context.axioms.push("p | ~ p".to_string());
        state.goals.push(Goal {
            id: "g0".to_string(),
            target: Term::Const("p".to_string()),
            hypotheses: vec![],
        });
        let tptp = to_tptp(&state);
        assert!(tptp.contains("fof(axiom_0, axiom, p | ~ p)."));
        assert!(tptp.contains("fof(conjecture, conjecture, p)."));
    }

    #[test]
    fn test_parse_szs_theorem() {
        let r = parse_szs_or_native("% SZS status Theorem\n").expect("expected Ok");
        assert!(r);
    }

    #[test]
    fn test_parse_szs_countersatisfiable() {
        let r = parse_szs_or_native("% SZS status CounterSatisfiable\n").expect("expected Ok");
        assert!(!r);
    }

    #[test]
    fn test_parse_szs_gaveup_is_err() {
        assert!(parse_szs_or_native("% SZS status GaveUp\n").is_err());
    }

    #[test]
    fn test_parse_native_proof_found() {
        let r = parse_szs_or_native("Matrix proof found").expect("expected Ok");
        assert!(r);
    }

    #[test]
    fn test_parse_native_no_proof() {
        let r = parse_szs_or_native("No proof.\n").expect("expected Ok");
        assert!(!r);
    }
}
