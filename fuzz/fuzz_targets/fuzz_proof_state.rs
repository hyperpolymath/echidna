// SPDX-License-Identifier: PMPL-1.0-or-later
//!
//! Fuzz target: ProofState JSON deserialization
//!
//! Exercise `serde_json::from_slice::<ProofState>` with arbitrary byte input.
//! A successful parse produces a ProofState; we then poke the resulting value
//! to ensure no implicit panics lurk in derived impls.  Deserialization errors
//! are expected and are *not* treated as failures.
//!
//! Coverage goals:
//! - All Serde derive paths in ProofState / Goal / Context / Term / Pattern
//! - ProofState::is_complete() logic (walks self.goals)
//! - ProofState::new() constructor path (exercised via a Term built from a
//!   deserialized Goal target, when at least one goal is present)

#![no_main]

use echidna::core::ProofState;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Attempt JSON deserialization.  Errors are fine; panics are bugs.
    let Ok(state): Result<ProofState, _> = serde_json::from_slice(data) else {
        return;
    };

    // Access every public field to catch any latent panics in derived Display
    // or other impls that run on first access.
    let _ = state.goals.len();
    let _ = state.is_complete();
    let _ = state.proof_script.len();
    let _ = state.metadata.len();

    // Walk goals: access each field, stringify the target Term.
    for goal in &state.goals {
        let _ = goal.id.len();
        let _ = goal.target.to_string(); // exercises the fmt::Display impl
        for hyp in &goal.hypotheses {
            let _ = hyp.name.len();
            let _ = hyp.ty.to_string();
            if let Some(body) = &hyp.body {
                let _ = body.to_string();
            }
        }
    }

    // Walk context.
    for theorem in &state.context.theorems {
        let _ = theorem.name.len();
        let _ = theorem.statement.to_string();
        let _ = theorem.aspects.len();
    }
    for axiom in &state.context.axioms {
        let _ = axiom.len();
    }
    for def in &state.context.definitions {
        let _ = def.to_string(); // exercises fmt::Display for Definition
    }

    // If there is at least one goal, build a fresh ProofState from its target
    // Term — exercises ProofState::new() with an arbitrary Term value.
    if let Some(first_goal) = state.goals.first() {
        let _fresh = ProofState::new(first_goal.target.clone());
    }

    // Re-serialise to JSON and back: round-trip must not panic.
    if let Ok(json) = serde_json::to_string(&state) {
        let _: Result<ProofState, _> = serde_json::from_str(&json);
    }
});
