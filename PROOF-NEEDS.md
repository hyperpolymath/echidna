# Proof Requirements

## Current state
- Extensive Idris2 ABI: `EchidnaABI/Types.idr` (655 lines), `EchidnaABI/Foreign.idr` (445 lines), `EchidnaABI/Layout.idr` (236 lines)
- Prover-specific ABI: `EchidnaABI/Provers/` — InteractiveAssistants, SmtSolvers, FirstOrderAtp, DeclarativeProvers, AutoActive, ConstraintSolvers
- `EchidnaABI/VqlUt.idr`, `EchidnaABI/Gnn.idr` — VQL and GNN type definitions
- `src/rust/verification/axiom_tracker.rs` — Tracks `sorry`/`Admitted` patterns (detection, not usage)
- `src/rust/provers/lean.rs` — Generates `sorry` as placeholder in Lean proof scaffolding (intentional — feeds goals to provers)
- `src/rust/provers/coq.rs` — Parses `Admitted` in Coq output (detection, not usage)
- No `believe_me` or `sorry` in the Idris2 ABI layer itself

## What needs proving
- **Confidence scoring soundness**: Prove that confidence levels in `confidence.rs` form a valid lattice and that `sorry` detection correctly downgrades confidence
- **Axiom tracking completeness**: Prove `axiom_tracker.rs` detects ALL dangerous patterns (no false negatives for `sorry`, `Admitted`, `believe_me`, `postulate`, `assert_total`, `unsafeCoerce`)
- **Prover dispatch correctness**: Prove that proof goals are dispatched to compatible provers (e.g., linear logic goals do not go to first-order ATP)
- **GNN embedding faithfulness**: Prove that proof-graph GNN embeddings preserve structural properties of the original proof tree
- **VQL-UT query safety**: Prove VQL queries are injection-free and type-safe at the ABI boundary
- **Proof composition**: Prove that combining sub-proofs from different provers preserves overall soundness (no implicit axiom conflicts)

## Recommended prover
- **Idris2** for ABI-level properties and prover dispatch correctness (dependent types model the prover taxonomy well)
- **Lean4** for confidence lattice algebraic properties
- **Agda** for metatheoretic properties of proof composition

## Priority
- **HIGH** — ECHIDNA is a proof verification orchestrator. A tool that checks proofs MUST itself be provably correct, or its guarantees are hollow. The axiom tracker and confidence scorer are the most critical targets.

## Template ABI Cleanup (2026-03-29)

Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved {{PROJECT}}/{{AUTHOR}} placeholders and no domain-specific proofs.
