# Proof Requirements

## Template ABI Cleanup (2026-03-29)
Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved {{PROJECT}}/{{AUTHOR}} placeholders and no domain-specific proofs.

When this project needs formal ABI verification, create domain-specific Idris2 proofs
following the pattern in repos like `typed-wasm`, `proven`, `echidna`, or `boj-server`.

## Current state (Updated 2026-04-04)
- **Confidence scoring soundness**: Proven in `verification/proofs/lean4/ConfidenceLattice.lean`. (Lattice, monotonicity, Reject->Level1)
- **Axiom tracking completeness**: Proven in `verification/proofs/idris2/AxiomCompleteness.idr`. (23 patterns, no false negatives). `unsafeCoerce` added to `axiom_tracker.rs`.
- **Prover dispatch correctness**: Proven in `verification/proofs/idris2/DispatchCorrectness.idr`. (Logic family compatibility). `DispatchOrdering.idr` (Pipeline stages).
- **Proof composition**: Proven in `proofs/agda/ProofComposition.agda`. (Soundness preservation, axiom conflict detection).
- **VCL-UT query safety**: Proven in `EchidnaABI/VqlUt.idr`. (L5 Injection-free, L3 Type-safe boundary).
- **GNN embedding faithfulness**: Documented in `EchidnaABI/Gnn.idr`. (Structural properties, feature bounds, score normalisation).
- Extensive Idris2 ABI: `EchidnaABI/Types.idr` (655 lines), `EchidnaABI/Foreign.idr` (445 lines), `EchidnaABI/Layout.idr` (236 lines)

## What needs proving
- **Confidence scoring soundness**: Prove that confidence levels in `confidence.rs` form a valid lattice and that `sorry` detection correctly downgrades confidence
- **Axiom tracking completeness**: Prove `axiom_tracker.rs` detects ALL dangerous patterns (no false negatives for `sorry`, `Admitted`, `believe_me`, `postulate`, `assert_total`, `unsafeCoerce`)
- **Prover dispatch correctness**: Prove that proof goals are dispatched to compatible provers (e.g., linear logic goals do not go to first-order ATP)
- **GNN embedding faithfulness**: Prove that proof-graph GNN embeddings preserve structural properties of the original proof tree
- **VCL-UT query safety**: Prove VCL queries are injection-free and type-safe at the ABI boundary
- **Proof composition**: Prove that combining sub-proofs from different provers preserves overall soundness (no implicit axiom conflicts)

## Recommended prover
- **Idris2** for ABI-level properties and prover dispatch correctness (dependent types model the prover taxonomy well)
- **Lean4** for confidence lattice algebraic properties
- **Agda** for metatheoretic properties of proof composition

## Priority
- **HIGH** - ECHIDNA is a proof verification orchestrator. A tool that checks proofs MUST itself be provably correct, or its guarantees are hollow. The axiom tracker and confidence scorer are the most critical targets.
