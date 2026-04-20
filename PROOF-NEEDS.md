# Proof Requirements

## Template ABI Cleanup (2026-03-29)
Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved {{PROJECT}}/{{AUTHOR}} placeholders and no domain-specific proofs.

When this project needs formal ABI verification, create domain-specific Idris2 proofs
following the pattern in repos like `typed-wasm`, `proven`, `echidna`, or `boj-server`.

## Current state (Updated 2026-04-11)

### Completed proofs

| Proof | File | Covers | Prover |
|-------|------|--------|--------|
| E2 Axiom tracking completeness | `verification/proofs/idris2/AxiomCompleteness.idr` | 23 dangerous patterns across 7 provers; no false negatives; classify covers all constructors | I2 |
| E3 Dispatch pipeline ordering | `verification/proofs/idris2/DispatchOrdering.idr` | 6 stages (Integrity→Sandbox→Verify→Certs→Axioms→Confidence) strictly ordered | I2 |
| E4 Trust level soundness | `verification/proofs/lean4/ConfidenceLattice.lean` (L4) + `verification/proofs/idris2/TrustLevelSoundness.idr` (I2 NEW 2026-04-11) | Reject axiom → trust ≤ TrustLevel1; SoundnessWitness type makes unsound assignments a compile error | L4 + I2 |
| E5 Prover dispatch compatibility | `verification/proofs/idris2/DispatchCorrectness.idr` | Logic family compatibility; linear logic ↛ first-order ATP | I2 |
| E6 ProverKind discriminant injectivity | `verification/proofs/idris2/ProverKindInjectivity.idr` | 105 variants, no collisions in kind_to_u8 | I2 |
| E7 GNN embedding faithfulness | `src/abi/EchidnaABI/Gnn.idr` | Structural properties, feature bounds, score normalisation | I2 |
| E9 Proof composition soundness | `proofs/agda/ProofComposition.agda` | Soundness preservation, axiom conflict detection | Agda |
| VCL-UT query safety | `src/abi/EchidnaABI/VqlUt.idr` | L5 injection-free, L3 type-safe boundary | I2 |
| Extensive ABI | `src/abi/EchidnaABI/Types.idr`, `Foreign.idr`, `Layout.idr` | All ABI types, no believe_me | I2 |

### Remaining (not Idris2, not actionable by Claude)

| # | What | Prover | Status |
|---|------|--------|--------|
| E1 | Confidence scoring lattice (TrustLevel forms valid partial order) | L4 | Covered by ConfidenceLattice.lean |
| E8 | VQL-UT query safety (SEC, deeper layer) | I2 | Partially covered by VqlUt.idr |
| E10 | Pareto frontier maximality | L4 | Not started |
| E11 | SHAKE3-512/BLAKE3 integrity | L4 | Not started |
| E12 | ProofState serialization losslessness | I2 | Not started |
| E13 | Portfolio cross-checking completeness | L4 | Not started |

## Recommended prover
- **Idris2** for ABI-level properties and prover dispatch correctness
- **Lean4** for algebraic properties of the confidence lattice
- **Agda** for metatheoretic properties of proof composition

## Priority
- **MEDIUM** (was HIGH) — Core trust pipeline proofs (E2-E6) are now complete. E10-E13 are P2 and do not block the critical path.
