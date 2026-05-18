# Proof Requirements

## Template ABI Cleanup (2026-03-29)
Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved {{PROJECT}}/{{AUTHOR}} placeholders and no domain-specific proofs.

When this project needs formal ABI verification, create domain-specific Idris2 proofs
following the pattern in repos like `typed-wasm`, `proven`, `echidna`, or `boj-server`.

## Current state (Updated 2026-05-18)

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
| E12 ProofState serialization losslessness | `verification/proofs/idris2/ProofStateSerialisation.idr` | Term/Goal/ProofState round-trip; encode injective; SExpr wire model; zero believe_me | I2 |
| VCL-UT query safety | `src/abi/EchidnaABI/VqlUt.idr` | L5 injection-free, L3 type-safe boundary | I2 |
| Extensive ABI | `src/abi/EchidnaABI/Types.idr`, `Foreign.idr`, `Layout.idr` | All ABI types, no believe_me | I2 |
| Stage 8a Trust-Kernel Monotonicity | `verification/proofs/idris2/TrustKernelMonotonicity.idr` | Reject/Warning danger → Level1; bad integrity → Level1; confirming≥2 + cert + small_kernel → ≥Level4; zero believe_me | I2 |
| Stage 8a Axiom-Policy Ordering | `verification/proofs/idris2/AxiomPolicyOrdering.idr` | worstDanger equalities for all 4 AxiomPolicy variants; isAcceptable ↔ danger≠Reject; PolicyLE monotone; zero believe_me | I2 |
| Stage 8a Clamp Trust Bounds | `verification/proofs/idris2/ClampTrustBounds.idr` | clamp_trust lower/upper bounds (1≤val≤5); monotonicity; fixed points (1→L1, 5→L5, 10→L5); surjectivity; zero believe_me | I2 |
| E10 Pareto frontier maximality | `verification/proofs/lean4/ParetoMaximality.lean` + `ParetoStrongMaximality.lean` | PO-1..PO-11 frontier soundness; PD-1..PD-3 strict `domCount` descent; PO-12 strong maximality (`dominated_by_frontier_member`: every non-frontier candidate dominated by a frontier member). Core Lean 4.13, no mathlib, no sorry. ECHIDNA-PARETO-DESCENT resolved without a Finset dependency. | L4 |
| E11 SHAKE3-512/BLAKE3 integrity | `verification/proofs/lean4/IntegrityVerification.lean` | PI-1..PI-12 integrity verification soundness; collision-resistance (PI-7, PI-9) stand as typeclass assumptions per zero-axiom policy. Core Lean 4.13, no sorry. NB: hash naming — implementation is SHAKE-256 squeezing 512 bits. | L4 |
| E13 Portfolio cross-checking completeness | `verification/proofs/lean4/PortfolioCompleteness.lean` | PR-1..PR-14 portfolio reconciliation completeness via `reconcile_cons`/`reconcile_nil` characterization lemmas. Core Lean 4.13, no sorry. | L4 |

### Remaining (not Idris2, not actionable by Claude)

| # | What | Prover | Status |
|---|------|--------|--------|
| E1 | Confidence scoring lattice (TrustLevel forms valid partial order) | L4 | Covered by ConfidenceLattice.lean |
| E8 | VQL-UT query safety (SEC, deeper layer) | I2 | Partially covered by VqlUt.idr |

## Recommended prover
- **Idris2** for ABI-level properties and prover dispatch correctness
- **Lean4** for algebraic properties of the confidence lattice
- **Agda** for metatheoretic properties of proof composition

## Priority
- **LOW** (was MEDIUM) — All E-series proofs are now discharged. Core trust pipeline (E2-E6) and Stage-8a (Idris2) complete; E10/E11/E13 (Lean4) landed and verified: `lake build` at `verification/proofs/lean4/` (Lean 4.13.0, no mathlib) is green from scratch, all 5 files 0 err / 0 warn / 0 sorry (#53, commit `760891e`). No outstanding proof obligations. E1/E8 above are covered/partially-covered informational entries, not gaps.
