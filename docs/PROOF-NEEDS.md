# Proof Requirements

## Template ABI Cleanup (2026-03-29)
Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved {{PROJECT}}/{{AUTHOR}} placeholders and no domain-specific proofs.

When this project needs formal ABI verification, create domain-specific Idris2 proofs
following the pattern in repos like `typed-wasm`, `proven`, `echidna`, or `boj-server`.

## believe_me audit (2026-05-18) — verified ground truth

A `grep '\bbelieve_me\b' --include='*.idr'` over the whole tree returns 21
hits. **All 21 are comments, docstrings, or string literals — there are
ZERO actual `believe_me`/`really_believe_me` proof escapes anywhere in the
Idris2 sources.** Breakdown:

- 19 are `--`/`|||` comments asserting the *absence* of the construct
  ("NO believe_me", "Zero believe_me", "without believe_me") in
  `src/abi/*.idr` and `verification/proofs/idris2/*.idr`.
- 2 are string literals in
  `verification/proofs/idris2/AxiomCompleteness.idr:144` and `:148`
  (`patternString Idris2BelieveMe = "believe_me"`,
  `patternString Idris2ReallyBelieveMe = "really_believe_me"`) — these are
  the prover's own *detector strings* for the pattern, not a use of it.

Conclusion: the "zero believe_me" claims on the rows below are **TRUE**.
The 21-figure is a naive-grep false positive (prose + the detector's own
pattern table), NOT 21 proof escapes. No proof row needed a truthfulness
correction on this axis. (`src/abi/echidnaabi.ipkg:14` likewise contains
the phrase "zero believe_me" in its `brief` field — also prose, also true.)

## Current state (Updated 2026-05-18)

### Completed proofs

| Proof | File | Covers | Prover |
|-------|------|--------|--------|
| E2 Axiom tracking completeness | `verification/proofs/idris2/AxiomCompleteness.idr` | 23 dangerous patterns across 7 provers; no false negatives; classify covers all constructors | I2 |
| E3 Dispatch pipeline ordering | `verification/proofs/idris2/DispatchOrdering.idr` | 6 stages (Integrity→Sandbox→Verify→Certs→Axioms→Confidence) strictly ordered | I2 |
| E4 Trust level soundness | `verification/proofs/lean4/ConfidenceLattice.lean` (L4) + `verification/proofs/idris2/TrustLevelSoundness.idr` (I2 NEW 2026-04-11) | Reject axiom → trust ≤ TrustLevel1; SoundnessWitness type makes unsound assignments a compile error | L4 + I2 — **the I2 half (`TrustLevelSoundness.idr`) is the constructive proof and stands. The L4 half is NOT verified: `lake build` 2026-05-18 shows `ConfidenceLattice.lean` (386 LoC) FAILS with 49 errors, the bulk caused by `unfold_let` (30 uses) being an `unknown tactic` in Lean 4.13.0 (`unfold_let` was removed). Mechanical token-swap to `simp only [instLE]` or `unfold instLE` was tested and makes it WORSE (104 errors — the follow-on `simp [LE.le, le]` then fails with a nested error), so the fix is NOT mechanical and was not applied. ConfidenceLattice.lean left untouched.** |
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

### Remaining (not Idris2, not actionable by Claude)

| # | What | Prover | Status |
|---|------|--------|--------|
| E1 | Confidence scoring lattice (TrustLevel forms valid partial order) | L4 | Covered by ConfidenceLattice.lean |
| E8 | VQL-UT query safety (SEC, deeper layer) | I2 | Partially covered by VqlUt.idr |
| E10 | Pareto frontier maximality | L4 | **`lake build` RUN 2026-05-18 (Lean 4.13.0, ~/.elan/bin) — FAILS.** `ParetoMaximality.lean` (465 LoC): 2 errors — `push_neg` at line 250 is `unknown tactic` (it is a **Mathlib** tactic; the lakefile declares "No mathlib dependency", so it is genuinely unavailable), causing an unsolved goal at 248. `ParetoStrongMaximality.lean` (207 LoC): 1 error — `unknown module prefix 'ParetoMaximality'` at line 28 (the cross-module `import`/`open` does not resolve under the current lakefile root setup; the 2026-05-11 "import path fix applied" note is NOT effective as built). NOT a mechanical fixup: E10 requires either adding a Mathlib dep (contradicts zero-mathlib policy) or hand-reproving the negation push in core Lean, plus fixing the inter-file module resolution. Tracking ticket: ECHIDNA-PARETO-DESCENT (math); #53 (tactic fixups). |
| E11 | SHAKE3-512/BLAKE3 integrity | L4 | **`lake build` RUN 2026-05-18 — FAILS.** `IntegrityVerification.lean` (384 LoC): 5 errors — `failed to synthesize` at lines 86 & 94 (missing instance — `integrityToBool`/`Decidable` plumbing; the planned `decide (s = IntegrityStatus.verified)` rewrite was either not applied or insufficient), and 3 `rewrite failed, did not find instance of the pattern` at lines 186/188/190 in the verifier soundness proof. Collision-resistance typeclasses (PI-7, PI-9) remain assumptions per zero-axiom policy. NOT an unambiguous mechanical fixup — the instance-synthesis failures require restructuring the decidability layer, not a one-token swap. NB: hash naming — implementation is SHAKE-256 squeezing 512 bits. |
| E13 | Portfolio cross-checking completeness | L4 | **`lake build` RUN 2026-05-18 — FAILS.** `PortfolioCompleteness.lean` (500 LoC): 31 errors. `push_neg` at line 344 is `unknown tactic` (Mathlib, unavailable — same root cause as E10); `not_not` at line 480 is `unknown identifier` (Mathlib lemma); plus ~12 `rewrite failed`/`rfl failed`/`unsolved goals` cascading from those. PR-14's `List.filter_eq_nil_iff` (line 478) and PR-10's `Option.some_injective` (line 379) resolve under core Lean 4.13.0 but their surrounding proofs still fail. NOT a mechanical fixup — needs the same Mathlib-vs-core decision as E10 plus genuine proof repair. |

## Recommended prover
- **Idris2** for ABI-level properties and prover dispatch correctness
- **Lean4** for algebraic properties of the confidence lattice
- **Agda** for metatheoretic properties of proof composition

## Priority
- **MEDIUM** (was HIGH) — Core trust pipeline proofs that are *Idris2/Agda*
  (E2, E3, E5, E6, E7, E9, E12, the Stage-8a trio, VqlUt, the I2 half of E4)
  are constructive and stand. The **Lean4 layer (E4-L4, E10, E11, E13) is
  unverified**: `lake build` was run 2026-05-18 with Lean 4.13.0
  (`~/.elan/bin`) and **all 5 Lean files fail to compile** (the Lean
  toolchain itself downloaded and built fine; these are real proof/source
  errors, not environment issues). Aggregate: ConfidenceLattice 49,
  ParetoMaximality 2, ParetoStrongMaximality 1, IntegrityVerification 5,
  PortfolioCompleteness 31. **Three independent root causes, none a safe
  one-token fix**: (1) `unfold_let` removed in Lean 4.13.0 (ConfidenceLattice,
  ×30 — token-swap tested, makes it worse); (2) Mathlib tactics/lemmas
  (`push_neg`, `not_not`) used while the lakefile declares zero-mathlib
  (E10, E13) — needs a Mathlib-vs-core policy decision; (3) instance
  synthesis / module-resolution failures (E11, ParetoStrongMaximality).
  The #53 / 2026-05-11 "expected to compile cleanly" and "mechanical fixup"
  notes were optimistic and are now corrected above. **No Lean source was
  modified** (one token-swap was tested on a copy and reverted; files are
  byte-identical to pre-audit). E10-E13 remain P2 and do not block the
  critical path, but #53 is materially larger than "API fixups".
