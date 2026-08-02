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

## Echo-types audit (2026-06-01)

Per the estate-wide standing directive: every proof in any sibling repo
with an echo-types link must first audit `hyperpolymath/echo-types`,
reuse if applicable, extend upstream WITH proofs if not, then
cross-document. L3 (echo) obligations are load-bearing; L1/L4-only
obligations audit-and-record-as-not-relevant.

Echo-types layer scheme: **L1** regions / **L2** modality / **L3** echo
(structured residue / fibre shape) / **L4** dyadic (orders, products,
predicates, exhaustivity, monotonicity).

### Surface audited

All proof files under `proofs/agda/`, `proofs/coq/`, `proofs/isabelle/`,
`proofs/lean/`, `verification/proofs/idris2/`,
`verification/proofs/lean4/`, and `meta-checker/src/Echidna/`. The
Idris2 ABI under `src/abi/` is owner-intentional and out of scope (per
estate memo `echidna_src_abi_namespace_intentional`). Per-prover
fixture files under `tests/` are out of scope (smoke fixtures, not
obligations).

### Classification summary (26 obligation-bearing modules)

| Layer | Count | Status |
|-------|-------|--------|
| L1 (regions) | 0 | n/a — echidna is not a typed-substrate project |
| L2 (modality) | 0 | n/a — no modal logic surface in the verifier |
| **L3 (echo)** | **2** | **cross-ref added below** |
| L4 (dyadic) | 24 | audit-and-not-relevant; recorded here |

### L3 obligations (cross-reference to echo-types)

Two existing echidna theorems land in the echo-types EQUIV / INJ
shapes from `proofs/agda/EchoLossTaxonomy.agda`. The directive's
"reuse if applicable" path is satisfied by **cross-reference** rather
than rewrite — both theorems already discharge their content directly
under the relevant prover (Idris2), and the echo-types lemmas are
stated in Agda over abstract `f : A → B`, so the reuse is at the
**conceptual / classification** layer, not the proof-term layer.

| Echidna theorem | Echo-types analogue | Relationship |
|-----------------|---------------------|--------------|
| `Serialisation.roundtrip : (x : a) → decode (encode x) = Just x` (`verification/proofs/idris2/ProofStateSerialisation.idr:88`, E12) | `HasInverse` + `equiv-fibre-center` + `equiv-implies-injective` in `proofs/agda/EchoLossTaxonomy.agda` (EQUIV case); `EchoTotalCompletion` for the Σ-packaging | The roundtrip witness IS the EQUIV-shape data instantiated at the wire-encoding map. Losslessness ≡ trivial fibre at every wire value in the encode image. Echidna's proof is concrete-prover (Idris2 over wire `SExpr`); echo-types' is abstract (Agda, K-free). Same content, different stratum. |
| `kind_to_u8_injective` (`verification/proofs/idris2/ProverKindInjectivity.idr`, E6) | `inj-fibre-proj-unique` (INJ case re-export from `EchoImageFactorization` in `proofs/agda/EchoLossTaxonomy.agda`) | Injectivity of the discriminant map IS the INJ-case projection-uniqueness statement at the concrete domain `ProverKind` (105 variants) → `Nat`. Echidna does the concrete case split (no `believe_me`); echo-types names + classifies the shape. |

**Upstream extension status: not required.** Echo-types already
mechanises both the EQUIV (`HasInverse`) and INJ
(`inj-fibre-proj-unique`) cases in `EchoLossTaxonomy.agda`. The
echidna theorems are downstream *applications* of these classified
shapes, not new content owed back to the upstream library.

### L4 obligations (audit-and-not-relevant, recorded)

Every other obligation listed in **Completed proofs** above is L4:
order-theoretic (TrustLattice, DispatchOrdering, ClampTrustBounds,
ConfidenceLattice, ParetoMaximality, ParetoStrongMaximality),
monotonicity (AxiomMonotonicity, TrustKernelMonotonicity, AxiomPolicyOrdering),
exhaustivity / case-coverage (AxiomCompleteness,
AxiomTrackerCompleteness, AxiomSafety, MetaChecker), aggregation
(PortfolioConsistency, ParallelSoundness, Portfolio,
PortfolioCompleteness), composition / closure (ProofComposition,
SoundnessPreservation, CertificateChain, Dispatch), totality (BasicTotality,
IdentityLaws, TrustLevelSoundness, TrustLevel), or hash-integrity
algebra (IntegrityVerification). None involves loss-with-residue,
fibre structure, image factorisation, or any other echo-typed
construct, so the directive's L4 branch — "audit-and-record-as-not-
relevant" — is discharged by this paragraph.

### Cross-doc echo

* Echidna → echo-types: this section.
* Echo-types → echidna: `docs/echo-types/echidna-design-search-2026-04-28.adoc`
  already cross-references echidna (as a *tool* used over the
  echo-types corpus). No reverse proof-relevance link is owed back
  from echo-types because echidna does not add classified-shape
  content (the EQUIV/INJ cases echidna instantiates are already
  upstream).

### Related obligation (echidna#117)

`echidna#117` (`Client.res` AffineScript-TEA port — missing
`Http.fetch` / `Promise` / `Json` / `Dict` primitives) is a stdlib-
primitives meta-issue. Its blocker set is purely **L4 representation
/ transport** (encoding shapes for Http / Promise / JSON / Dict). It
carries no L3 obligation (no claim about fibre structure of the wire
transport), so audit-and-not-relevant applies. Recorded here so a
future port reviewer does not need to re-audit.
