# ECHIDNA Correctness Architecture

**Author**: Claude Opus 4.5 (architecture design)
**Date**: 2026-02-05
**Purpose**: Design for absolute confidence in ECHIDNA's correctness.
This addresses the core question: how can users trust that ECHIDNA's
outputs are mathematically sound, not "AI hallucinations"?

---

## The Core Guarantee

**ECHIDNA's soundness invariant**: ML only _suggests_ — provers _verify_.

No proof can be accepted unless a formal theorem prover has mechanically
checked every step. The ML layer is advisory only. Even if the ML model
is completely wrong, the worst outcome is wasted compute, never a false proof.

This is fundamentally different from LLMs generating "proofs" — ECHIDNA
uses real theorem provers (Coq, Lean, Isabelle, etc.) as the final arbiter.

---

## Five Layers of Correctness Assurance

### Layer 1: Prover Verification (FOUNDATION)

Every tactic suggestion from ML is submitted to a real theorem prover.
The prover either accepts (proof step valid) or rejects (invalid).
This is a binary gate — no "maybe" or "probably correct".

**Implementation**: `src/rust/provers/*.rs` — each of 12 backends
has `apply_tactic()` which returns `Ok(new_state)` or `Err(rejection)`.

**Guarantee**: No false proofs. Period. The prover's type checker is
the ultimate authority.

### Layer 2: Multi-Prover Cross-Validation (REDUNDANCY)

For high-assurance proofs, submit the same theorem to multiple provers.
If Coq, Lean, and Isabelle all accept the proof, confidence is extremely high.

**Implementation**: `src/rust/agent/consensus.rs` (planned for v2.0)

```
Proof accepted by:
  - 1 prover: Standard confidence
  - 2 provers: High confidence
  - 3+ provers: Maximum confidence (different foundations agree)
```

**Guarantee**: Independent verification across different logical foundations
(constructive type theory, classical HOL, SMT).

### Layer 3: Anomaly Detection (EARLY WARNING)

Detect when ML is behaving abnormally before provers waste time.

**Implementation**: `src/rust/anomaly_detection.rs` — 7 anomaly types:
- Overconfidence (ML claims >95% but prover rejects)
- Disagreement (multiple ML models disagree)
- Circular reasoning (tactic chain loops)
- Complexity explosion (proof tree growing without progress)
- Distribution shift (input unlike training data)
- Repetition (same tactic suggested repeatedly)
- Timeout (ML inference too slow)

**Guarantee**: Early detection of ML failures. Does not replace prover
verification — complements it.

### Layer 4: Property-Based Testing (INVARIANTS)

Automatically generated test cases verify core invariants hold.

**Implementation**: `tests/property_tests.rs` using PropTest:
- Confidence scores always in [0, 1]
- Tactic serialization roundtrips correctly
- Deterministic: same input → same output
- No empty suggestions for valid goals
- Parsing handles all valid syntax
- Memory bounded (no leaks)

**Guarantee**: Statistical confidence that implementation matches spec.

### Layer 5: Formal Proof Validator (META-VERIFICATION)

An independently-implemented proof checker in Idris2 with dependent types.

**Implementation**: `src/idris/ProofTerm.idr` + `src/idris/Validator.idr`
- AST for dependent type theory proof terms
- Type checker with totality guarantee
- Detects: circular reasoning, type mismatches, invalid tactics
- Soundness theorem signature (to be fully proven)

**Guarantee**: Even if the Rust/Julia code has bugs, the Idris2 validator
independently checks proof terms. A proof accepted by both the prover
AND the Idris2 validator is extremely unlikely to be false.

---

## Correctness Certification Pipeline (v2.0)

For every proof ECHIDNA produces, generate a **proof certificate**:

```json
{
  "theorem": "forall n : nat, n + 0 = n",
  "proof_steps": [...],
  "prover": "coq-8.19",
  "prover_output": "<raw prover transcript>",
  "cross_validated_by": ["lean4", "isabelle"],
  "ml_confidence": 0.87,
  "anomaly_flags": [],
  "idris2_validation": "PASSED",
  "certificate_hash": "sha256:abc123...",
  "provenance": {
    "echidna_version": "2.0.0",
    "model_version": "transformer-v1",
    "training_data_hash": "sha256:def456...",
    "timestamp": "2026-03-15T10:30:00Z"
  }
}
```

**Key properties**:
1. **Machine-checkable**: Anyone can replay the proof steps in the prover
2. **Provenance chain**: Full history of how the proof was generated
3. **Tamper-evident**: SHA-256 hash of entire certificate
4. **Reproducible**: Same inputs always produce same proof

---

## Compute Layer Integration (Julia/Chapel/Rust)

### Current Architecture

```
Chapel (ISOLATED)     Julia ML (HTTP)     Rust Core
   |                     |                   |
   | (no connection)     |<-- HTTP POST ---->|
   |                     |   port 8090       |
   |                                         |
   |                    12 Prover Backends <--|
```

### Recommended Architecture (v2.0)

```
Chapel HPC Layer (parallel orchestration)
   |
   |-- C FFI --> Rust Core (prover execution)
   |                |
   |                |--> Prover 1 (Coq)    } executed in
   |                |--> Prover 2 (Lean)   } parallel by
   |                |--> Prover 3 (Z3)     } Chapel coforall
   |                |--> ...               }
   |
   |-- HTTP --> Julia ML (neural guidance)
                   |
                   |--> GNN encoder (proof graph structure)
                   |--> Transformer (premise selection)
                   |--> Confidence estimation (Monte Carlo dropout)
```

**How it works**:
1. Chapel receives a theorem to prove
2. Chapel calls Julia for initial neural guidance (which provers + tactics to try)
3. Chapel launches `coforall` over recommended provers
4. Each parallel task calls Rust via C FFI to execute real prover
5. Chapel collects results, selects best proof
6. If no proof found, Chapel calls Julia for refined suggestions (beam search)
7. Repeat until proof found or timeout

**Why this is better than current**:
- Chapel gets REAL provers (not simulated success/failure)
- Julia neural guidance focuses search (not random exploration)
- Rust handles prover lifecycle and safety
- All three layers contribute their strength:
  - Julia: intelligence (which tactics to try)
  - Chapel: parallelism (try many at once)
  - Rust: safety (correct prover execution)

### Julia/Chapel Interaction Recommendation

**Option A: HTTP (Simpler, Recommended for v2.0)**
- Chapel calls Julia HTTP API for neural suggestions
- Same API that Rust already uses
- Pro: No new FFI code needed
- Con: Network overhead per request

**Option B: Shared Memory via Rust (Advanced, v3.0)**
- Julia writes neural rankings to shared memory
- Chapel reads via Rust C FFI bridge
- Pro: Zero-copy, minimum latency
- Con: Complex memory management

**Recommendation**: Start with HTTP (Option A). The latency (~1ms localhost)
is negligible compared to prover execution time (~100ms-10s). Move to
shared memory only if profiling shows HTTP is a bottleneck.

---

## Applying ECHIDNA to Absolute Zero (Test Case)

### Why Absolute Zero is the Perfect Test Case

1. **Well-defined theorems**: 81 completed Coq proofs to validate against
2. **Known gaps**: 19 Admitted proofs that ECHIDNA could attempt
3. **Multi-domain**: Category theory, lambda calculus, quantum, thermodynamics
4. **Ground truth**: We know which proofs are correct (Qed) and which are incomplete
5. **Shared author**: Same repository standards, same proof style

### Integration Plan

#### Phase 1: Validation (verify ECHIDNA against known proofs)

Feed each of the 81 completed Coq proofs to ECHIDNA:
- Does ECHIDNA's ML suggest the same tactics used in the actual proofs?
- Does ECHIDNA find the proofs faster or slower than the actual proof scripts?
- Are there any false positives (ECHIDNA claims proof but Coq rejects)?

**Expected outcome**: 0 false positives (soundness invariant), ML accuracy
measurable against ground truth.

#### Phase 2: Discovery (attempt the 19 Admitted proofs)

Feed each of the 19 Admitted proofs to ECHIDNA:
- Priority order (from PROOF-INSIGHTS.md):
  1. quantum_state_eq_refl/sym/trans (need Cexp axioms)
  2. FilesystemCNO.v 6 proofs
  3. MalbolgeCore.v 1 proof
  4. quantum_cno_composition (fix intermediate)
  5. global_phase_is_cno
  6. LandauerDerivation.v 3 proofs (hardest)
  7. y_not_cno (may be unprovable constructively)

**Expected outcome**: ECHIDNA may complete some of the easier proofs
automatically. The harder ones (Landauer, y_not_cno) are likely beyond
current ML capability but provide excellent benchmark data.

#### Phase 3: Cross-Validation (multi-prover verification)

For proofs that exist in both Coq and Lean 4:
- Verify that both provers accept equivalent proof terms
- Use ECHIDNA's multi-prover consensus to increase confidence
- Report any discrepancies (which would indicate a bug in one formalization)

#### Phase 4: Correctness Certification

Generate proof certificates for all Absolute Zero theorems:
- Machine-checkable certificates for each of the 81 Coq proofs
- Cross-validation with Lean 4 versions where available
- Publish certificates alongside the proofs in the repository
- This demonstrates ECHIDNA's certification pipeline on a real project

### Concrete First Steps (for Sonnet)

1. Create `examples/absolute-zero/` in the echidna repo
2. Copy 3 representative Coq proof files (CNO.v, LambdaCNO.v, StatMech.v)
3. Add extraction script to parse proof states and tactics
4. Feed to Julia training pipeline to expand training data
5. Test ECHIDNA's suggestions against known proofs
6. Report accuracy metrics

---

## Trust Communication Strategy

### For Skeptics ("This is just LLM bullshit")

Show them:
1. ECHIDNA uses REAL theorem provers (Coq, Lean, Isabelle)
2. Every proof step is mechanically checked — no shortcuts
3. The ML model cannot override the prover — it can only suggest
4. Property-based tests catch implementation bugs
5. Idris2 validator independently checks proof terms
6. Anomaly detection catches ML failures early
7. Multi-prover consensus validates across different foundations

### For Regulators ("How do we know this is safe?")

Provide:
1. Proof certificates with full provenance chain
2. SHA-256 hashes for tamper-evidence
3. Reproducible proof generation
4. Audit trail of every ML suggestion + prover decision
5. Independent validation by Idris2 formal checker
6. Performance benchmarks showing regression detection

### For Users ("Can I trust this in production?")

Demonstrate:
1. 99 unit tests + 38 integration tests passing
2. Property-based testing of core invariants
3. Four-layer trust framework documentation
4. Clear error messages when proofs fail
5. Confidence scores with uncertainty quantification
6. Fallback to manual proving when ML confidence is low

---

## Summary

ECHIDNA's correctness comes from **defense in depth**:

| Layer | What it catches | Cost of failure |
|-------|----------------|-----------------|
| Prover verification | Invalid proof steps | Zero (binary gate) |
| Multi-prover consensus | Prover-specific bugs | Very low (redundancy) |
| Anomaly detection | ML misbehavior | Low (early warning) |
| Property testing | Implementation bugs | Low (CI catches) |
| Formal validator | Systematic errors | Very low (independent check) |

**The key insight**: No single layer needs to be perfect.
The combination of multiple independent layers makes the probability
of a false proof astronomically low.

A proof accepted by Coq AND Lean AND Isabelle AND the Idris2 validator
AND passing anomaly detection AND satisfying property-based tests
has essentially zero chance of being incorrect.
