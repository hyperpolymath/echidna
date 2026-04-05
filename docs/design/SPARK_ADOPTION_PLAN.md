<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# SPARK Adoption Plan — Echidna Trust Pipeline

**Status:** Proposal
**Target:** `src/rust/verification/` (7 modules, ~2600 LoC)
**Filed:** 2026-04-05
**Owner:** Jonathan D.A. Jewell

## Why

The hyperpolymath standard is **SPARK integration by default when touching Rust/Ada
code**. Echidna is a theorem prover; its own verification layer deciding whether
a proof is *trustworthy* is exactly the code where formal verification pays off.

The rest of echidna is not a good SPARK target:
- Prover backends (52 files, ~20K LoC) — shell-out glue, domain is external
- HTTP server (server.rs, interfaces/) — network I/O, dynamic
- GNN integration, agent/, neural.rs — ML scoring, heuristic
- CLI, REPL, config — presentation layer

The trust pipeline is different: it makes **invariant-heavy judgement calls**
("is this proof sound?", "what is the confidence level?", "does this certificate
check out?") and those judgements determine whether downstream consumers trust
a result. A bug here turns a theorem prover into a liar.

## Target surface

`src/rust/verification/` — 7 modules, ~2600 LoC.

| Module | LoC | Role | Invariant-heavy? |
|---|---|---|---|
| `axiom_tracker.rs` | 487 | Detects dangerous patterns (sorry, Admitted, believe_me, type-in-type) per prover | **Yes** — soundness gate |
| `certificates.rs` | 413 | Verifies Alethe/DRAT/LRAT/TSTP certificates | **Yes** — trust root |
| `confidence.rs` | 259 | 5-level trust hierarchy, confidence aggregation | **Yes** — ordering invariants |
| `mutation.rs` | 339 | Mutation testing: perturb spec, check prover still rejects | Partial — methodology |
| `pareto.rs` | 247 | Pareto frontier over (time, confidence, axioms-used) | **Yes** — frontier correctness |
| `portfolio.rs` | 375 | Cross-checks multiple solvers, flags disagreement | **Yes** — consensus logic |
| `statistics.rs` | 464 | Bayesian timeout estimation, statistical tracking | Partial — estimator properties |

The five "Yes" modules are where SPARK delivers the most value. The two "Partial"
modules have mathematical content worth proving but can wait a cycle.

## Toolchain candidates

Four realistic options exist for verifying Rust. None is perfect; each involves
trade-offs that matter for this codebase.

### 1. Creusot (SMT-based, annotated Rust)

- **What:** Deductive verifier — annotate Rust functions with contracts
  (`#[requires]`, `#[ensures]`) in a Rust-embedded logic. Compiles to Why3,
  discharged by Z3/CVC5/Alt-Ergo.
- **Strengths:**
  - Closest thing to SPARK/Ada for Rust (SMT-based deductive verification)
  - Echidna already ships Z3, CVC5, Alt-Ergo backends — same solvers
  - Function-level reasoning matches the pipeline's modular structure
  - Handles `Vec`, `HashMap`, iterators — the types actually used here
- **Weaknesses:**
  - Pre-1.0, API changes between releases
  - Requires a nightly toolchain pinned to specific versions
  - Limited async support — verification is opt-in, not whole-crate
- **Fit score:** 8/10

### 2. Prusti (Viper-based, annotated Rust)

- **What:** Viper-backed verifier from ETH Zürich. Specification via
  `#[requires]`/`#[ensures]` + separation logic primitives.
- **Strengths:**
  - Mature research project, well-documented
  - Handles ownership/borrow-checker invariants natively
  - Good for memory-safety properties
- **Weaknesses:**
  - Viper is less familiar than SMT; debugging requires learning a new backend
  - Weak on algebraic/mathematical properties (what we care about here)
  - Slower verification cycle
- **Fit score:** 6/10

### 3. Verus (Z3, full-crate verification)

- **What:** Whole-crate verifier from Microsoft Research. Annotations live
  inside `verus!{ }` macro blocks.
- **Strengths:**
  - Newest and most actively developed
  - Designed for systems code, not toy examples
  - Strong linear/ghost state support
  - Used in real production systems (StorageSystem verification)
- **Weaknesses:**
  - Whole-crate model conflicts with "annotate only the trust pipeline"
  - Requires significant refactoring to adopt incrementally
  - Ghost variables + exec separation is an unfamiliar discipline
- **Fit score:** 7/10

### 4. Kani (model checking)

- **What:** Bounded model checker (backed by CBMC) — proves absence of panics,
  overflow, UB within a bound.
- **Strengths:**
  - Property-based testing with exhaustive inputs
  - No proof writing — just `#[kani::proof]` harnesses
  - Catches real bugs quickly
- **Weaknesses:**
  - Bounded only — can't prove functional correctness of non-bounded inputs
  - Not equivalent to SPARK/deductive verification
  - Better as a complement than a replacement
- **Fit score (as primary):** 4/10
- **Fit score (as complement):** 9/10

### Recommendation

**Adopt Creusot as primary, Kani as complement.**

- **Creusot** handles the deductive reasoning for invariants, ordering, and
  certificate correctness. Aligns with SPARK's philosophy. Uses solvers
  echidna already ships (meta-dogfooding).
- **Kani** runs alongside as a sanity layer — harness every public function
  in `verification/`, prove-no-panic for realistic input bounds.
- **Verus** and **Prusti** stay on the watchlist. If Creusot stalls, Verus is
  the next pick (higher ceiling, higher adoption cost).

This is a **dual-tool strategy**, not a monoculture. The echidna trust
pipeline already uses 48 provers; using 2 for its own verification is
coherent.

## Adoption sequence

Five milestones. Each one independently valuable; project can stop at any
milestone and ship what's done.

### M1 — Toolchain bring-up (1 session)

- Install Creusot + Kani
- Pin Rust toolchain in `rust-toolchain.toml` (Creusot needs specific nightly)
- Add `[workspace.metadata.creusot]` config
- Add `cargo creusot`, `cargo kani` recipes to `Justfile`
- CI workflow `.github/workflows/formal-verification.yml` (non-blocking, report-only)
- One trivial verified function as smoke test (`confidence::level_ordering_reflexive`)

**Success criterion:** `just verify-trust-pipeline` runs clean on zero real
functions, one trivial lemma discharges.

### M2 — axiom_tracker.rs (1-2 sessions)

Smallest invariant-heavy module. Candidate properties to prove:

1. **Completeness:** Every `DangerLevel::Reject` pattern is flagged whenever it
   appears in input (modulo the comment/marker exclusions — those are encoded
   as pre-conditions).
2. **No false reject:** Patterns classified `DangerLevel::Safe` or not in the
   pattern set never produce a `Reject` finding.
3. **Scaffold marker soundness:** Lines containing `ECHIDNA_SCAFFOLD_SORRY` are
   always skipped, regardless of other sorry presence. (Just proven by test —
   replace test with Creusot contract.)
4. **Monotonicity:** Adding dangerous patterns to a policy never removes
   findings from a prior scan.

**Success criterion:** 4 of 4 properties verified; existing 9 unit tests pass
unchanged.

### M3 — confidence.rs + pareto.rs (2 sessions)

Ordering invariants are textbook Creusot territory.

**confidence.rs:**
- `TrustLevel` enum is totally ordered
- `combine_confidence(a, b)` is commutative and associative
- Weakest-link semantics: `combine(low, high) = low`
- Never promotes below input floor

**pareto.rs:**
- `ParetoFrontier` never contains dominated candidates
- `add_candidate` preserves the Pareto property
- Frontier is monotone-shrinking under `dominates_strictly`

**Success criterion:** All ordering properties discharge by SMT within 30s each.

### M4 — portfolio.rs (2-3 sessions)

Consensus logic for cross-checking. Hardest property to state cleanly.

- **Agreement:** If all solvers return `Sat`, portfolio returns `Sat`
- **Disagreement flag:** Mixed results trigger `PortfolioResult::Divergent`
- **Timeout handling:** Single-solver timeout doesn't produce a `Proved` result
- **Majority vote:** If portfolio policy is `Majority`, result matches strict
  majority or returns `Divergent`

**Risk:** Portfolio spawns async solver tasks; Creusot is weak on async. May
need to extract pure decision logic into separate functions to verify.

**Success criterion:** Pure decision-core properties verified; async dispatch
kept outside the verified boundary and explicitly documented.

### M5 — certificates.rs (2-3 sessions)

Hardest target — certificate verification is a trust root.

- **Format detection:** `CertificateFormat::detect` is injective (no format
  ambiguity on well-formed input)
- **Round-trip:** `parse(serialize(c)) = c` for each format
- **Rejection:** Malformed certificates never pass verification
- **Audit chain:** Every accepted certificate carries a non-empty axiom list

**Risk:** DRAT/LRAT parsing is complex. May need external oracles (pre-verified
parsers) or restrict verification to the **acceptance logic** rather than the
parser itself.

**Success criterion:** Acceptance logic fully verified; parser stays in a
clearly-marked "trusted parser" boundary.

## Preconditions

Before M1:

- [ ] Nightly Rust toolchain decision (pin via `rust-toolchain.toml` — Creusot
  requires specific versions)
- [ ] Agreement that non-blocking CI is acceptable for M1-M2 (formal
  verification failures don't break merges until M5 lands)
- [ ] Decision: where do verified proofs live? Options: inline as contracts
  (Creusot default) OR separate `verification/proofs/` directory

Before M5:

- [ ] Trust boundary documented: which parsers are trusted-not-verified?
- [ ] Round-trip property tests exist (QuickCheck/proptest) as ground truth

## Risks

1. **Toolchain churn.** Creusot is pre-1.0. A breaking release mid-adoption
   could force rework. **Mitigation:** pin version, upgrade deliberately.

2. **Async boundary.** Several modules use `tokio`; Creusot doesn't verify
   async. **Mitigation:** refactor to pure decision cores + async shells;
   verify cores only.

3. **Over-specification.** Writing contracts for code that already has tests
   can feel like duplication. **Mitigation:** pick properties tests *can't*
   express (ordering, monotonicity, completeness over infinite input sets).

4. **Dogfooding loop.** Echidna's SMT solvers verify echidna's SMT-dispatched
   proofs. Not circular (different proof obligations), but worth watching.
   **Mitigation:** at M5, have Kani *and* a second SMT solver cross-check.

## Non-goals

- **Not verifying prover backends** (`provers/*.rs`). They shell out to
  external tools; the trust gap is in the external tool, not our glue.
- **Not verifying HTTP handlers** or GraphQL/gRPC/REST interfaces. Network
  code, dynamic by nature.
- **Not replacing the Agda meta-checker.** Agda verifies 30+ trust-pipeline
  properties at the specification level. Creusot verifies the Rust
  implementation matches that specification. Complementary, not
  substitutable.
- **Not touching the Idris2 ABI.** Already formally verified by its own type
  system; `believe_me` count is confirmed zero (E1).

## Open questions

- **Q1:** Do we pin Creusot to a stable release or track head? *Proposal:
  pinned release, reviewed quarterly.*
- **Q2:** Who reviews verification contracts? They're code; they need
  review too. *Proposal: same PR review process as ordinary Rust.*
- **Q3:** How do we handle failures in CI when SMT can't discharge within
  timeout? *Proposal: non-blocking report at M1-M2, blocking from M3.*
- **Q4:** Is there value in also emitting Coq/Lean proof certificates from
  the verified pipeline? I.e. "here is the proof echidna made, verified by
  echidna's own verifier, checkable in Coq." *Open — could be a M6.*

## First-action checklist (if approved)

1. [ ] Decide Creusot-vs-Verus (owner: Jonathan)
2. [ ] Pin Rust nightly in `rust-toolchain.toml`
3. [ ] Install + test Creusot: `cargo install creusot`
4. [ ] Add `just verify-trust-pipeline` recipe
5. [ ] Write first contract on `confidence::TrustLevel` ordering
6. [ ] Run, debug, document gotchas, commit
7. [ ] Open PR with M1 deliverable + updated this plan

## References

- Creusot: https://github.com/creusot-rs/creusot
- Prusti: https://github.com/viperproject/prusti-dev
- Verus: https://github.com/verus-lang/verus
- Kani: https://github.com/model-checking/kani
- SPARK 2014 Reference Manual: https://docs.adacore.com/spark2014-docs/
- Existing echidna Agda meta-checker: `proofs/agda/`, `meta-checker/src/Echidna/AxiomSafety.agda`
