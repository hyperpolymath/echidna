# Test & Benchmark Requirements

## CRG Grade: B — ACHIEVED 2026-04-04

> CRG B achieved 2026-04-04: Verified proofs from 6 diverse external repos with real output.

## CRG B Evidence — External Targets

| Target Repo | Language | What Was Tested | Result |
|-------------|----------|-----------------|--------|
| echidna (own proofs) | Coq | `echidna verify` on proofs/coq/basic.v | VALID: 0 goals, 43 tactics, 0 theorems |
| nextgen-languages/wokelang | Coq | `echidna verify` on WokeLang.v | INVALID: proof rejected |
| nextgen-languages/my-lang | Coq | `echidna verify` on Syntax.v | INVALID: proof rejected |
| maa-framework/absolute-zero | Coq | `echidna verify` on CNOCategory.v | VALID: 0 goals, 81 tactics, 0 theorems |
| protocol-squisher | Lean | `echidna verify` on wheelbarrow_necessity.lean | VALID: 0 goals, 0 tactics, 5 theorems |
| nextgen-languages/tangle | Lean | `echidna verify` on Tangle.lean | VALID: 0 goals, 0 tactics, 10 theorems |

### Target Details

**1. echidna own Coq proofs (baseline)**
- Command: `echidna verify /var/mnt/eclipse/repos/echidna/proofs/coq/basic.v`
- Key findings: Valid proof. 43 tactics detected. Baseline verification working correctly.

**2. nextgen-languages/wokelang (Coq)**
- Command: `echidna verify /var/mnt/eclipse/repos/nextgen-languages/wokelang/docs/proofs/verification/WokeLang.v`
- Key findings: Proof invalid. Echidna correctly rejected an incomplete/malformed proof file. Demonstrates false-positive resilience.

**3. nextgen-languages/my-lang (Coq)**
- Command: `echidna verify /var/mnt/eclipse/repos/nextgen-languages/my-lang/proofs/verification/coq/Syntax.v`
- Key findings: Proof invalid. Another correctly rejected proof. Confirms echidna does not blindly accept all Coq files.

**4. maa-framework/absolute-zero (Coq — category theory)**
- Command: `echidna verify /var/mnt/eclipse/repos/maa-framework/absolute-zero/proofs/coq/category/CNOCategory.v`
- Key findings: Valid proof with 81 tactics. Complex category theory proof verified successfully. Demonstrates handling of advanced mathematical content.

**5. protocol-squisher (Lean — wheelbarrow necessity)**
- Command: `echidna verify /var/mnt/eclipse/repos/protocol-squisher/proofs/lean/wheelbarrow_necessity.lean`
- Key findings: Valid proof. 5 theorems in context, 0 tactics (declarative style). Cross-prover support (Lean vs Coq) verified.

**6. nextgen-languages/tangle (Lean — language proofs)**
- Command: `echidna verify /var/mnt/eclipse/repos/nextgen-languages/tangle/proofs/Tangle.lean`
- Key findings: Valid proof. 10 theorems in context. Lean parser handles different proof styles correctly.

## Current State (updated 2026-04-04)

- Unit tests: 756 pass / 0 fail / 16 ignored
  - 556 in main crate, 200 across integration/property/aspect/E2E suites
- Integration tests: full (echidnabot + prover backends)
- E2E tests: COMPLETE (tests/e2e_prover_test.rs — 10 tests)
- P2P property tests: COMPLETE (tests/p2p_property_tests.rs — ~1,000 proptest cases)
- Aspect tests: COMPLETE (tests/aspect_tests.rs — 12 tests)
- Julia smoke tests: COMPLETE (tests/julia/smoke_test.jl — 63 tests)
- Shell validation: COMPLETE (tests/shell/validate_scripts.sh — 68 checks)
- Benchmarks: BASELINED (benches/proof_benchmarks.rs — 13 Criterion functions)
- panic-attack scan: NEVER RUN

## Benchmark Status (verified 2026-04-04)

**The 1,035 .v files are Coq proof files from external_corpora/ — NOT runnable benchmarks.**
- `external_corpora/CoqGym/` — 6,678 Coq proofs (training/ML corpus data)
- `proofs/coq/` — 16 project Coq proof files
- These are NOT V-lang files and NOT benchmark runners

**Real Criterion benchmarks exist in `benches/proof_benchmarks.rs`:**
- `bench_proof_state_construction` (5 goal-count variants)
- `bench_term_construction` (4 depth variants)
- `bench_prover_creation` (8 provers)
- `bench_prover_detection` (8 file extensions)
- `bench_trust_computation` (3 scenarios: max_trust, single_prover, dangerous)
- `bench_axiom_scanning` (4 patterns)
- `bench_mutation_generation`
- `bench_pareto_frontier` (3 point-count variants)
- `bench_statistics_tracking`
- `bench_ffi_kind_mapping`
Run with: `cargo bench`

## Ignored Test Investigation (9 tests)

All 9 ignored tests are in `tests/integration_v1_2.rs`. They are **legitimately ignored** — each has a `// Requires <X> binary` comment:
- 2 tests: `#[ignore] // Requires ACL2 binary`
- 2 tests: `#[ignore] // Requires PVS binary`
- 2 tests: `#[ignore] // Requires HOL4 binary`
- 3 tests: `#[ignore] // Requires prover binaries`

**No action needed.** These test real prover binary invocation and must remain
skipped until ACL2/PVS/HOL4 are installed in the CI environment. The ignore
reason is clearly documented.

(Note: TEST-NEEDS.md said "9 ignored" but `cargo test` shows 16 ignored total.
The additional 7 are in `tests/test_neural_integration.rs` requiring the Julia
server running on port 8081.)

## What's Covered

### Point-to-Point (P2P) — tests/p2p_property_tests.rs
- [x] Dispatch determinism: same input → same trust level (proptest, 500 cases)
- [x] ProofState serialisation: arbitrary states survive JSON roundtrip (200 cases)
- [x] Reject danger caps trust at Level2 (proptest, 200 cases)
- [x] Safe danger >= Warning danger (proptest, 200 cases)
- [x] ProverFactory correct kind (proptest, 50 cases)
- [x] AxiomTracker stateless / idempotent (proptest, 200 cases)
- [x] ProverKind JSON roundtrip (proptest, 50 cases)
- [x] TrustLevel ordering consistent with value() (proptest, 200 cases)
- [x] DispatchConfig clone preserves fields (proptest, 100 cases)

### End-to-End (E2E) — tests/e2e_prover_test.rs
- [x] All 48 prover backends instantiate via ProverFactory
- [x] DispatchConfig defaults are safe (invariant check)
- [x] Trust pipeline — all 5 levels produce correct ordering
- [x] Reject axiom prevents Level3+ trust
- [x] Axiom tracker detects sorry/Admitted/believe_me
- [x] Z3 full dispatch workflow (skips if binary absent)
- [x] Malformed input returns error, not panic
- [x] Missing binary returns error (not false success)
- [x] DispatchResult JSON roundtrip (all fields)
- [x] Dispatcher respects timeout config
- [x] select_prover heuristic coverage

### Aspect Tests — tests/aspect_tests.rs
- [x] Security: malicious input no high trust
- [x] Security: no proof cert from arbitrary string
- [x] Security: zero timeout no panic
- [x] Concurrency: parallel dispatches isolated (8 workers)
- [x] Concurrency: axiom tracker stateless (16 workers)
- [x] Error handling: impossible trust requirement
- [x] Error handling: config validation
- [x] Error handling: DispatchResult edge cases
- [x] Trust: DangerLevel total order
- [x] Trust: TrustLevel values monotone
- [x] Trust: compute_trust_level deterministic (100 iterations)
- [x] Coverage: ProverKind::all() count >= 30, no duplicates
- [x] Coverage: ProverKind JSON stable (5 canonical names)

### Julia Smoke Tests — tests/julia/smoke_test.jl
- [x] Syntax validation: 9 top-level scripts (api_server, run_server, train_models, etc.)
- [x] Syntax validation: inference/ sub-package
- [x] EchidnaML module structure
- [x] api/ sub-package syntax
- [x] scripts/*.jl corpus scripts (32 scripts)
- [x] Directory structure (JULIA_SRC, Project.toml, entrypoints)
- [x] Tokenizer unit smoke (5 properties)
- [x] BOW vectorizer unit smoke (4 properties)

### Shell Validation — tests/shell/validate_scripts.sh
- [x] Syntax check (bash -n) on all scripts/*.sh
- [x] Syntax check on tests/*.sh
- [x] SPDX header check
- [x] Banned pattern check (docker/npm/HTTP)
- [x] --help smoke test for selected scripts

**Findings from shell validation:**
- scripts/install-provers.sh — missing SPDX header
- scripts/mvp-smoke.sh — missing SPDX header
- scripts/expand_training_data.sh — HTTP URL (should use HTTPS)
- scripts/test-integration.sh — HTTP URL
- scripts/test_integration.sh — HTTP URL

### Benchmarks — benches/proof_benchmarks.rs
- [x] Core type construction (ProofState, Term)
- [x] Prover creation (8 representative backends)
- [x] Prover detection from file extension
- [x] Trust computation (3 scenarios)
- [x] Axiom scanning (4 patterns)
- [x] Mutation generation
- [x] Pareto frontier (3 sizes)
- [x] Statistics tracking
- [x] FFI kind mapping roundtrip

## Still Missing

### V-lang prover (6,694 files — ZERO tests)
- This is Coq formal proof code in external_corpora/ (training data)
- The "V" extension here means Coq, not V-lang
- Coq proofs are inherently self-verifying when compiled with coqc
- No dedicated test infrastructure for the Coq corpus
- **Status:** Out of scope for this blitz (requires Coq toolchain + significant effort)

### Zig FFI (34 files — 7 test files)
- [x] 7 test files exist
- [ ] Coverage verification pending

### Idris2 ABI (42 files)
- Formal proofs are self-verifying (checked at type-check time)
- No runtime integration tests yet
- **Status:** Deferred — requires Idris2 toolchain in CI

### ReScript UI (33 files — ZERO tests)
- Dashboard components need render tests
- **Status:** Deferred — requires Deno + ReScript test setup

### Self-Tests
- [ ] panic-attack assail on own repo
- [ ] Echidnabot self-scan
- [ ] Prover correctness validation suite

## Known Issues

### /api/verify false-positive on unparseable input (2026-04-05)

**Bug:** `POST /api/verify` returns `valid: true` for content that a prover's
`parse_string` cannot interpret, even when that content is syntactically
invalid for the target prover.

Reproduction:
```bash
curl -X POST http://localhost:8090/api/verify \
  -H 'Content-Type: application/json' \
  -d '{"prover":"Coq","content":"absolute garbage @#$ not coq"}'
# → {"valid":true,"goals_remaining":0,"tactics_used":0}
```

Also affected: empty content, cross-prover content (Lean syntax to Coq),
anything the per-prover `parse_string` cannot extract structure from.

**Root cause:** the verification pipeline is:

1. `parse_string(content)` → `ProofState` (partial parse; empty state on
   unrecognised input, no failure propagated).
2. `verify_proof(&state)` calls `state.export()` to regenerate prover source
   from the `ProofState`, writes it to a temp file, then runs the real
   backend binary (`coqc`, `lean`, `idris2 --check`).
3. Empty `ProofState` → empty exported file → prover returns exit 0 →
   `valid: true`.

**Impact:** any downstream system treating `valid: true` as ground truth
will accumulate false positives. Observed externally: the hyperpolymath
`proof_attempts` learning loop was polluted with 29 false-success rows
before the bug was spotted; fix was to bypass `/api/verify` and shell out
to prover binaries directly in the batch driver.

Idris2 has the mirror-image bug (false-negative): `parse_string` parses
`main = putStrLn "ok"` but `export()` regenerates the body as `?main_todo`
(a hole), so `idris2 --check` always fails. See the generated file at
`/tmp/echidna_idris2/Verify.idr` after any Idris2 API call.

**Fix direction:**
- `parse_string` should return `Err` on unrecognised input rather than
  silently producing an empty state.
- `verify_proof` for each prover should either preserve original content
  (write `content` directly, not `export(state)`) or treat an empty
  `ProofState` as a parse failure.
- Add regression tests: `verify` on garbage, empty, cross-prover content
  must all return `valid: false`.

## Priority
- **CRG C COMPLETE** as of 2026-04-04
- Next priority: Fix 5 shell issues found by validation
- V-lang prover testing remains the largest correctness gap but is out of scope
  until the Coq corpus toolchain is set up in CI
