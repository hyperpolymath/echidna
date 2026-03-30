# Test & Benchmark Requirements

## Current State
- Unit tests: 684 pass / 0 fail / 16 ignored (556 in main crate + 128 across other crates)
- Integration tests: partial (echidnabot has integration tests)
- E2E tests: NONE
- Benchmarks: 1,035 benchmark files (likely V-lang prover benchmarks)
- panic-attack scan: NEVER RUN

## What's Missing
### Point-to-Point (P2P)
**Source counts:** 146 Rust + 6,694 V + 34 Zig + 42 Idris2 + 33 ReScript + 52 Julia + 39 JS + 226 Shell

#### Rust crate (146 files, ~684 tests — BEST tested component):
- 79 files with #[test] in main crate — good inline test coverage
- 3 files with #[test] in echidnabot — minimal
- fuzz/ crate exists (Cargo.toml) — verify fuzzing actually runs
- 9 ignored tests need investigation

#### V-lang prover (6,694 files — ZERO tests):
- This is the bulk of the codebase
- Prover correctness is critical — needs property-based testing
- All proof dispatch, verification, and formal reasoning untested

#### Zig FFI (34 files — 7 test files):
- Reasonable ratio but verify coverage

#### Idris2 ABI (42 files — ZERO tests):
- Formal verification definitions should be self-verifying
- But runtime behavior still needs integration testing

#### Julia (52 files — ZERO tests):
- Likely analysis/reporting scripts — need at least smoke tests

#### ReScript (33 files — ZERO tests):
- Dashboard/UI components — need render and interaction tests

#### Shell (226 files — ZERO tests):
- Scripts need at least --help and dry-run validation

### End-to-End (E2E)
- Full prover workflow: input problem -> preprocess -> prove -> verify result
- Echidnabot: receive repo event -> analyze -> report findings
- Dashboard: load data -> display results -> filter/search
- Proof dispatch: select prover backend -> route -> collect results
- VeriSimDB integration: write proof results -> query -> aggregate
- Dodeca-API interaction
- Report generation pipeline

### Aspect Tests
- [ ] Security (proof validation bypass, malicious input to prover, echidnabot webhook injection)
- [ ] Performance (prover on large problems, proof verification latency)
- [ ] Concurrency (parallel proof attempts, concurrent echidnabot webhook processing)
- [ ] Error handling (unsolvable problems, prover timeout, malformed input)
- [ ] Accessibility (dashboard UI)

### Build & Execution
- [x] cargo build — compiles
- [x] cargo test — 684 pass, 0 fail, 16 ignored
- [ ] V build — not verified
- [ ] Zig build — not verified
- [ ] echidnabot binary — not verified
- [ ] Self-diagnostic — none

### Benchmarks Needed
- Prover throughput on standard benchmark suites
- Proof verification latency
- VeriSimDB write/query performance
- Echidnabot analysis speed per repo
- Verify 1,035 existing benchmark files actually run (V-lang prover benchmarks?)

### Self-Tests
- [ ] panic-attack assail on own repo
- [ ] Echidnabot self-scan
- [ ] Prover correctness validation suite

## Priority
- **HIGH** — The Rust crate is well-tested (684 tests) but the V-lang prover (6,694 files) has ZERO tests. This is a formal verification tool where prover correctness is the entire value proposition. The 1,035 benchmark files need verification — if they are actually prover benchmarks, the situation is better than it appears for performance testing. But correctness testing for the prover logic is non-negotiable and completely absent.
