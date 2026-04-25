# Handoff to Sonnet 4.7: Container Isolation + GNN Training

**From**: Haiku (2026-04-25 session)  
**To**: Sonnet 4.7  
**Priority**: 🔴 CRITICAL (Stage 1 production blocker) + 🟡 HIGH (Stage 3 quality gate)

---

## What Haiku Just Completed

This session restructured echidna as a full tooling server and documented two major implementation gaps:

1. **Repo reorganization** (DONE)
   - Echidna moved to top-level (was in verification-ecosystem)
   - Echidnabot moved to gitbot-fleet (resolved dual-truth repo)
   - Echidna-llm-mcp extracted to standalone repo (can be pushed once GitHub repo created)
   - Contractiles 6/6 complete (intend/bust/adjust added; all A2ML + .ncl runners)

2. **A2ML Conformance** (DONE)
   - `AGENTIC.a2ml`: full spec compliance (426 lines; gating, entropy, risk thresholds, overrides, audit)
   - `NEUROSYM.a2ml`: full spec compliance (342 lines; operations, composition, obligations, types)
   - `ROADMAP.a2ml`: 8-stage service roadmap (Stage 1–8 with blockers and timelines)

3. **Implementation Specs** (DONE — ready for you to execute)
   - `docs/IMPLEMENTATION-SPECS.md` — two detailed, execution-ready specs

---

## Two Critical Tasks (Ready for You)

### TASK 1: Container Isolation (🔴 CRITICAL)

**File**: `docs/IMPLEMENTATION-SPECS.md` § SPEC 1

**Problem**: All 105 prover implementations directly execute solver binaries without sandboxing.
```rust
// Current (UNSAFE):
let mut cmd = Command::new(self.binary());
cmd.arg("--version").output().await
```

**Gap**: Sandbox infrastructure exists (`src/rust/executor/sandbox.rs` — fully implemented) but isn't wired into any prover backend.

**Fix**: Wrap all 105 `Command::new()` calls with `SandboxedExecutor`.

**Why Critical**: Stage 1 production release is gated on this. Unsandboxed solver execution = arbitrary code execution risk.

**Effort**: 2–3 weeks (parallelizable by prover family)

**Files to Modify** (from spec):
- `src/rust/provers/mod.rs` — trait update (1 day)
- `src/rust/provers/*.rs` — 105 implementations (batched commits, ~5–7 days)
- `src/rust/executor/wrapper.rs` — new wrapper (1 day)
- `src/rust/dispatch.rs` — route sandbox config (2 days)
- `tests/e2e_security_isolation.rs` — new security test (2 days)

**Success**: All 105 provers sandboxed, 638+ tests green, security test passing.

---

### TASK 2: GNN Model Training (🟡 HIGH)

**File**: `docs/IMPLEMENTATION-SPECS.md` § SPEC 2

**Problem**: GNN training scaffolds exist (`src/julia/training/`, `models/`) but model was never trained on corpus. Currently using cosine-similarity fallback (works, but suboptimal).

**Gap**: 
- Corpus ready (553 MB, 66,674 proofs, 4.7M premises) but untouched
- Training code is stubs (~1.4k LoC)
- Model metadata shows "0 words, 0 classes" (never trained)

**Fix**: Run full training pipeline → achieve MRR ≥ 0.66 + nDCG ≥ 0.60 → integrate into dispatch.

**Why Important**: Stage 3 quality gate. GNN can improve premise ranking semantics; cosine is acceptable but suboptimal.

**Effort**: 2–3 weeks (can run in parallel with container isolation)

**Files to Modify/Create** (from spec):
- `src/julia/training/data_pipeline.jl` — new
- `src/julia/training/train_gnn.jl` — new (replaces stub)
- `src/julia/training/eval_gnn.jl` — new
- `models/gnn_model.jl` — new
- `src/rust/gnn/model.rs` — load trained weights
- `src/abi/GnnIntegration.idr` — new formal proof (Idris2)
- `tests/gnn_ranking.rs` — new integration test

**Success**: Model trained (MRR ≥ 0.66, nDCG ≥ 0.60), integrated, formal proof verified, benchmarks < 100ms.

---

## Execution Strategy

**Recommended order:**
1. **Container Isolation first** (Stage 1 gate is critical for production)
2. **GNN in parallel** (no dependencies; independent workstream)

**Why parallel:**
- Isolation touches 105 prover backends (file-level parallelization possible)
- GNN is self-contained (Julia training + Rust integration + Idris2 proof)
- Both can be merged simultaneously when ready

---

## Context: Where Echidna Stands

**What Works** (mature):
- ✅ 113 prover backends (105 active + 8 type-checker variants)
- ✅ 3.0 GB training corpus (66K proofs, 4.7M premises)
- ✅ 1.43M vocabulary (premise + tactic)
- ✅ REST/gRPC/GraphQL APIs (fully operational)
- ✅ Trust pipeline: portfolio solvers, certificate verification, axiom tracking, confidence scoring
- ✅ Zig FFI layer, Idris2 ABI proofs (zero believe_me)
- ✅ 638+ tests passing (528 unit + 38 integration + 21 property)
- ✅ A2ML conformance (AGENTIC, NEUROSYM fully spec-compliant as of this session)

**What's Missing** (your work):
- 🔴 Container isolation (105 provers unsandboxed)
- 🟡 GNN training (scaffolds only, never converged)

---

## Key Files for Reference

**Specs** (read these first):
- `docs/IMPLEMENTATION-SPECS.md` — your execution playbook
- `.machine_readable/6a2/AGENTIC.a2ml` — gating/entropy/audit config
- `.machine_readable/6a2/NEUROSYM.a2ml` — operation semantics
- `.machine_readable/ROADMAP.a2ml` — 8-stage service architecture

**Code to Understand**:
- `src/rust/executor/sandbox.rs` — SandboxedExecutor (fully implemented, just not wired)
- `src/rust/provers/mod.rs` — ProverBackend trait (where to add sandbox param)
- `src/rust/provers/athena.rs`, `cameleer.rs`, `kissat.rs` — example implementations (105 variations on same pattern)
- `src/julia/training/train.jl` — GNN training scaffold
- `models/premise_vocab.txt`, `tactic_vocab.txt` — ready to use

**Tests to Maintain**:
- `tests/e2e_proof_pipeline.rs` — must keep passing post-sandbox
- All 638+ tests in `Cargo.toml` test suite

---

## Critical Invariants

1. **All 105 provers must be wrapped** (not just SMT solvers; includes Lean, Coq, Agda, etc.)
2. **Default sandbox mode = Podman** (not None; None is dev-only with explicit opt-in)
3. **Sandbox config flows from AGENTIC.a2ml** (entropy level → sandbox strictness)
4. **GNN model achieved nDCG ≥ 0.60 before integration** (fallback to cosine if not met)
5. **Formal Idris2 proof required for GNN integration** (M11 Parameter axiom pattern acceptable for training convergence)

---

## Questions for Sonnet

1. **Parallelization strategy for 105 provers**: Batch by prover family (ATPs, SMTs, Interactive, etc.) or by similarity?
2. **GNN convergence risk**: If training doesn't converge to nDCG ≥ 0.60, roll back to cosine or investigate architecture?
3. **Formal proof scope**: Full proof of nDCG guarantee or just integration contract?

---

## Success Definition

**Container Isolation**: All 105 provers sandboxed, 638+ tests green, security integration test passing, no performance regression.

**GNN Training**: Model trained (MRR ≥ 0.66, nDCG ≥ 0.60), integrated into dispatch, formal proof verified, query latency < 100ms.

**Both together**: Stage 1 production-ready (container isolation) + Stage 3 quality baseline (GNN).

---

## Branch & Commits

All of Haiku's work is on `main`:
- Latest commits: AGENTIC/NEUROSYM/ROADMAP A2ML + implementation specs
- All reorganization work (echidnabot move, cartridge extract, contractiles) merged and pushed

You can start from `main` immediately. Create a feature branch for your work (e.g., `feat/container-isolation` and `feat/gnn-training` in parallel).

---

**Ready to start?** Read `docs/IMPLEMENTATION-SPECS.md` first. Both specs are detailed and execution-ready.
