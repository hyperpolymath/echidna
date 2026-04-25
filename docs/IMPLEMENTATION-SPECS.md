# Implementation Specifications: Container Isolation + GNN Training

## SPEC 1: Container Isolation (🔴 CRITICAL - Stage 1 Blocker)

### Problem
All 105 prover implementations directly invoke solver binaries via `Command::new(self.binary())` without sandbox wrapping. This allows arbitrary code execution on the host system. **Required for production Stage 1 release.**

### Current State
- ✅ `src/rust/executor/sandbox.rs` — SandboxedExecutor fully implemented (lines 84-200+)
  - Supports Podman (preferred), Bubblewrap (fallback), None (dev)
  - Includes resource limits: memory, CPU, time, disk
  - Auto-detection of available sandboxing tools
- ❌ **NOT WIRED**: Sandbox not called from any prover backend

### Gap Analysis
**File: src/rust/provers/*.rs** (all 105 implementations)

Vulnerable pattern (current):
```rust
// athena.rs:91, cameleer.rs:111, kissat.rs:368, etc. (105 occurrences)
let mut cmd = Command::new(self.binary());
cmd.arg("--version").output().await
```

Safe pattern (required):
```rust
let config = SandboxConfig { kind: SandboxKind::Podman, ..Default::default() };
let executor = SandboxedExecutor::new(config);
let output = executor.run_command(
    Command::new(self.binary()),
    &goal_input,
    ...
)?;
```

### Implementation Steps

1. **Update ProverBackend trait** (`src/rust/provers/mod.rs`)
   - Add `sandbox_config: SandboxConfig` parameter to trait methods
   - Modify `fn solve(&self, goal: Goal) -> Result<Proof>` signature

2. **Create SandboxExecutor wrapper** (`src/rust/executor/wrapper.rs` — NEW)
   - Method: `async fn run_sandboxed_command(config: SandboxConfig, cmd: Command, stdin: &str) -> Result<SandboxedOutput>`
   - Delegates to `SandboxedExecutor::new(config).execute(cmd, stdin)`
   - **Critical**: Preserve stderr for debugging; enforce resource limits strictly

3. **Migrate all 105 prover backends**
   - Pattern: Replace all `Command::new()...spawn()` with `run_sandboxed_command(config, cmd, input)`
   - **Files to modify**: `src/rust/provers/{athena,cameleer,kissat,matita,...,vcl_ut}.rs`
   - One commit per prover family (e.g., "feat(sandbox): wrap SMT solvers (Z3, CVC5, Alt-Ergo)") to keep history clean
   - Integration test: each prover must still produce correct proofs post-wrapping

4. **Update dispatch.rs** (`src/rust/dispatch.rs`)
   - Pass `SandboxConfig` from AGENTIC.a2ml entropy/risk level → sandbox mode selection
     - Low risk: Podman (full isolation)
     - Medium/High: Bubblewrap (lightweight)
     - Critical (never): Podman with stricter limits
   - Audit: log sandbox choice + resource usage per proof

5. **Tests**
   - Unit: Each prover's sandbox wrapper produces same output as unsandboxed (regression test)
   - Integration: Run e2e_proof_pipeline.rs with Podman sandbox enabled
   - Security: Attempt file/network access from proof; verify isolation blocks it

### Success Criteria
- ✅ All 105 provers wrapped in SandboxedExecutor
- ✅ Default sandbox mode is Podman (not None)
- ✅ 638+ existing tests pass with sandbox enabled
- ✅ New security integration test passes (isolation enforcement)
- ✅ Panic-attack + clippy warnings clear
- ✅ Audit log shows sandbox mode + resource usage per proof

### Files Modified
- `src/rust/provers/mod.rs` — trait update
- `src/rust/executor/wrapper.rs` — new wrapper
- `src/rust/provers/*.rs` — 105 implementations (batched commits)
- `src/rust/dispatch.rs` — sandbox config routing
- `tests/e2e_security_isolation.rs` — new security test

### Timeline
- High complexity but highly parallelizable (105 provers can be migrated in batches)
- Estimate: 2-3 weeks for thorough migration + testing
- **Critical path**: Trait update (1 day) → 3 prover families as POC (2 days) → roll out rest (5-7 days) → testing (3-5 days)

---

## SPEC 2: GNN Model Training & Integration (🟡 HIGH - Stage 3 Quality Blocker)

### Problem
GNN scaffolds exist (`src/julia/`, `src/rust/gnn/`) but model was never trained on corpus. Currently using cosine-similarity fallback (works, but suboptimal). **Blocks Stage 3 quality gate.**

### Current State

**Corpus ready**: `training_data/` — 553 MB, 66,674 proofs, 179,933 tactics across 16 prover systems
- `proof_states_UNIFIED_BALANCED.jsonl` (161,989 lines)
- `premises_COMPLETE.jsonl` (4,789,221 lines)

**Scaffolds exist but untouched**:
- `src/julia/Project.toml` — Flux.jl, StatsBase.jl, MLUtils.jl declared
- `src/julia/training/train.jl` — training loop (~1.4k LoC) but never invoked
- `models/neural_solver.jl` — logistic regression (never trained)
- `src/julia/api/gnn_endpoint.jl:40-114` — falls back to cosine similarity if model missing
- `models/premise_vocab.txt` (1.31M tokens), `models/tactic_vocab.txt` (120k tokens)

**Idris2 formal proofs** (ready for integration):
- `src/abi/GnnProperties.idr` — 7 GNN properties proven (0 believe_me)
- Requires: `MRR ≥ 0.66`, `nDCG ≥ 0.60` for claim-type="verified"

### Gap Analysis

**Why training never ran:**
1. No documented protocol for data → model pipeline
2. Unclear performance requirements (MRR/nDCG targets)
3. No integration between Julia training output + Rust GNN inference
4. Risk of overfitting (163k train set for 16 prover systems = ~10k examples per system)

**Why fallback works but is suboptimal:**
- Cosine similarity in premise space: O(n) for every query
- No learned ranking: premise order = random TF-IDF scores
- GNN could rank by proof-relevance semantics (same axioms, similar lemmas)

### Implementation Steps

1. **Data preparation** (`data_pipeline.jl` — NEW)
   - Load `proof_states_UNIFIED_BALANCED.jsonl` + `premises_COMPLETE.jsonl`
   - Normalize: split 80/10/10 (train/val/test) **stratified by prover system** (not random)
   - Encode: terms → token IDs using `premise_vocab.txt`
   - Output: three Julia DataFrames (train_df, val_df, test_df) serialized to JLD2

2. **Model architecture** (`models/gnn_model.jl` — NEW)
   - Graph neural network (7 node kinds, 8 edge kinds from proof graph)
   - Architecture: 3-layer message passing + global readout (32-dim embedding)
   - Flux.jl layers: GraphConv, BatchNorm, Dropout(0.2)
   - Loss: ranking loss (BPR or margin loss) on premise pairs
   - Why ranking loss: "is premise P₁ better than P₂ for this proof?" is the actual task

3. **Training loop** (`src/julia/training/train_gnn.jl` — REPLACE current stub)
   - Hyperparameters:
     - Learning rate: 1e-3 (Adam)
     - Batch size: 32 (premise batches)
     - Epochs: 100 (with early stopping on val nDCG)
     - Dropout: 0.2
   - Validation every 10 epochs: compute nDCG@10, MRR on val set
   - Early stopping: if val nDCG doesn't improve for 20 epochs, stop
   - Save best model (weights + architecture) to `models/gnn_trained_model.jld2`

4. **Evaluation protocol** (`eval_gnn.jl` — NEW)
   - Metrics on test set:
     - **nDCG@10**: ideal ranking coefficient (is ground-truth premise in top-10?)
     - **MRR**: mean reciprocal rank (1/position of first-correct)
     - **Recall@5**: % of proofs where ground-truth premise appears in top-5
   - Report: nDCG, MRR, Recall@5 per prover system (16 rows)
   - **Gate**: MRR ≥ 0.66, nDCG ≥ 0.60 for "verified" claim-type; else fallback to cosine

5. **Integration** (`src/rust/gnn/model.rs` — modify)
   - Load trained model from `models/gnn_trained_model.jld2` at startup
   - Route request to Julia RPC endpoint (`api/gnn_endpoint.jl`)
   - Julia endpoint:
     ```rust
     POST /gnn/rank
     Input: { goal_id, premise_ids: [p1, p2, ...] }
     Output: { ranked_ids: [p_i, p_j, ...], scores: [0.92, 0.87, ...] }
     ```
   - **Fallback**: if model missing/loading fails, use cosine similarity (no error)

6. **Formal verification** (`src/abi/GnnIntegration.idr` — NEW)
   - Proof: If model achieves nDCG ≥ 0.60, then claim-type can be "verified" for GNN-guided proofs
   - Proof sketch: Lemma showing ranking guarantee (top-10 recall ≥ 0.6)
   - Reference existing properties in `src/abi/GnnProperties.idr`
   - Status: Use Parameter axiom (M11 pattern) for training convergence proof (external fact)

7. **Tests**
   - Unit: Load trained model, rank premise set, check output shape
   - Integration: Submit proof with GNN-guided search; verify correct premise ranked high
   - Regression: All 638+ existing tests pass with new GNN model
   - Performance: Query latency < 100ms per premise set (benchmark w/ Criterion)

### Success Criteria
- ✅ Training completes on corpus (66k proofs, 4.7M premises)
- ✅ Model achieves MRR ≥ 0.66, nDCG ≥ 0.60 on test set
- ✅ Per-prover-system breakdown available (16 rows of metrics)
- ✅ Integrated into dispatch.rs as preferred ranking strategy
- ✅ Formal Idris2 proof of nDCG threshold guarantee
- ✅ Fallback to cosine similarity if model unavailable
- ✅ 638+ tests pass; no performance regressions

### Files Modified/Created
- `src/julia/training/data_pipeline.jl` — new
- `src/julia/training/train_gnn.jl` — new (replaces stub)
- `src/julia/training/eval_gnn.jl` — new
- `models/gnn_model.jl` — new
- `models/gnn_trained_model.jld2` — new (generated artifact)
- `src/rust/gnn/model.rs` — load trained weights
- `src/abi/GnnIntegration.idr` — new formal proof
- `tests/gnn_ranking.rs` — new integration test
- `benches/gnn_latency.rs` — new benchmark

### Timeline
- Data prep: 2-3 days (handle stragglers, outliers, normalization)
- Model training & eval: 5-7 days (iterate on architecture, hyperparams)
- Integration: 2-3 days (RPC endpoint, fallback, error handling)
- Formal proofs: 2-3 days (Idris2, reference existing lemmas)
- Testing & CI: 3-5 days
- **Total**: 2-3 weeks (can be parallelized: data prep in parallel with formal proofs)

### Known Risks
- **Overfitting**: 16 prover systems × 10k examples/system is tight; use cross-validation
- **Convergence**: GNN may not converge on ranking loss; have cosine fallback always ready
- **Reproducibility**: Flux.jl + CUDA random seeds must be pinned for reproducible weights
- **Maintenance**: Retrain if corpus grows significantly (> 100k proofs); document retraining protocol

---

## Handoff Checklist

Both specs are ready for Sonnet or Opus to execute:

- [ ] Container Isolation (Spec 1)
  - Estimated 2-3 weeks, parallelizable (105 provers)
  - Critical path: trait → 3 POC → rollout → test
  - **Blocker for Stage 1 production release**

- [ ] GNN Training (Spec 2)
  - Estimated 2-3 weeks, parallelizable (data/training/formal in parallel)
  - Rich integration: Julia ML + Rust dispatch + Idris2 proofs
  - **Blocker for Stage 3 quality gate**

### Recommended Execution Order
1. **Container Isolation first** (Stage 1 gate is critical)
2. **GNN in parallel** (no dependencies on isolation; independent workstream)
3. Merge both when ready; re-test full 638-test suite

### Success Definition
- Container: All 105 provers sandboxed, 638+ tests green, security test passing
- GNN: Model trained (MRR ≥ 0.66), integrated, formal proof verified, benchmarks < 100ms
