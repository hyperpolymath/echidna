# ECHIDNA v2.0 Roadmap

## Vision

ECHIDNA v2.0 aims to be the **definitive neurosymbolic theorem proving platform** with:
- **Deep learning** for tactic prediction and premise selection
- **Protocol verification** for cryptographic protocols
- **True parallelism** via Chapel for portfolio solving
- **Seamless interop** with all prover backends via FFI/IPC

## Current State (v1.5.0)

✅ **Complete:**
- 30 prover backends (all tiers)
- Trust & safety pipeline (13 components)
- 3 API interfaces (GraphQL, gRPC, REST)
- Julia ML layer (logistic regression)
- ReScript UI (28 files)
- Gitbot-fleet integration
- 306+ tests passing

⚠️ **Gaps:**
- API interfaces use stub responses, don't call Rust backends
- ML models are simple (logistic regression only)
- Chapel integration exists but not activated
- No protocol verification support
- No FFI between Julia/Rust/ReScript

---

## v2.0 Features

### 1. FFI/IPC Bridge (Priority: CRITICAL)

**Goal**: Wire API interfaces to actually call Rust prover backends.

**Current State**:
- GraphQL server (port 8080) - stub responses
- gRPC server (port 50051) - stub responses
- REST server (port 8000) - stub responses
- Rust backends exist but not connected

**Tasks**:
- [ ] Design IPC protocol (Unix sockets vs TCP vs shared memory)
- [ ] Implement Rust IPC server wrapping ProverFactory
- [ ] Update GraphQL resolvers to call IPC server
- [ ] Update gRPC handlers to call IPC server
- [ ] Update REST handlers to call IPC server
- [ ] Add connection pooling and request queueing
- [ ] End-to-end integration tests
- [ ] Benchmark: target <50ms overhead per request

**Alternative Approach**: Embed Rust as shared library
- Compile Rust to .so/.dylib
- Call directly via FFI from TypeScript/Julia
- Lower latency but tighter coupling

**Timeline**: 4-6 weeks

---

### 2. Deep Learning Models (Priority: HIGH)

**Goal**: Replace logistic regression with Transformer models for tactic prediction.

**Current State**:
- Julia ML layer exists (src/julia/)
- Simple logistic regression for tactic scoring
- No premise selection

**Tasks**:
- [ ] Set up Flux.jl Transformer models
- [ ] Train on proof corpus (Coq stdlib, mathlib, AFP)
- [ ] Implement premise selection via semantic search
- [ ] Build proof context encoder (goals + hypotheses → embeddings)
- [ ] Integrate with prover backends (suggest tactics)
- [ ] Add feedback loop (success/failure → retraining)
- [ ] GPU acceleration via CUDA.jl
- [ ] Model versioning and A/B testing

**Data Requirements**:
- Coq standard library (~50K proofs)
- Lean mathlib (~100K proofs)
- Isabelle Archive of Formal Proofs (~500K proofs)
- Storage: ~500GB raw proof data

**Models**:
- **Tactic Predictor**: Input=goal state, Output=ranked tactics
- **Premise Selector**: Input=goal, Output=relevant lemmas
- **Proof Completer**: Input=partial proof, Output=continuation

**Timeline**: 8-12 weeks (includes training time)

---

### 3. Protocol Verification (Priority: MEDIUM)

**Goal**: Add Tamarin and ProVerif for cryptographic protocol analysis.

**Current State**:
- None - ECHIDNA focuses on pure mathematics/logic proofs

**Why Add Protocol Verification?**
- Complement formal verification with security protocols
- Analyze TLS, Signal Protocol, WireGuard, etc.
- Bridge symbolic + computational security

**Tasks**:
- [ ] Add Tamarin as Tier 4 prover (ProverKind::Tamarin)
- [ ] Add ProVerif as Tier 4 prover (ProverKind::ProVerif)
- [ ] Implement Tamarin file parsing (.spthy files)
- [ ] Implement ProVerif file parsing (.pv files)
- [ ] Add protocol-specific tactics (induction, case analysis)
- [ ] Integrate with trust pipeline (axiom tracking for crypto assumptions)
- [ ] Build protocol gallery (TLS 1.3, Signal, Noise)

**Use Cases**:
- Verify custom authentication protocols
- Check key exchange security properties
- Prove forward secrecy, authenticity
- CI/CD for protocol specifications

**Timeline**: 4-6 weeks

---

### 4. Chapel Parallel Proof Search (Priority: HIGH)

**Goal**: Activate Chapel backend for true portfolio parallelism.

**Current State**:
- Chapel FFI exists in src/rust/proof_search.rs
- 7 unsafe blocks, all documented
- Feature-gated: `#[cfg(feature = "chapel")]`
- **NOT activated** - compiles but chapel not in PATH

**Tasks**:
- [ ] Install Chapel runtime (version 2.0+)
- [ ] Build Chapel integration module (chapel/proof_parallel.chpl)
- [ ] Implement multi-prover dispatch in Chapel
- [ ] Add locale-aware scheduling (NUMA optimization)
- [ ] Benchmark: N provers in parallel, M-way speedup
- [ ] Compare vs sequential: portfolio solving effectiveness
- [ ] Document Chapel installation in INSTALL.md
- [ ] Add Chapel to CI/CD (if feasible)

**Expected Performance**:
- **Sequential**: Try provers one-by-one (worst case: sum of timeouts)
- **Chapel Parallel**: Try all provers simultaneously (best case: fastest prover)
- **Goal**: 5-10x speedup on typical proofs

**Challenges**:
- Chapel adds ~200MB dependency
- Not widely available in package managers
- May complicate deployment

**Timeline**: 2-3 weeks (if Chapel builds smoothly)

---

### 5. Advanced Trust Features (Priority: LOW)

**Goal**: Enhance trust pipeline with additional verification layers.

**Ideas**:
- [ ] Proof certificate cross-checking (Coq → Lean translation)
- [ ] Metamath verification of all proofs
- [ ] Formal verification of prover implementations (?)
- [ ] Byzantine fault tolerance (3+ provers must agree)
- [ ] Proof mining (extract computational content)
- [ ] Certified code extraction (Coq → OCaml/Haskell)

**Timeline**: Long-term research direction

---

### 6. User Experience Improvements (Priority: MEDIUM)

**Goal**: Make ECHIDNA easier to use and deploy.

**Tasks**:
- [ ] Interactive proof mode (REPL with live feedback)
- [ ] VSCode extension (proof state visualization)
- [ ] Web-based proof explorer (browse proof trees)
- [ ] One-click installers (AppImage, .deb, .rpm)
- [ ] Docker/Podman images with all provers pre-installed
- [ ] Improved error messages (explain why proof failed)
- [ ] Proof diff tool (compare proof attempts)
- [ ] Collaborative proving (multi-user proof sessions)

**Timeline**: Ongoing (6-12 months)

---

## Dependency Map

```
v2.0 Core Components:
┌─────────────────────────────────────┐
│  GraphQL/gRPC/REST APIs             │
│  (TypeScript/Rust)                  │
└──────────────┬──────────────────────┘
               │ FFI/IPC Bridge (NEW)
               ↓
┌─────────────────────────────────────┐
│  Rust Core (30+ Provers)            │
│  ├─ ProverFactory                   │
│  ├─ Trust Pipeline                  │
│  ├─ Chapel Parallel (NEW)           │
│  └─ Protocol Verifiers (NEW)        │
└──────────────┬──────────────────────┘
               │
               ↓
┌─────────────────────────────────────┐
│  Julia ML Layer (NEW: Transformers) │
│  ├─ Tactic Predictor                │
│  ├─ Premise Selector                │
│  └─ Proof Completer                 │
└─────────────────────────────────────┘
```

## Release Strategy

### v1.6.0 (Incremental - 1 month)
- FFI/IPC bridge completion
- Basic Transformer integration
- Documentation updates

### v1.7.0 (Incremental - 2 months)
- Chapel parallel activation
- Advanced Transformer models
- Protocol verification (Tamarin/ProVerif)

### v2.0.0 (Major - 3-4 months)
- All features complete
- Full test coverage
- Production-ready deployment
- Comprehensive benchmarks

## Success Metrics

**Performance**:
- ✅ Proof throughput: 100+ proofs/minute
- ✅ Latency: <1s for simple proofs, <60s for complex
- ✅ Parallel speedup: 5-10x with Chapel

**Accuracy**:
- ✅ Tactic prediction: >70% top-5 accuracy
- ✅ Premise selection: >80% recall@20
- ✅ Trust pipeline: Zero false positives on verified proofs

**Usability**:
- ✅ Installation: <30 minutes
- ✅ First proof: <5 minutes from install
- ✅ API response time: <100ms (excluding proof time)

**Ecosystem**:
- ✅ Integration with gitbot-fleet (v1.5.0 ✓)
- ✅ VeriSimDB ingestion
- ✅ Continuous Hypatia scans
- ✅ 5+ public repositories using ECHIDNA in CI

## Long-Term Vision (v3.0+)

- **Proof automation**: Full auto-proving for 50%+ of lemmas
- **Proof repair**: Automatically fix broken proofs after library updates
- **Cross-prover translation**: Coq ↔ Lean ↔ Isabelle
- **Educational mode**: Interactive tutorials for proof techniques
- **Distributed proving**: Cloud-scale proof search
- **Proof marketplace**: Share and monetize formal proofs

---

**Status**: v1.5.0 complete, v2.0 planning phase
**Next Steps**: FFI/IPC bridge + Transformer training
**Timeline**: v2.0 release target: Q2 2026
