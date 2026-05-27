# Architecture

The canonical, current architecture overview lives in the repo at
[`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md).
This page is a short summary; consult the in-repo doc for the up-to-date
component map and the 11-step trust pipeline walkthrough.

## Component map (one paragraph)

ECHIDNA is a polyglot system. The **Rust core** (`src/rust/`, plus extracted
workspace crates in `crates/`) owns dispatch, the trust pipeline, and the 128
prover backend implementations. Four API surfaces (CLI, REPL, REST/GraphQL
on port 8000, gRPC on port 50051) hit `ProverDispatcher`, which picks a
backend, runs the verification under sandboxing (Podman / bubblewrap), and
walks the proof through the trust pipeline. A **Julia ML sidecar**
(`src/julia/`, port 8090) provides GNN-based premise ranking, tactic
suggestion, and accumulates per-(prover, domain) success-rate weights from
proof outcomes. **VeriSimDB** (cross-repo) persists `proof_attempts` rows
and serves `mv_prover_success_by_class` for history-guided routing.
**Idris2** (`src/abi/`) carries the FFI ABI proofs (zero `believe_me`).
**Agda** (`meta-checker/`) carries trust-pipeline meta-proofs. **AffineScript**
(in migration from ReScript at `src/rescript/`) carries the UI, served by
Deno.

## Trust pipeline (11 steps)

1. Integrity (SHAKE3-512 + BLAKE3 of solver binaries against `config/solver-manifest.toml`)
2. Dispatch (select backend; optionally history-guided via `VeriSimAdvisor`)
3. Sandbox (Podman / bubblewrap)
4. Portfolio cross-check (SMT: two independent solvers must agree)
5. Certificate verification (replay Alethe / DRAT-LRAT / TSTP independently)
6. Axiom tracking (Safe / Noted / Warning / Reject)
7. Confidence scoring (5-tier Bayesian)
8. Mutation testing (specifications)
9. Pareto frontier (speed × trust × certificate-availability)
10. Statistics update (per-(prover, domain) success rate)
11. Outcome emission to VeriSimDB (closes the learning loop)

## ProverBackend trait

```rust
#[async_trait]
trait ProverBackend: Send + Sync {
    fn kind(&self) -> ProverKind;
    async fn version(&self) -> Result<String>;
    async fn parse_string(&self, content: &str) -> Result<ProofState>;
    async fn apply_tactic(&self, state: &ProofState, t: &Tactic) -> Result<TacticResult>;
    async fn verify_proof(&self, state: &ProofState) -> Result<bool>;
    async fn check(&self, state: &ProofState) -> Result<ProverOutcome>; // rich variant
    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>>;
    async fn export(&self, state: &ProofState) -> Result<String>;
}
```

See [`src/rust/provers/mod.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/mod.rs).

## Polyglot source layout

| Path | Language | Role |
|---|---|---|
| `src/rust/` + `crates/` | Rust | Core, dispatch, trust, backends, servers |
| `src/julia/` | Julia | ML sidecar, GNN, training, eval |
| `src/abi/` | Idris 2 | Formal FFI ABI proofs |
| `meta-checker/` | Agda | Trust-pipeline meta-proofs |
| `src/chapel/` + `src/zig_ffi/` | Chapel + Zig | Parallel proof search (L2.1 live) |
| `src/ada/` + `spark/` | Ada/SPARK | Formal companion library |
| `src/rescript/` → AffineScript | ReScript→AffineScript | UI (migration in progress) |

Pointers and history evolve; the in-repo [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md) is authoritative.
