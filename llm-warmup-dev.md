<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- LLM warmup context — DEVELOPER level (<400 lines) -->
<!-- Feed this to an LLM before doing development work on ECHIDNA -->

# ECHIDNA — Developer Context

## Architecture

ECHIDNA is a Rust workspace with Julia ML, Idris2 ABI, Zig FFI, and ReScript UI.

### Rust Core (src/rust/)

The main binary and library. Key modules:

| File/Dir | Purpose |
|----------|---------|
| `main.rs` | CLI entry (clap) |
| `lib.rs` | Library root — re-exports all modules |
| `core.rs` | Core types: `Term`, `ProofState`, `Tactic`, `Goal`, `Context`, `Theorem` |
| `repl.rs` | Interactive REPL |
| `server.rs` | HTTP API server |
| `dispatch.rs` | Full trust-hardening dispatch pipeline |
| `neural.rs` | Neural premise selection |
| `aspect.rs` | Aspect tagging |
| `provers/` | 30 prover backend implementations |
| `provers/mod.rs` | `ProverBackend` trait, `ProverKind` enum (48 variants), `ProverFactory` |
| `verification/` | Trust pipeline modules |
| `integrity/` | Solver binary integrity (SHAKE3-512, BLAKE3) |
| `executor/` | Sandboxed execution (Podman, bubblewrap) |
| `exchange/` | Cross-prover proof exchange (OpenTheory, Dedukti) |
| `agent/` | Agentic proof search (actor model) |
| `parsers/` | Proof file parsers |
| `ffi/` | Foreign function interface |

### Verification Pipeline (src/rust/verification/)

| Module | Purpose |
|--------|---------|
| `portfolio.rs` | SMT portfolio solving / cross-checking |
| `certificates.rs` | Proof certificate checking (Alethe, DRAT/LRAT, TSTP) |
| `axiom_tracker.rs` | Axiom usage tracking (Safe, Noted, Warning, Reject) |
| `confidence.rs` | 5-level trust hierarchy, Bayesian scoring |
| `mutation.rs` | Mutation testing for specifications |
| `pareto.rs` | Pareto frontier for multi-objective proof search |
| `statistics.rs` | Statistical confidence + Bayesian timeout estimation |

### API Interfaces (src/interfaces/)

Three workspace members under `src/interfaces/`:

| Dir | Tech | Port | Notes |
|-----|------|------|-------|
| `graphql/` | async-graphql | 8080 | Query/Mutation/Subscription |
| `grpc/` | tonic | 50051 | 4 services |
| `rest/` | axum + utoipa | 8000 | OpenAPI spec |

**Invariant**: Interfaces stay under `src/interfaces/` — never extract to separate repos.

### Julia ML Layer (src/julia/)

Logistic regression for tactic prediction. Runs on port 8090.
Future: Flux.jl Transformer models.

### Idris2 ABI (src/abi/)

7 modules with dependent type proofs. Zero `believe_me`.

| File | Purpose |
|------|---------|
| `Types.idr` | Core types with proofs |
| `GraphQL.idr` | Query/Mutation/Subscription operations |
| `GRPC.idr` | gRPC service definitions |
| `REST.idr` | REST endpoint definitions (18 endpoints, 6 groups) |
| `FFI.idr` | GADT constructors for C ABI functions |
| `echidnaabi.ipkg` | Package definition |

### Zig FFI (ffi/zig/)

4 shared libraries. Bridges Idris2 ABI to C ABI.

### ReScript UI (src/rescript/)

28 files. Deno runtime.

### Chapel PoC (chapel_poc/)

Optional parallel proof dispatch. Requires Chapel compiler.

## ProverBackend Trait

The core abstraction in `src/rust/provers/mod.rs`:

```rust
pub trait ProverBackend: Send + Sync {
    fn name(&self) -> &str;
    fn kind(&self) -> ProverKind;
    fn prove(&self, goal: &Goal, timeout: Duration) -> ProofResult;
    fn check_certificate(&self, cert: &Certificate) -> CertificateResult;
    fn supports_exchange(&self) -> bool;
}
```

48 variants in `ProverKind` enum. `ProverFactory` creates instances.

## Dispatch Pipeline (dispatch.rs)

Full trust-hardening flow:
1. Select candidate provers (aspect tags + neural ranking)
2. Verify solver binary integrity (SHAKE3-512 + BLAKE3)
3. Execute in sandbox (Podman/bubblewrap/none)
4. Portfolio cross-check (multiple solvers on same goal)
5. Verify proof certificates
6. Track axiom usage
7. Score confidence (Bayesian, 5-level hierarchy)
8. Optional: mutation testing, Pareto frontier

## Build Commands

```bash
just build              # Debug build
just build-release      # Release build
just test               # Unit tests (232)
just test-all           # All tests (389)
just test-integration   # Integration tests (38)
just test-neural        # Julia ML tests
just lint               # Clippy
just fmt                # Rustfmt
just pre-commit         # fmt-check + lint + test
just container-build    # Minimal container
just container-build-full # Full container
just build-chapel-ffi   # Zig FFI for Chapel
just build-chapel-poc   # Chapel PoC binary
just chapel-all         # Full Chapel stack
just doctor             # Check prerequisites
just heal               # Install instructions
```

## Adding a New Prover Backend

1. Add variant to `ProverKind` enum in `src/rust/provers/mod.rs`
2. Implement `ProverBackend` trait in `src/rust/provers/<name>.rs`
3. Register in `ProverFactory`
4. Add tests (unit + integration)
5. Update Julia layer (`src/julia/`) with prover metadata
6. Update Chapel layer (`chapel_poc/`) if parallel dispatch applies
7. Run `just test-all`

## Workspace Members

```toml
[workspace]
members = [".", "src/interfaces/graphql", "src/interfaces/grpc", "src/interfaces/rest"]
```

## Key Dependencies

- `tokio` — Async runtime
- `clap` — CLI parsing
- `serde`/`serde_json`/`toml` — Serialization
- `anyhow`/`thiserror` — Error handling
- `async-graphql` — GraphQL
- `tonic`/`prost` — gRPC
- `axum`/`utoipa` — REST + OpenAPI
- `sha3`/`blake3` — Integrity hashing

## Machine-Readable Metadata

All in `.machine_readable/`:
- `6a2/STATE.a2ml` — Current state
- `6a2/META.a2ml` — Architecture decisions
- `6a2/ECOSYSTEM.a2ml` — Ecosystem position
- `6a2/AGENTIC.a2ml`, `NEUROSYM.a2ml`, `PLAYBOOK.a2ml`

**NEVER** create these in the root directory.

## Packaging

- `guix.scm` — Guix package definition (uses cargo-build-system)
- `flake.nix` — Nix flake (with rust-overlay)
- `Containerfile` — Podman container

## Test Structure

- 232 unit tests (`cargo test --lib`)
- 38 integration tests (`cargo test --test integration_tests`)
- 119 additional tests (doc tests, property tests)
- Total: 389

## Banned Patterns

- No Python anywhere (use Julia for ML)
- No Docker (use Podman)
- No TypeScript (use ReScript)
- No `believe_me`/`assert_total` in Idris2
- PMPL-1.0-or-later license throughout

## CI/CD

17 workflows in `.github/workflows/`:
- `hypatia-scan.yml`, `codeql.yml`, `scorecard.yml`, `quality.yml`
- `mirror.yml`, `instant-sync.yml`
- All actions SHA-pinned

## License

PMPL-1.0-or-later.
Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
Git author: 6759885+hyperpolymath@users.noreply.github.com
