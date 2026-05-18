# Echidna L1 — Cap'n Proto Protocol Swap — Continuation Prompt

**Context**: Echidna currently uses HTTP + JSON for Rust↔Julia (GNN inference) via
`src/rust/gnn/client.rs` → `src/julia/api_server.jl` port 8090. This violates the
`feedback_no_json_emit_a2ml` memory rule and blocks a clean polyglot IPC story. Swap to
**Cap'n Proto** (chosen over Bebop3 for dependability + maturity + zero-copy reads).

**Master plan**: `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
**Prerequisite**: L3 Tier-1 green for ≥7 days on main.
**Follows**: L2 (Chapel) consumes these schemas.

## Deliverables

### Schema
- `schemas/echidna.capnp` — canonical wire schemas:
  - `ProofGoal` — a theorem/claim to prove
  - `ProofResult` — success/failure + metadata
  - `TacticSuggestion` — ML-suggested tactic
  - `GnnRankRequest` / `GnnRankResponse` — replaces current HTTP+JSON
  - `ProverInvocation` — dispatch message to a backend (used later by Chapel in L2)
  - `TrustedOutcome` — post-trust-pipeline result
- `schemas/VERSIONING.md` — forward/backward compat rules

### Rust side (hot-path consumer)
- `src/rust/ipc/mod.rs` — Cap'n Proto transport module
- `src/rust/ipc/uds.rs` — Unix-domain socket transport (primary)
- `src/rust/ipc/tcp.rs` — TCP transport (fallback for containerised cases)
- Replace `src/rust/gnn/client.rs` HTTP calls with Cap'n Proto over UDS
- Keep `serde_json` out of hot path; retain only for config/log emission (Nickel for config proper)

### Julia side
- `src/julia/ipc.jl` — Cap'n Proto reader/writer
- **RATIFIED 2026-05-18: C-ABI shim through the existing Zig FFI layer** (NOT
  `CapnProto.jl`). Buffer-oriented ABI — Julia hands the Zig layer opaque
  Cap'n Proto frames; Zig owns parse/validate/gate. Rationale: estate-canonical
  (FFI=Zig everywhere; single wire codec shared with Rust; the Zig layer is the
  estate interface-safety transaction point). `CapnProto.jl` rejected: low
  maturity + a second independent codec = wire-drift engine. See open-question
  #2 resolution below.
- `src/julia/api_server.jl` — switch from HTTP to UDS listener

### Idris2 ABI proofs
- `src/abi/CapnSchemas.idr` — formal proofs that schema round-trip preserves meaning
- Zero `believe_me` (per estate rule); constructive proofs only
- Coordinate with `src/abi/Types.idr` / `src/abi/Foreign.idr`

### Zig FFI bridge
- `ffi/zig/capnp_bridge.zig` — C-ABI bridge for polyglot consumers (esp. Chapel in L2)

### AffineScript bindings (UI path)
- `bindings/affinescript/echidna_capnp.affine` — typed AffineScript bindings for the
  UI layer (compiled to typed-wasm). **ReScript is banned estate-wide** — this was
  formerly listed as `bindings/rescript/echidna_capnp.res`; the destination is
  AffineScript directly, not ReScript.
- Keep the existing 3 API interfaces (GraphQL/gRPC/REST) as external surfaces; Cap'n Proto is the
  **internal** wire format

### Tooling
- `just capnp-gen` — regenerates Rust/Julia/Idris2/Zig/AffineScript bindings from `.capnp` schemas
- CI check: `capnp compile` runs clean + generated code is committed

## Acceptance criteria

- Zero `serde_json::to_*` / `serde_json::from_*` calls on the Rust↔Julia hot path
- `src/rust/gnn/client.rs` uses UDS+Cap'n Proto
- Benchmarks: Cap'n Proto round-trip ≤ 50% of JSON latency for GNN rank request
- Idris2 ABI compiles with zero `believe_me`
- Round-trip property tests on all six schemas (Rust, Julia, Idris2)
- `schemas/VERSIONING.md` explains migration story

## Open design questions to settle early

1. **UDS path convention** — `/run/echidna/ipc.sock` vs `$XDG_RUNTIME_DIR/echidna/ipc.sock`?
2. **Authentication** — initial handshake signed with existing BLAKE3/SHAKE3-512 integrity keys?
3. **Streaming vs request-response** — Cap'n Proto RPC streams for GNN batch inference?
4. **Multi-locale Chapel** — schemas need to survive locale-to-locale transit; design for that now
   so L2 doesn't re-spec.

### Resolved decisions

- **Julia transport (was: "`CapnProto.jl` vs Zig C-ABI shim", TODO.md open Q#2)**
  — **RATIFIED 2026-05-18: Zig C-ABI shim, buffer-oriented.** Estate-canonical
  (FFI=Zig; one codec shared with Rust; Zig = the interface-safety transaction
  layer). `CapnProto.jl` rejected (low maturity + second wire codec). This is
  gate-permitted spec/design; L1 *implementation* still waits on the L3 hand-off.
- Q1/Q3/Q4 above remain open (recommended defaults, pending ratification): Q1 →
  `$XDG_RUNTIME_DIR/echidna/ipc.sock` with `/run/echidna/ipc.sock` fallback; Q2
  (auth) → yes, sign the handshake with the existing SHAKE3-512 integrity keys
  (aligns with estate interface-safety policy); Q3 → request-response first,
  streaming deferred until a measured GNN-batch need; Q4 → frames carry an
  explicit `schemaVersion`, locale-agnostic by construction (no host pointers
  on the wire — Cap'n Proto already guarantees this).

## Hand to L2 when

- Cap'n Proto is the default Rust↔Julia path
- `ProverInvocation` + `TrustedOutcome` schemas are stable (L2 Chapel will consume them)
- Zig FFI bridge passes round-trip test

---

## Rules active

- `no_json_emit_a2ml` — the whole reason this phase exists
- `feedback_verisimdb_policy` — all IPC traffic should be observable as VeriSimDB records
- `feedback_code_only_grep_for_banned_patterns` — when auditing for `serde_json` removal, use
  code-only grep (`^[^-|]*serde_json`) to avoid comment/doc noise
- `feedback_wire_everything` — no stubs; every schema has a live consumer on all sides

## Key files to read first

1. `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
2. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/rust/gnn/client.rs` (current JSON path)
3. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/julia/api_server.jl` (Julia server)
4. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/abi/*.idr` (existing Idris2 ABI)
5. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/src/zig_ffi/` (existing Zig FFI layer)
