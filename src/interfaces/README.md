# ECHIDNA Interfaces

This directory contains all interface implementations for ECHIDNA theorem proving platform.

## Available Interfaces

### GraphQL (`graphql/`)
- **Framework:** Rust + async-graphql + axum
- **Port:** 8080
- **Playground:** http://localhost:8080/
- **Features:**
  - Type-safe schema with all 17 provers
  - Queries: provers, proof_state, list_proofs, suggest_tactics
  - Mutations: submit_proof, apply_tactic, cancel_proof
  - Subscriptions: proof_updates (planned)

### gRPC (`grpc/`)
- **Framework:** Rust + tonic + Protocol Buffers
- **Port:** 50051
- **Proto:** `grpc/proto/echidna.proto`
- **Features:**
  - High-performance binary protocol
  - Bidirectional streaming for long-running proofs
  - RPCs: SubmitProof, GetProofStatus, StreamProof, ApplyTactic, CancelProof
  - Neural premise selection via SuggestTactics

### REST (`rest/`)
- **Framework:** Rust + axum + utoipa (OpenAPI)
- **Port:** 8000
- **Swagger UI:** http://localhost:8000/swagger-ui
- **Features:**
  - RESTful JSON API
  - OpenAPI 3.0 specification with Swagger UI
  - Standard HTTP verbs (GET, POST, DELETE)
  - Endpoints: `/api/v1/provers`, `/api/v1/proofs`, `/api/v1/proofs/:id/tactics`

## Running Interfaces

Each interface can be run independently:

```bash
# GraphQL
cd src/interfaces/graphql && cargo run

# gRPC
cd src/interfaces/grpc && cargo run

# REST
cd src/interfaces/rest && cargo run
```

## Integration with ECHIDNA Core

All interfaces communicate with the ECHIDNA core via:
- **Option 1:** FFI (Foreign Function Interface) - direct Rust calls
- **Option 2:** IPC (Inter-Process Communication) - message passing
- **Option 3:** Shared library - dynamic linking

**TODO:** Implement core integration layer

## Architecture

```
ECHIDNA Core (Rust)
├── Prover Backends (17 provers)
├── ML Layer (Julia)
└── Parallel Layer (Chapel)
    ↓
Interface Layer
├── GraphQL Server → Port 8080
├── gRPC Server → Port 50051
└── REST Server → Port 8000
    ↓
Clients
├── echidnabot
├── Web UI
├── CLI tools
└── External integrations
```

## Development

Each interface is a separate Cargo package within the workspace:

```toml
[workspace]
members = [
    "src/interfaces/graphql",
    "src/interfaces/grpc",
    "src/interfaces/rest",
]
```

Build all interfaces:
```bash
cargo build --workspace
```

Test all interfaces:
```bash
cargo test --workspace
```
