---
title: gRPC API Reference
date: 2026-02-09
template: default
---

# gRPC API Reference

Endpoint: `localhost:50051`

Proto file: `src/interfaces/grpc/proto/echidna.proto`

## Service Definition

```protobuf
service ProofService {
    rpc SubmitProof (SubmitProofRequest) returns (SubmitProofResponse);
    rpc GetProofStatus (GetProofStatusRequest) returns (GetProofStatusResponse);
    rpc StreamProof (StreamProofRequest) returns (stream ProofUpdate);
    rpc ApplyTactic (ApplyTacticRequest) returns (ApplyTacticResponse);
    rpc CancelProof (CancelProofRequest) returns (CancelProofResponse);
    rpc ListProvers (ListProversRequest) returns (ListProversResponse);
    rpc SuggestTactics (SuggestTacticsRequest) returns (SuggestTacticsResponse);
}
```

## RPC Methods

### SubmitProof

Submit a new proof for verification.

**Request:**
```protobuf
message SubmitProofRequest {
    string prover_kind = 1;
    string goal = 2;
    int64 timeout_ms = 3;
}
```

**Response:**
```protobuf
message SubmitProofResponse {
    string session_id = 1;
    ProofStatus status = 2;
    repeated string goals = 3;
}
```

### StreamProof

Stream proof progress updates in real time.

**Request:**
```protobuf
message StreamProofRequest {
    string prover_kind = 1;
    string goal = 2;
}
```

**Response (stream):**
```protobuf
message ProofUpdate {
    string step = 1;
    ProofStatus status = 2;
    repeated string remaining_goals = 3;
    float progress = 4;
}
```

### ApplyTactic

Apply a tactic to an active proof session.

### CancelProof

Cancel an active proof session.

### ListProvers

List all 30 available prover backends with tier and complexity.

### SuggestTactics

Get ML-suggested tactics for the current proof state.

## Connection

```bash
# Using grpcurl
grpcurl -plaintext localhost:50051 echidna.ProofService/ListProvers

# Submit a proof
grpcurl -plaintext -d '{
  "prover_kind": "coq",
  "goal": "forall n, n + 0 = n"
}' localhost:50051 echidna.ProofService/SubmitProof
```
