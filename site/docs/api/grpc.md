---
title: gRPC Interface Reference
date: 2026-07-28
template: default
---

# gRPC Interface Reference

The `echidna-grpc` binary is an optional self-hosted service listening
on `localhost:50051`. The authoritative schema is
`src/interfaces/grpc/proto/echidna.proto`; everything below is taken
from it.

## Service definition

```protobuf
service ProofService {
    rpc SubmitProof (SubmitProofRequest) returns (ProofResponse);
    rpc GetProofStatus (GetProofStatusRequest) returns (ProofResponse);
    rpc StreamProof (StreamProofRequest) returns (stream ProofUpdate);
    rpc ApplyTactic (ApplyTacticRequest) returns (TacticResponse);
    rpc CancelProof (CancelProofRequest) returns (CancelProofResponse);
    rpc ListProvers (ListProversRequest) returns (ListProversResponse);
    rpc SuggestTactics (SuggestTacticsRequest) returns (SuggestTacticsResponse);
}
```

## Methods

### SubmitProof

Submit a goal for verification. `prover` is the `ProverKind` enum and
the timeout is expressed in seconds.

```protobuf
message SubmitProofRequest {
    string goal = 1;
    ProverKind prover = 2;
    optional uint32 timeout_seconds = 3;
}

message ProofResponse {
    string proof_id = 1;
    ProverKind prover = 2;
    string goal = 3;
    ProofStatus status = 4;
    repeated string proof_script = 5;
    optional double time_elapsed = 6;
    optional string error_message = 7;
}
```

`GetProofStatus` takes `{ proof_id }` and returns the same
`ProofResponse`.

### StreamProof

Streams progress for a proof that has already been submitted, so the
request is just its identifier:

```protobuf
message StreamProofRequest {
    string proof_id = 1;
}

message ProofUpdate {
    string proof_id = 1;
    ProofStatus status = 2;
    string message = 3;
    optional double progress = 4;
}
```

### ApplyTactic

Note the field names: `tactic_name` and a repeated `tactic_args`.

```protobuf
message ApplyTacticRequest {
    string proof_id = 1;
    string tactic_name = 2;
    repeated string tactic_args = 3;
}

message TacticResponse {
    bool success = 1;
    ProofResponse proof_state = 2;
}
```

### CancelProof

Takes `{ proof_id }`, returns `{ success }`.

### ListProvers

Takes an empty request and returns `ProverInfo` entries carrying kind,
version, tier, complexity, and availability.

### SuggestTactics

Keyed by proof, not by goal text:

```protobuf
message SuggestTacticsRequest {
    string proof_id = 1;
    optional uint32 limit = 2;
}

message Tactic {
    string name = 1;
    repeated string args = 2;
    optional string description = 3;
    optional float confidence = 4;
}
```

## Connecting

```bash
grpcurl -plaintext localhost:50051 echidna.ProofService/ListProvers

grpcurl -plaintext -d '{
  "goal": "forall n, n + 0 = n",
  "prover": "COQ"
}' localhost:50051 echidna.ProofService/SubmitProof
```

[Documentation index](/docs/index.html)
