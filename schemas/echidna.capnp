# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# ECHIDNA canonical Cap'n Proto wire schemas (L1 IPC)
#
# Replaces HTTP+JSON on the Rust↔Julia hot path. Transport: Unix domain
# socket (primary), TCP fallback. See docs/handover/L1-CAPNPROTO.md.
#
# Generate bindings: `just capnp-gen`
# Versioning: add fields at end of structs only. See schemas/VERSIONING.md.

@0xd3b45f8ae1c79012;

using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("echidna::ipc");

# ─── Core proof types ────────────────────────────────────────────────────────

struct ProofGoal {
  id          @0 :Text;
  prover      @1 :Text;
  content     @2 :Data;
  timeoutSecs @3 :UInt32 = 300;
  filePath    @4 :Text;
  metadata    @5 :List(KeyValue);
}

struct ProofResult {
  goalId      @0 :Text;
  prover      @1 :Text;
  verified    @2 :Bool;
  trustLevel  @3 :UInt8;
  elapsedMs   @4 :UInt64;
  outcome     @5 :OutcomeTag;
  message     @6 :Text;
  axiomReport @7 :AxiomReport;
  certHash    @8 :Text;

  enum OutcomeTag {
    proved               @0;
    noProofFound         @1;
    timeout              @2;
    invalidInput         @3;
    unsupportedFeature   @4;
    inconsistentPremises @5;
    proverError          @6;
    systemError          @7;
  }
}

# ─── GNN inference — L1 primary target (Rust↔Julia hot path) ─────────────────

struct GnnRankRequest {
  requestId        @0 :Text;
  graph            @1 :ProofGraph;
  topK             @2 :UInt32 = 20;
  minScore         @3 :Float32 = 0.05;
  includeEmbeddings @4 :Bool = false;
  numLayers        @5 :UInt32 = 4;
  useAttention     @6 :Bool = true;
}

struct GnnRankResponse {
  requestId    @0 :Text;
  rankings     @1 :List(PremiseScore);
  embeddings   @2 :List(NodeEmbedding);
  modelVersion @3 :Text;
  elapsedMs    @4 :UInt64;
}

struct ProofGraph {
  nodes       @0 :List(GraphNode);
  edges       @1 :List(GraphEdge);
  goalNodeIdx @2 :UInt32;
}

struct GraphNode {
  id        @0 :UInt32;
  kind      @1 :NodeKind;
  label     @2 :Text;
  embedding @3 :List(Float32);

  enum NodeKind {
    goal       @0;
    hypothesis @1;
    axiom      @2;
    definition @3;
    theorem    @4;
    tactic     @5;
    term       @6;
  }
}

struct GraphEdge {
  srcId  @0 :UInt32;
  dstId  @1 :UInt32;
  kind   @2 :EdgeKind;
  weight @3 :Float32 = 1.0;

  enum EdgeKind {
    appliesTo   @0;
    dependsOn   @1;
    similarTo   @2;
    refines     @3;
    contradicts @4;
    subsumes    @5;
    hasType     @6;
    hasSubterm  @7;
  }
}

struct PremiseScore {
  premiseId   @0 :Text;
  rank        @1 :UInt32;
  label       @2 :Text;
  nodeIdx     @3 :UInt32;
  explanation @4 :Text;
  score       @5 :Float32;
}

struct NodeEmbedding {
  nodeIdx @0 :UInt32;
  vector  @1 :List(Float32);
}

# ─── Trust pipeline ───────────────────────────────────────────────────────────

struct AxiomReport {
  usages     @0 :List(AxiomUsage);
  worstLevel @1 :DangerLevel;

  enum DangerLevel {
    safe    @0;
    noted   @1;
    warning @2;
    reject  @3;
  }
}

struct AxiomUsage {
  name        @0 :Text;
  danger      @1 :AxiomReport.DangerLevel;
  occurrences @2 :UInt32;
}

struct TrustedOutcome {
  result       @0 :ProofResult;
  crossChecked @1 :Bool;
  confirmedBy  @2 :List(Text);
  certChain    @3 :List(Text);
}

# ─── Chapel parallel dispatch — L2 ────────────────────────────────────────────

struct ProverInvocation {
  goalId      @0 :Text;
  provers     @1 :List(Text);
  strategy    @2 :DispatchStrategy;
  timeoutSecs @3 :UInt32 = 300;

  enum DispatchStrategy {
    firstWins @0;
    quorum    @1;
    portfolio @2;
  }
}

# ─── Utilities ────────────────────────────────────────────────────────────────

struct KeyValue {
  key   @0 :Text;
  value @1 :Text;
}
