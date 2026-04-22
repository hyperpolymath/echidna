@0xfbb66b8481def8a0;

using Common = import "common.capnp";

struct GnnGraphPayload {
  numNodes             @0  :UInt32;
  numEdges             @1  :UInt32;
  edgeSrc              @2  :List(UInt32);
  edgeDst              @3  :List(UInt32);
  edgeWeights          @4  :List(Float32);
  edgeKinds            @5  :List(Text);
  nodeFeatures         @6  :List(Float32);
  featureDim           @7  :UInt32;
  nodeKinds            @8  :List(Text);
  nodeLabels           @9  :List(Text);
  goalNodeIdx          @10 :UInt32 = 4294967295;
  hasGoalNode          @11 :Bool;
  premiseNodeIndices   @12 :List(UInt32);
}

struct GnnServerHints {
  numGnnLayers   @0 :UInt16 = 4;
  useAttention   @1 :Bool   = true;
}

struct GnnRankRequest {
  schemaVersion      @0 :UInt16 = 1;
  requestId          @1 :Text;
  graph              @2 :GnnGraphPayload;
  topK               @3 :UInt32 = 20;
  minScore           @4 :Float32 = 0.05;
  includeEmbeddings  @5 :Bool    = false;
  config             @6 :GnnServerHints;
}

struct FloatVec { values @0 :List(Float32); }

struct GnnRankResponse {
  schemaVersion      @0 :UInt16 = 1;
  requestId          @1 :Text;
  success            @2 :Bool;
  scores             @3 :List(Float32);
  premiseNames       @4 :List(Text);
  embeddings         @5 :List(FloatVec);
  inferenceTimeMs    @6 :Float32;
  error              @7 :Text;
}

struct TacticSuggestion {
  schemaVersion     @0 :UInt16 = 1;
  requestId         @1 :Text;
  tactic            @2 :Text;
  structuredTactic  @3 :Common.Tactic;
  hasStructured     @4 :Bool;
  confidence        @5 :Float32;
  premise           @6 :Text;
  hasPremise        @7 :Bool;
  aspectTags        @8 :List(Text);
  gnnScore          @9 :Float32 = 0;
  symbolicScore    @10 :Float32 = 0;
  fromServer       @11 :Bool   = false;
}
