@0xf1841ae6bbc44651;

using Common = import "common.capnp";

struct AxiomUsage {
  proverKind   @0 :UInt16;
  proverName   @1 :Text;
  construct    @2 :Text;
  dangerLevel  @3 :UInt8;     # 0=Safe, 1=Noted, 2=Warning, 3=Reject
  explanation  @4 :Text;
  line         @5 :UInt32 = 0;
  hasLine      @6 :Bool;
}

struct ProverInvocation {
  schemaVersion    @0 :UInt16 = 1;
  requestId        @1 :Text;
  invocationId     @2 :Text;
  proverKind       @3 :UInt16;
  proverName       @4 :Text;
  goal             @5 :Common.Goal;
  context          @6 :Common.Context;
  executablePath   @7 :Text;
  libraryPaths     @8 :List(Text);
  extraArgs        @9 :List(Text);
  timeoutSecs     @10 :UInt32 = 300;
  neuralEnabled   @11 :Bool = true;
  portfolioMembers @12 :List(UInt16);
}

struct TrustedOutcome {
  schemaVersion   @0 :UInt16 = 1;
  invocationId    @1 :Text;

  status :union {
    proved               @2 :ProvedT;
    noProofFound         @3 :NoProofFoundT;
    invalidInput         @4 :InvalidInputT;
    unsupportedFeature   @5 :UnsupportedFeatureT;
    timeout              @6 :TimeoutT;
    inconsistentPremises @7 :InconsistentPremisesT;
    proverError          @8 :ProverErrorT;
    systemError          @9 :SystemErrorT;
  }

  trustLevel             @10 :UInt8;
  confirmingProvers      @11 :UInt32 = 1;
  hasCertificate         @12 :Bool;
  certificateVerified    @13 :Bool;
  certificateFormat      @14 :UInt8 = 255;
  certificateHashBlake3  @15 :Text;
  worstAxiomDanger       @16 :UInt8 = 0;
  solverIntegrityOk      @17 :Bool = true;
  portfolioConfidence    @18 :Float32 = 0;
  hasPortfolioConfidence @19 :Bool = false;
  axiomUsages            @20 :List(AxiomUsage);
  proverKind             @21 :UInt16;
  proverName             @22 :Text;

  struct ProvedT               { elapsedMs @0 :UInt64; }
  struct NoProofFoundT         { elapsedMs @0 :UInt64; reason @1 :Text; hasReason @2 :Bool; }
  struct InvalidInputT         { reason @0 :Text; location @1 :UInt32 = 0; hasLocation @2 :Bool; }
  struct UnsupportedFeatureT   { feature @0 :Text; }
  struct TimeoutT              { limitSecs @0 :UInt64; }
  struct InconsistentPremisesT { detail @0 :Text; hasDetail @1 :Bool; }
  struct ProverErrorT          { detail @0 :Text; exitCode @1 :Int32 = 0; hasExitCode @2 :Bool; }
  struct SystemErrorT          { detail @0 :Text; }
}
