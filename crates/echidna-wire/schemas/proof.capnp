@0xfa73f2ec7415f450;

using Common = import "common.capnp";
using Prover = import "prover.capnp";

struct ProofGoal {
  schemaVersion       @0 :UInt16 = 1;
  requestId           @1 :Text;
  sessionId           @2 :Text;
  goal                @3 :Common.Goal;
  context             @4 :Common.Context;
  preferredProverKind @5 :UInt16 = 65535;
  preferredProverName @6 :Text;
  timeoutMs           @7 :UInt32 = 300000;
  minTrustLevel       @8 :UInt8 = 2;
  crossCheck          @9 :Bool = false;
  requestDiagnostics  @10 :Bool = false;
  trackAxioms         @11 :Bool = true;
  generateCertificate @12 :Bool = false;
  metadataJson        @13 :Text;
}

struct ProofResult {
  schemaVersion       @0 :UInt16 = 1;
  requestId           @1 :Text;
  verified            @2 :Bool;
  trustLevel          @3 :UInt8;
  proversUsed         @4 :List(Text);
  proofTimeMs         @5 :UInt64;
  goalsRemaining      @6 :UInt32;
  message             @7 :Text;
  crossChecked        @8 :Bool;
  outcome             @9 :Prover.TrustedOutcome;
  axiomReport         @10 :Prover.AxiomUsage;
  hasAxiomReport      @11 :Bool;
  certificateHash     @12 :Text;
  hasCertificate      @13 :Bool;
  diagnostics         @14 :RunDiagnostics;
  hasDiagnostics      @15 :Bool;
}

struct RunDiagnostics {
  normalizedInput  @0 :Text;
  proversSelected  @1 :List(Text);
  perProver        @2 :List(PerProverRecord);
}

struct PerProverRecord {
  prover     @0 :Text;
  outcome    @1 :Prover.TrustedOutcome;
  elapsedMs  @2 :UInt64;
}
