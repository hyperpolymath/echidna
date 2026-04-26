-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| ECHIDNA ABI — Cap'n Proto Schema Mirror
|||
||| Idris2 data types that mirror the 7 Cap'n Proto message types in
||| schemas/echidna.capnp, together with constructive proofs of their
||| cardinality and bounded-representation invariants.
|||
||| These proofs guard the C-ABI bridge: before any serialisation round-trip
||| is attempted the type-checker guarantees that every enum fits in a UInt8
||| and that the schema identifier is genuinely non-zero.
|||
||| NO believe_me — every proof is constructive (Refl, Vect witness, %search).
||| NO postulate  — all properties derived from definitions.
|||
||| Schema ID : 0xd3b45f8ae1c79012  (echidna.capnp @0xd3b45f8ae1c79012)
||| Mirrors   : schemas/echidna.capnp
||| Status    : L1 pre-work; schema-evolution proofs deferred to L1 wave 1.

module EchidnaABI.CapnSchemas

import Data.Nat
import Data.Vect
import Data.Fin

%default total

------------------------------------------------------------------------
-- § 1  Schema identity
------------------------------------------------------------------------

||| The Cap'n Proto schema unique identifier for echidna.capnp.
||| Hex: 0xd3b45f8ae1c79012 = 15,242,516,543,891,767,314 (decimal).
public export
echidnaSchemaId : Nat
echidnaSchemaId = 15242516543891767314

||| Proof: the schema identifier is non-zero.
||| Cap'n Proto uses 0 as the "no schema" sentinel; a zero schema ID
||| would silently poison all wire messages.
public export
schemaIdNonZero : Not (echidnaSchemaId = 0)
schemaIdNonZero = \h => absurd h

------------------------------------------------------------------------
-- § 2  ProofGoal — 6 fields (5 data fields + 1 metadata list)
------------------------------------------------------------------------

||| Tags for the six fields of the Cap'n Proto `ProofGoal` struct.
||| Cap'n Proto field ordinals are listed as comments so that any future
||| change to the .capnp file immediately shows here as a mismatch.
public export
data ProofGoalTag
  = PG_Id          -- @0 :Text
  | PG_Prover      -- @1 :Text
  | PG_Content     -- @2 :Data
  | PG_TimeoutSecs -- @3 :UInt32
  | PG_FilePath    -- @4 :Text
  | PG_Metadata    -- @5 :List(KeyValue)

||| Total enumeration — one entry per field ordinal.
public export
allProofGoalTags : Vect 6 ProofGoalTag
allProofGoalTags =
  [ PG_Id, PG_Prover, PG_Content
  , PG_TimeoutSecs, PG_FilePath, PG_Metadata
  ]

public export
proofGoalFieldCount : Nat
proofGoalFieldCount = 6

||| Proof: ProofGoal has exactly 6 fields.
||| The Vect literal fixes the length at compile time; this is Refl.
public export
proofGoalFieldCountCorrect : length allProofGoalTags = proofGoalFieldCount
proofGoalFieldCountCorrect = Refl

------------------------------------------------------------------------
-- § 3  OutcomeTag — 8 variants  (ProofResult.OutcomeTag in .capnp)
------------------------------------------------------------------------

||| Mirrors `ProofResult.OutcomeTag` from schemas/echidna.capnp.
public export
data OutcomeTag
  = Proved               -- @0
  | NoProofFound         -- @1
  | Timeout              -- @2
  | InvalidInput         -- @3
  | UnsupportedFeature   -- @4
  | InconsistentPremises -- @5
  | ProverError          -- @6
  | SystemError          -- @7

public export
allOutcomeTags : Vect 8 OutcomeTag
allOutcomeTags =
  [ Proved, NoProofFound, Timeout, InvalidInput
  , UnsupportedFeature, InconsistentPremises, ProverError, SystemError
  ]

public export
outcomeTagCount : Nat
outcomeTagCount = 8

||| Proof: every OutcomeTag maps injectively to a Fin 8.
||| Injectivity guarantees no hidden collisions in the wire encoding.
public export
outcomeTagToFin : OutcomeTag -> Fin 8
outcomeTagToFin Proved               = 0
outcomeTagToFin NoProofFound         = 1
outcomeTagToFin Timeout              = 2
outcomeTagToFin InvalidInput         = 3
outcomeTagToFin UnsupportedFeature   = 4
outcomeTagToFin InconsistentPremises = 5
outcomeTagToFin ProverError          = 6
outcomeTagToFin SystemError          = 7

public export
outcomeTagToFinInjective
  : (a, b : OutcomeTag)
  -> outcomeTagToFin a = outcomeTagToFin b
  -> a = b
outcomeTagToFinInjective Proved               Proved               Refl = Refl
outcomeTagToFinInjective NoProofFound         NoProofFound         Refl = Refl
outcomeTagToFinInjective Timeout              Timeout              Refl = Refl
outcomeTagToFinInjective InvalidInput         InvalidInput         Refl = Refl
outcomeTagToFinInjective UnsupportedFeature   UnsupportedFeature   Refl = Refl
outcomeTagToFinInjective InconsistentPremises InconsistentPremises Refl = Refl
outcomeTagToFinInjective ProverError          ProverError          Refl = Refl
outcomeTagToFinInjective SystemError          SystemError          Refl = Refl

||| Proof: 8 outcome variants fit in a UInt8 (cardinality ≤ 256).
public export
outcomeBounded : LTE outcomeTagCount 256
outcomeBounded = %search

------------------------------------------------------------------------
-- § 4  NodeKind — 7 variants  (GraphNode.NodeKind in .capnp)
------------------------------------------------------------------------

||| Mirrors `GraphNode.NodeKind` from schemas/echidna.capnp.
public export
data CapnNodeKind
  = CNK_Goal       -- @0
  | CNK_Hypothesis -- @1
  | CNK_Axiom      -- @2
  | CNK_Definition -- @3
  | CNK_Theorem    -- @4
  | CNK_Tactic     -- @5
  | CNK_Term       -- @6

public export
allCapnNodeKinds : Vect 7 CapnNodeKind
allCapnNodeKinds =
  [ CNK_Goal, CNK_Hypothesis, CNK_Axiom, CNK_Definition
  , CNK_Theorem, CNK_Tactic, CNK_Term
  ]

public export
nodeKindCount : Nat
nodeKindCount = 7

public export
nodeKindCountCorrect : length allCapnNodeKinds = nodeKindCount
nodeKindCountCorrect = Refl

public export
nodeKindToFin : CapnNodeKind -> Fin 7
nodeKindToFin CNK_Goal       = 0
nodeKindToFin CNK_Hypothesis = 1
nodeKindToFin CNK_Axiom      = 2
nodeKindToFin CNK_Definition = 3
nodeKindToFin CNK_Theorem    = 4
nodeKindToFin CNK_Tactic     = 5
nodeKindToFin CNK_Term       = 6

public export
nodeKindToFinInjective
  : (a, b : CapnNodeKind)
  -> nodeKindToFin a = nodeKindToFin b
  -> a = b
nodeKindToFinInjective CNK_Goal       CNK_Goal       Refl = Refl
nodeKindToFinInjective CNK_Hypothesis CNK_Hypothesis Refl = Refl
nodeKindToFinInjective CNK_Axiom      CNK_Axiom      Refl = Refl
nodeKindToFinInjective CNK_Definition CNK_Definition Refl = Refl
nodeKindToFinInjective CNK_Theorem    CNK_Theorem    Refl = Refl
nodeKindToFinInjective CNK_Tactic     CNK_Tactic     Refl = Refl
nodeKindToFinInjective CNK_Term       CNK_Term       Refl = Refl

||| Proof: 7 node kinds fit in a UInt8.
public export
nodeKindBounded : LTE nodeKindCount 256
nodeKindBounded = %search

------------------------------------------------------------------------
-- § 5  EdgeKind — 8 variants  (GraphEdge.EdgeKind in .capnp)
------------------------------------------------------------------------

||| Mirrors `GraphEdge.EdgeKind` from schemas/echidna.capnp.
public export
data CapnEdgeKind
  = CEK_AppliesTo   -- @0
  | CEK_DependsOn   -- @1
  | CEK_SimilarTo   -- @2
  | CEK_Refines     -- @3
  | CEK_Contradicts -- @4
  | CEK_Subsumes    -- @5
  | CEK_HasType     -- @6
  | CEK_HasSubterm  -- @7

public export
allCapnEdgeKinds : Vect 8 CapnEdgeKind
allCapnEdgeKinds =
  [ CEK_AppliesTo, CEK_DependsOn, CEK_SimilarTo, CEK_Refines
  , CEK_Contradicts, CEK_Subsumes, CEK_HasType, CEK_HasSubterm
  ]

public export
edgeKindCount : Nat
edgeKindCount = 8

public export
edgeKindCountCorrect : length allCapnEdgeKinds = edgeKindCount
edgeKindCountCorrect = Refl

public export
edgeKindToFin : CapnEdgeKind -> Fin 8
edgeKindToFin CEK_AppliesTo   = 0
edgeKindToFin CEK_DependsOn   = 1
edgeKindToFin CEK_SimilarTo   = 2
edgeKindToFin CEK_Refines     = 3
edgeKindToFin CEK_Contradicts = 4
edgeKindToFin CEK_Subsumes    = 5
edgeKindToFin CEK_HasType     = 6
edgeKindToFin CEK_HasSubterm  = 7

public export
edgeKindToFinInjective
  : (a, b : CapnEdgeKind)
  -> edgeKindToFin a = edgeKindToFin b
  -> a = b
edgeKindToFinInjective CEK_AppliesTo   CEK_AppliesTo   Refl = Refl
edgeKindToFinInjective CEK_DependsOn   CEK_DependsOn   Refl = Refl
edgeKindToFinInjective CEK_SimilarTo   CEK_SimilarTo   Refl = Refl
edgeKindToFinInjective CEK_Refines     CEK_Refines     Refl = Refl
edgeKindToFinInjective CEK_Contradicts CEK_Contradicts Refl = Refl
edgeKindToFinInjective CEK_Subsumes    CEK_Subsumes    Refl = Refl
edgeKindToFinInjective CEK_HasType     CEK_HasType     Refl = Refl
edgeKindToFinInjective CEK_HasSubterm  CEK_HasSubterm  Refl = Refl

||| Proof: 8 edge kinds fit in a UInt8.
public export
edgeKindBounded : LTE edgeKindCount 256
edgeKindBounded = %search

------------------------------------------------------------------------
-- § 6  DangerLevel — 4 variants  (AxiomReport.DangerLevel in .capnp)
------------------------------------------------------------------------

||| Mirrors `AxiomReport.DangerLevel` from schemas/echidna.capnp.
public export
data CapnDangerLevel
  = CDL_Safe    -- @0
  | CDL_Noted   -- @1
  | CDL_Warning -- @2
  | CDL_Reject  -- @3

public export
allCapnDangerLevels : Vect 4 CapnDangerLevel
allCapnDangerLevels = [CDL_Safe, CDL_Noted, CDL_Warning, CDL_Reject]

public export
dangerLevelCount : Nat
dangerLevelCount = 4

public export
dangerLevelCountCorrect : length allCapnDangerLevels = dangerLevelCount
dangerLevelCountCorrect = Refl

public export
dangerLevelToFin : CapnDangerLevel -> Fin 4
dangerLevelToFin CDL_Safe    = 0
dangerLevelToFin CDL_Noted   = 1
dangerLevelToFin CDL_Warning = 2
dangerLevelToFin CDL_Reject  = 3

public export
dangerLevelToFinInjective
  : (a, b : CapnDangerLevel)
  -> dangerLevelToFin a = dangerLevelToFin b
  -> a = b
dangerLevelToFinInjective CDL_Safe    CDL_Safe    Refl = Refl
dangerLevelToFinInjective CDL_Noted   CDL_Noted   Refl = Refl
dangerLevelToFinInjective CDL_Warning CDL_Warning Refl = Refl
dangerLevelToFinInjective CDL_Reject  CDL_Reject  Refl = Refl

||| Proof: 4 danger levels fit in a UInt8.
public export
dangerLevelBounded : LTE dangerLevelCount 256
dangerLevelBounded = %search

------------------------------------------------------------------------
-- § 7  DispatchStrategy — 3 variants  (ProverInvocation in .capnp)
------------------------------------------------------------------------

||| Mirrors `ProverInvocation.DispatchStrategy` from schemas/echidna.capnp.
public export
data CapnDispatchStrategy
  = CDS_FirstWins -- @0
  | CDS_Quorum    -- @1
  | CDS_Portfolio -- @2

public export
allCapnDispatchStrategies : Vect 3 CapnDispatchStrategy
allCapnDispatchStrategies = [CDS_FirstWins, CDS_Quorum, CDS_Portfolio]

public export
dispatchStrategyCount : Nat
dispatchStrategyCount = 3

public export
dispatchStrategyCountCorrect : length allCapnDispatchStrategies = dispatchStrategyCount
dispatchStrategyCountCorrect = Refl

public export
dispatchStrategyToFin : CapnDispatchStrategy -> Fin 3
dispatchStrategyToFin CDS_FirstWins = 0
dispatchStrategyToFin CDS_Quorum    = 1
dispatchStrategyToFin CDS_Portfolio = 2

public export
dispatchStrategyToFinInjective
  : (a, b : CapnDispatchStrategy)
  -> dispatchStrategyToFin a = dispatchStrategyToFin b
  -> a = b
dispatchStrategyToFinInjective CDS_FirstWins CDS_FirstWins Refl = Refl
dispatchStrategyToFinInjective CDS_Quorum    CDS_Quorum    Refl = Refl
dispatchStrategyToFinInjective CDS_Portfolio CDS_Portfolio Refl = Refl

||| Proof: 3 dispatch strategies fit in a UInt8.
public export
dispatchStrategyBounded : LTE dispatchStrategyCount 256
dispatchStrategyBounded = %search

------------------------------------------------------------------------
-- § 8  GnnRankRequest default invariants
------------------------------------------------------------------------

||| Default topK value from the .capnp schema (`topK @2 :UInt32 = 20`).
public export
defaultTopK : Nat
defaultTopK = 20

||| Proof: the default topK is positive (> 0).
||| Required by the GNN ranking logic which uses topK as a loop bound.
public export
topKDefaultPositive : GT defaultTopK 0
topKDefaultPositive = %search
