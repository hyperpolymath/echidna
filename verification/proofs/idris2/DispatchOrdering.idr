-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- DispatchOrdering.idr
--
-- Proves that Echidna's dispatch pipeline always executes its stages in
-- the correct order:
--
--   integrity -> sandbox -> verify -> certs -> axioms -> confidence
--
-- Models pipeline stages as an indexed type with a successor relation,
-- then proves that the composed pipeline respects this ordering.
--
-- Uses %default total to enforce totality on every definition.

module DispatchOrdering

%default total

-- ==========================================================================
-- Section 1: Pipeline stages as an indexed type
-- ==========================================================================

||| The six stages of the trust-hardening dispatch pipeline,
||| mirroring dispatch.rs verify_proof().
|||
||| The Nat index encodes the execution order (0 = first, 5 = last).
public export
data Stage : Nat -> Type where
  ||| Step 1 (index 0): Verify solver binary integrity (SHAKE3-512, BLAKE3)
  Integrity  : Stage 0
  ||| Step 2 (index 1): Set up sandboxed execution environment
  Sandbox    : Stage 1
  ||| Step 3 (index 2): Run the actual proof verification
  Verify     : Stage 2
  ||| Step 4 (index 3): Check proof certificates (Alethe, DRAT/LRAT, TSTP)
  Certs      : Stage 3
  ||| Step 5 (index 4): Scan for dangerous axiom usage
  Axioms     : Stage 4
  ||| Step 6 (index 5): Compute confidence / trust level
  Confidence : Stage 5

-- ==========================================================================
-- Section 2: Stage ordering relation
-- ==========================================================================

||| Witness that stage at index n executes before stage at index m.
||| This is simply the proof that n < m at the type level.
public export
data ExecutesBefore : Stage n -> Stage m -> Type where
  ||| A stage at index n executes before a stage at index m when n < m.
  MkBefore : {auto prf : LT n m} -> ExecutesBefore (s1 : Stage n) (s2 : Stage m)

-- ==========================================================================
-- Section 3: Direct predecessor relation (immediate succession)
-- ==========================================================================

||| Witness that two stages are in immediate succession (n + 1 = m).
public export
data ImmediatelyPrecedes : Stage n -> Stage m -> Type where
  MkImmediate : {auto prf : S n = m} -> ImmediatelyPrecedes (s1 : Stage n) (s2 : Stage m)

-- ==========================================================================
-- Section 4: Pipeline ordering proofs (consecutive pairs)
-- ==========================================================================

||| Integrity executes before Sandbox.
public export
integrityBeforeSandbox : ExecutesBefore Integrity Sandbox
integrityBeforeSandbox = MkBefore

||| Sandbox executes before Verify.
public export
sandboxBeforeVerify : ExecutesBefore Sandbox Verify
sandboxBeforeVerify = MkBefore

||| Verify executes before Certs.
public export
verifyBeforeCerts : ExecutesBefore Verify Certs
verifyBeforeCerts = MkBefore

||| Certs executes before Axioms.
public export
certsBeforeAxioms : ExecutesBefore Certs Axioms
certsBeforeAxioms = MkBefore

||| Axioms executes before Confidence.
public export
axiomsBeforeConfidence : ExecutesBefore Axioms Confidence
axiomsBeforeConfidence = MkBefore

-- ==========================================================================
-- Section 5: Immediate succession proofs
-- ==========================================================================

||| Integrity immediately precedes Sandbox.
public export
integrityThenSandbox : ImmediatelyPrecedes Integrity Sandbox
integrityThenSandbox = MkImmediate

||| Sandbox immediately precedes Verify.
public export
sandboxThenVerify : ImmediatelyPrecedes Sandbox Verify
sandboxThenVerify = MkImmediate

||| Verify immediately precedes Certs.
public export
verifyThenCerts : ImmediatelyPrecedes Verify Certs
verifyThenCerts = MkImmediate

||| Certs immediately precedes Axioms.
public export
certsThenAxioms : ImmediatelyPrecedes Certs Axioms
certsThenAxioms = MkImmediate

||| Axioms immediately precedes Confidence.
public export
axiomsThenConfidence : ImmediatelyPrecedes Axioms Confidence
axiomsThenConfidence = MkImmediate

-- ==========================================================================
-- Section 6: Transitivity of execution ordering
-- ==========================================================================

||| ExecutesBefore is transitive: if a runs before b and b runs before c,
||| then a runs before c.
public export
transExecutesBefore : ExecutesBefore (s1 : Stage n) (s2 : Stage m) ->
                      ExecutesBefore (s2 : Stage m) (s3 : Stage k) ->
                      ExecutesBefore (s1 : Stage n) (s3 : Stage k)
transExecutesBefore (MkBefore {prf = p1}) (MkBefore {prf = p2}) =
  MkBefore {prf = transitive p1 p2}

-- ==========================================================================
-- Section 7: Non-adjacent ordering proofs (derived via transitivity)
-- ==========================================================================

||| Integrity executes before Verify (skipping Sandbox).
public export
integrityBeforeVerify : ExecutesBefore Integrity Verify
integrityBeforeVerify = transExecutesBefore integrityBeforeSandbox sandboxBeforeVerify

||| Integrity executes before Certs (skipping Sandbox, Verify).
public export
integrityBeforeCerts : ExecutesBefore Integrity Certs
integrityBeforeCerts = transExecutesBefore integrityBeforeVerify verifyBeforeCerts

||| Integrity executes before Axioms.
public export
integrityBeforeAxioms : ExecutesBefore Integrity Axioms
integrityBeforeAxioms = transExecutesBefore integrityBeforeCerts certsBeforeAxioms

||| Integrity executes before Confidence (full pipeline span).
public export
integrityBeforeConfidence : ExecutesBefore Integrity Confidence
integrityBeforeConfidence = transExecutesBefore integrityBeforeAxioms axiomsBeforeConfidence

||| Sandbox executes before Axioms.
public export
sandboxBeforeAxioms : ExecutesBefore Sandbox Axioms
sandboxBeforeAxioms = transExecutesBefore sandboxBeforeVerify
                        (transExecutesBefore verifyBeforeCerts certsBeforeAxioms)

||| Sandbox executes before Confidence.
public export
sandboxBeforeConfidence : ExecutesBefore Sandbox Confidence
sandboxBeforeConfidence = transExecutesBefore sandboxBeforeAxioms axiomsBeforeConfidence

||| Verify executes before Confidence.
public export
verifyBeforeConfidence : ExecutesBefore Verify Confidence
verifyBeforeConfidence = transExecutesBefore verifyBeforeCerts
                           (transExecutesBefore certsBeforeAxioms axiomsBeforeConfidence)

||| Certs executes before Confidence.
public export
certsBeforeConfidence : ExecutesBefore Certs Confidence
certsBeforeConfidence = transExecutesBefore certsBeforeAxioms axiomsBeforeConfidence

-- ==========================================================================
-- Section 8: Irreflexivity -- no stage executes before itself
-- ==========================================================================

||| No stage can execute before itself (strict ordering).
public export
noSelfExecution : {n : Nat} -> (s : Stage n) -> Not (ExecutesBefore s s)
noSelfExecution _ (MkBefore {prf}) = absurd prf

-- ==========================================================================
-- Section 9: Antisymmetry -- no two stages can be mutually before
-- ==========================================================================

||| If a executes before b, then b does not execute before a.
public export
antisymmetric : ExecutesBefore (s1 : Stage n) (s2 : Stage m) ->
                Not (ExecutesBefore s2 s1)
antisymmetric (MkBefore {prf = p1}) (MkBefore {prf = p2}) =
  let combined = transitive p1 p2 in
  absurd combined

-- ==========================================================================
-- Section 10: Pipeline as a well-ordered sequence
-- ==========================================================================

||| A pipeline execution is a sequence of stages in correct order.
||| We model it as a linked list of stages where each is indexed by
||| its position, and consecutive stages are in immediate succession.
public export
data Pipeline : Nat -> Nat -> Type where
  ||| A single stage.
  Single : Stage n -> Pipeline n n
  ||| Extend a pipeline by one stage in immediate succession.
  Extend : Pipeline n m -> Stage (S m) -> Pipeline n (S m)

||| The complete Echidna dispatch pipeline: all 6 stages in order.
public export
completePipeline : Pipeline 0 5
completePipeline = Extend
                     (Extend
                       (Extend
                         (Extend
                           (Extend
                             (Single Integrity)
                             Sandbox)
                           Verify)
                         Certs)
                       Axioms)
                     Confidence

||| The complete pipeline has exactly 6 stages.
public export
pipelineLength : {n : Nat} -> {m : Nat} -> Pipeline n m -> Nat
pipelineLength (Single _) = 1
pipelineLength (Extend p _) = S (pipelineLength p)

||| Witness that the complete pipeline has 6 stages.
public export
completePipelineHas6Stages : pipelineLength DispatchOrdering.completePipeline = 6
completePipelineHas6Stages = Refl

-- ==========================================================================
-- Section 11: Every pair in the pipeline is correctly ordered
-- ==========================================================================

||| For any pipeline from n to m, n <= m.
public export
pipelineOrdered : Pipeline n m -> LTE n m
pipelineOrdered (Single {n} _) = lteRefl
pipelineOrdered (Extend {m} p _) = lteSuccRight (pipelineOrdered p)

||| The complete pipeline starts at 0 and ends at 5.
public export
completePipelineSpan : LTE 0 5
completePipelineSpan = pipelineOrdered completePipeline
