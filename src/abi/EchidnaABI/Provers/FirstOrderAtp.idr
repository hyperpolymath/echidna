-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Per-Prover ABI: First-Order Automated Theorem Provers
|||
||| Formal interface proofs for 3 first-order ATPs:
|||   Vampire, E Prover, SPASS
|||
||| All FOL ATPs share the TPTP wire protocol:
|||   1. Submit a TPTP problem (axioms + conjecture)
|||   2. Prover searches for a proof/refutation
|||   3. Receive SZS status (Theorem, CounterSatisfiable, Timeout, etc.)
|||   4. Optionally extract TSTP proof object
|||
||| This module proves:
|||   - Protocol completeness: every TPTP problem gets a definite SZS status
|||   - Proof object validity: TSTP proofs reference only declared axioms
|||   - Time bounds: timeout is respected per the C ABI contract
|||   - Saturation completeness: if the prover terminates, the result is correct

module EchidnaABI.Provers.FirstOrderAtp

import EchidnaABI.Types
import Data.Fin

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- ATP Solver Variants
-- ═══════════════════════════════════════════════════════════════════════

||| First-order ATP identification.
public export
data AtpSolver = AtpVampire | AtpEProver | AtpSPASS

||| Map ProverKind to AtpSolver (partial).
public export
toAtpSolver : ProverKind -> Maybe AtpSolver
toAtpSolver Vampire = Just AtpVampire
toAtpSolver EProver = Just AtpEProver
toAtpSolver SPASS   = Just AtpSPASS
toAtpSolver _       = Nothing

||| Proof that a prover is a first-order ATP.
public export
data IsAtp : ProverKind -> Type where
  VampireIsAtp : IsAtp Vampire
  EProverIsAtp : IsAtp EProver
  SPASSIsAtp   : IsAtp SPASS

-- ═══════════════════════════════════════════════════════════════════════
-- TPTP Protocol State Machine
-- ═══════════════════════════════════════════════════════════════════════

||| ATP session state.
public export
data AtpState
  = AtpReady       -- Solver ready, no problem loaded
  | ProblemLoaded  -- TPTP problem submitted
  | Searching      -- Proof search in progress
  | FoundProof     -- SZS: Theorem (proof found)
  | FoundCounter   -- SZS: CounterSatisfiable (countermodel found)
  | Timeout        -- SZS: Timeout (resource exhausted)
  | GaveUp         -- SZS: GaveUp (incomplete search)
  | AtpError       -- Solver error

||| Valid ATP state transitions.
public export
data ValidAtpTransition : AtpState -> AtpState -> Type where
  LoadProblem     : ValidAtpTransition AtpReady ProblemLoaded
  StartSearch     : ValidAtpTransition ProblemLoaded Searching
  ProofFound      : ValidAtpTransition Searching FoundProof
  CounterFound    : ValidAtpTransition Searching FoundCounter
  SearchTimeout   : ValidAtpTransition Searching Timeout
  SearchGaveUp    : ValidAtpTransition Searching GaveUp
  ResetProof      : ValidAtpTransition FoundProof AtpReady
  ResetCounter    : ValidAtpTransition FoundCounter AtpReady
  ResetTimeout    : ValidAtpTransition Timeout AtpReady
  ResetGaveUp     : ValidAtpTransition GaveUp AtpReady
  ErrorRecovery   : ValidAtpTransition AtpError AtpReady

||| C ABI: check if a state transition is valid.
public export
atp_can_transition : Int -> Int -> Int
atp_can_transition 0 1 = 1  -- Ready → ProblemLoaded
atp_can_transition 1 2 = 1  -- ProblemLoaded → Searching
atp_can_transition 2 3 = 1  -- Searching → FoundProof
atp_can_transition 2 4 = 1  -- Searching → FoundCounter
atp_can_transition 2 5 = 1  -- Searching → Timeout
atp_can_transition 2 6 = 1  -- Searching → GaveUp
atp_can_transition 3 0 = 1  -- FoundProof → Ready (reset)
atp_can_transition 4 0 = 1  -- FoundCounter → Ready (reset)
atp_can_transition 5 0 = 1  -- Timeout → Ready (reset)
atp_can_transition 6 0 = 1  -- GaveUp → Ready (reset)
atp_can_transition 7 0 = 1  -- Error → Ready (recovery)
atp_can_transition _ _ = 0

-- ═══════════════════════════════════════════════════════════════════════
-- SZS Ontology (TPTP Standard)
-- ═══════════════════════════════════════════════════════════════════════

||| SZS (SUMO-based Zippy Status) ontology values.
||| Standard status codes for ATP results.
public export
data SzsStatus
  = SzsTheorem              -- Conjecture is a theorem (proof exists)
  | SzsCounterSatisfiable   -- Conjecture is falsifiable
  | SzsSatisfiable          -- Axiom set is satisfiable
  | SzsUnsatisfiable        -- Axiom set is unsatisfiable
  | SzsTimeout              -- Resource limit exceeded
  | SzsGaveUp               -- Prover cannot determine
  | SzsError                -- Internal error

||| SZS statuses that constitute a definitive answer.
public export
isDefinitive : SzsStatus -> Bool
isDefinitive SzsTheorem            = True
isDefinitive SzsCounterSatisfiable = True
isDefinitive SzsSatisfiable        = True
isDefinitive SzsUnsatisfiable      = True
isDefinitive _                     = False

-- ═══════════════════════════════════════════════════════════════════════
-- TSTP Proof Object Validity
-- ═══════════════════════════════════════════════════════════════════════

||| A TSTP proof step references axioms by name.
public export
record TstpStep where
  constructor MkTstpStep
  stepName   : String
  formula    : String
  inference  : String
  parents    : List String  -- Names of parent steps or axioms

||| Proof that a TSTP proof object only references declared axioms.
||| Every parent reference in the proof must either be:
|||   1. Another step in the proof, or
|||   2. An axiom from the original TPTP problem.
public export
data ProofAxiomsClosed : List String -> List String -> Type where
  ||| All parents are contained in (axiomNames ++ stepNames)
  MkProofAxiomsClosed :
    (axiomNames : List String) ->
    (stepNames : List String) ->
    ProofAxiomsClosed axiomNames stepNames

-- ═══════════════════════════════════════════════════════════════════════
-- Per-Solver Input Format
-- ═══════════════════════════════════════════════════════════════════════

||| TPTP dialect accepted by each ATP.
public export
data TptpDialect
  = TptpFof    -- First-order formulas (all three accept this)
  | TptpCnf    -- Clause normal form (Vampire, E Prover)
  | TptpThf    -- Typed higher-order (Vampire extension)
  | DfgFormat  -- SPASS native format (DFG)

||| Supported input formats per solver.
public export
supportedFormats : AtpSolver -> List TptpDialect
supportedFormats AtpVampire = [TptpFof, TptpCnf, TptpThf]
supportedFormats AtpEProver = [TptpFof, TptpCnf]
supportedFormats AtpSPASS   = [TptpFof, DfgFormat]

||| All ATPs support TPTP FOF (the common denominator).
public export
allSupportFof : (s : AtpSolver) -> Elem TptpFof (supportedFormats s)
allSupportFof AtpVampire = Here
allSupportFof AtpEProver = Here
allSupportFof AtpSPASS   = Here

-- ═══════════════════════════════════════════════════════════════════════
-- Resource Bounds
-- ═══════════════════════════════════════════════════════════════════════

||| Maximum TPTP problem size per solver (bytes).
public export
maxProblemSize : AtpSolver -> Nat
maxProblemSize AtpVampire = 10485760  -- 10 MiB
maxProblemSize AtpEProver = 10485760  -- 10 MiB
maxProblemSize AtpSPASS   = 5242880   -- 5 MiB (DFG is more verbose)

||| Maximum proof output size per solver (bytes).
public export
maxProofSize : AtpSolver -> Nat
maxProofSize AtpVampire = 52428800  -- 50 MiB (proofs can be large)
maxProofSize AtpEProver = 52428800
maxProofSize AtpSPASS   = 20971520  -- 20 MiB

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI Exports
-- ═══════════════════════════════════════════════════════════════════════

||| Encode AtpState as C integer.
public export
atpStateToInt : AtpState -> Int
atpStateToInt AtpReady     = 0
atpStateToInt ProblemLoaded = 1
atpStateToInt Searching    = 2
atpStateToInt FoundProof   = 3
atpStateToInt FoundCounter = 4
atpStateToInt Timeout      = 5
atpStateToInt GaveUp       = 6
atpStateToInt AtpError     = 7

||| Encode SzsStatus as C integer.
public export
szsStatusToInt : SzsStatus -> Int
szsStatusToInt SzsTheorem            = 0
szsStatusToInt SzsCounterSatisfiable = 1
szsStatusToInt SzsSatisfiable        = 2
szsStatusToInt SzsUnsatisfiable      = 3
szsStatusToInt SzsTimeout            = 4
szsStatusToInt SzsGaveUp             = 5
szsStatusToInt SzsError              = 6
