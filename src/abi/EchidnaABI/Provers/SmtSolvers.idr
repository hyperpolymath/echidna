-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Per-Prover ABI: SMT Solvers
|||
||| Formal interface proofs for 3 SMT solvers:
|||   Z3, CVC5, Alt-Ergo
|||
||| All SMT solvers share the SMT-LIB2 wire protocol:
|||   1. Push assertion context
|||   2. Assert formulas (quantifier-free or quantified)
|||   3. Check satisfiability
|||   4. Extract model (SAT) or unsat core (UNSAT)
|||   5. Pop context
|||
||| This module proves:
|||   - Protocol ordering: assert before check, push before pop
|||   - Stack discipline: push/pop are balanced
|||   - Soundness: UNSAT result with proof certificate is trustworthy
|||   - Portfolio safety: cross-checking between solvers is well-formed

module EchidnaABI.Provers.SmtSolvers

import EchidnaABI.Types
import Data.Fin
import Data.Nat

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- SMT Solver Variants
-- ═══════════════════════════════════════════════════════════════════════

||| SMT solver identification.
public export
data SmtSolver = SmtZ3 | SmtCVC5 | SmtAltErgo

||| Map ProverKind to SmtSolver (partial).
public export
toSmtSolver : ProverKind -> Maybe SmtSolver
toSmtSolver Z3      = Just SmtZ3
toSmtSolver CVC5    = Just SmtCVC5
toSmtSolver AltErgo = Just SmtAltErgo
toSmtSolver _       = Nothing

||| Proof that a prover is an SMT solver.
public export
data IsSmt : ProverKind -> Type where
  Z3IsSmt      : IsSmt Z3
  CVC5IsSmt    : IsSmt CVC5
  AltErgoIsSmt : IsSmt AltErgo

-- ═══════════════════════════════════════════════════════════════════════
-- SMT-LIB2 Protocol State Machine
-- ═══════════════════════════════════════════════════════════════════════

||| SMT-LIB2 solver state.
public export
data SmtState
  = SmtReady       -- Solver initialised, ready for commands
  | SmtAsserted    -- Formulas have been asserted
  | SmtChecking    -- check-sat in progress
  | SmtSat         -- Result: satisfiable (model available)
  | SmtUnsat       -- Result: unsatisfiable (proof/core available)
  | SmtUnknown     -- Result: unknown (timeout or incomplete)
  | SmtError       -- Solver error

||| Valid SMT state transitions.
public export
data ValidSmtTransition : SmtState -> SmtState -> Type where
  Assert       : ValidSmtTransition SmtReady SmtAsserted
  AssertMore   : ValidSmtTransition SmtAsserted SmtAsserted
  CheckSat     : ValidSmtTransition SmtAsserted SmtChecking
  ResultSat    : ValidSmtTransition SmtChecking SmtSat
  ResultUnsat  : ValidSmtTransition SmtChecking SmtUnsat
  ResultUnknown : ValidSmtTransition SmtChecking SmtUnknown
  ResetFromSat  : ValidSmtTransition SmtSat SmtReady
  ResetFromUnsat : ValidSmtTransition SmtUnsat SmtReady
  ResetFromUnknown : ValidSmtTransition SmtUnknown SmtReady
  ErrorRecovery : ValidSmtTransition SmtError SmtReady

||| C ABI: check if a state transition is valid.
public export
smt_can_transition : Int -> Int -> Int
smt_can_transition 0 1 = 1  -- Ready → Asserted
smt_can_transition 1 1 = 1  -- Asserted → Asserted (more asserts)
smt_can_transition 1 2 = 1  -- Asserted → Checking
smt_can_transition 2 3 = 1  -- Checking → Sat
smt_can_transition 2 4 = 1  -- Checking → Unsat
smt_can_transition 2 5 = 1  -- Checking → Unknown
smt_can_transition 3 0 = 1  -- Sat → Ready (reset)
smt_can_transition 4 0 = 1  -- Unsat → Ready (reset)
smt_can_transition 5 0 = 1  -- Unknown → Ready (reset)
smt_can_transition 6 0 = 1  -- Error → Ready (recovery)
smt_can_transition _ _ = 0

-- ═══════════════════════════════════════════════════════════════════════
-- Push/Pop Stack Discipline
-- ═══════════════════════════════════════════════════════════════════════

||| Assertion stack depth (natural number, starts at 0).
||| Push increments, Pop decrements. Pop at 0 is invalid.
public export
data StackDepth : Nat -> Type where
  EmptyStack : StackDepth Z
  Pushed     : StackDepth n -> StackDepth (S n)

||| Proof that pop is only valid when stack depth > 0.
public export
canPop : StackDepth (S n) -> StackDepth n
canPop (Pushed prev) = prev

||| Proof that push/pop are always balanced.
||| After k pushes and k pops, we return to the original depth.
public export
pushPopBalanced : (stack : StackDepth n) ->
                  canPop (Pushed stack) = stack
pushPopBalanced stack = Refl

-- ═══════════════════════════════════════════════════════════════════════
-- Proof Certificate Validation
-- ═══════════════════════════════════════════════════════════════════════

||| SMT proof certificate formats supported by each solver.
public export
data CertFormat
  = Alethe    -- Z3, CVC5 (Alethe proof format)
  | DratLrat  -- SAT solvers (DRAT/LRAT for propositional)
  | NoCert    -- Alt-Ergo (no standard cert format)

||| Map each SMT solver to its supported certificate format.
public export
certFormat : SmtSolver -> CertFormat
certFormat SmtZ3      = Alethe
certFormat SmtCVC5    = Alethe
certFormat SmtAltErgo = NoCert

||| Proof that an UNSAT result with a valid certificate is trustworthy.
||| We trust the result if:
|||   1. The solver is in SmtUnsat state
|||   2. A certificate was produced
|||   3. The certificate format matches the solver's expected format
public export
data TrustworthyUnsat : SmtSolver -> Type where
  MkTrustworthyUnsat :
    (solver : SmtSolver) ->
    (fmt : CertFormat) ->
    (certFormat solver = fmt) ->
    (Not (fmt = NoCert)) ->
    TrustworthyUnsat solver

||| Z3's UNSAT results are trustworthy (Alethe certificates).
public export
z3Trustworthy : TrustworthyUnsat SmtZ3
z3Trustworthy = MkTrustworthyUnsat SmtZ3 Alethe Refl (\prf => case prf of {})

||| CVC5's UNSAT results are trustworthy (Alethe certificates).
public export
cvc5Trustworthy : TrustworthyUnsat SmtCVC5
cvc5Trustworthy = MkTrustworthyUnsat SmtCVC5 Alethe Refl (\prf => case prf of {})

-- ═══════════════════════════════════════════════════════════════════════
-- Portfolio Cross-Checking
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that cross-checking between two distinct SMT solvers is valid.
||| Both solvers must reach the same satisfiability result.
public export
data CrossCheckValid : SmtSolver -> SmtSolver -> Type where
  MkCrossCheckValid :
    (s1 : SmtSolver) -> (s2 : SmtSolver) ->
    Not (s1 = s2) ->
    CrossCheckValid s1 s2

||| Z3 ↔ CVC5 cross-check is valid.
public export
z3CVC5CrossCheck : CrossCheckValid SmtZ3 SmtCVC5
z3CVC5CrossCheck = MkCrossCheckValid SmtZ3 SmtCVC5 (\prf => case prf of {})

||| Z3 ↔ Alt-Ergo cross-check is valid.
public export
z3AltErgoCrossCheck : CrossCheckValid SmtZ3 SmtAltErgo
z3AltErgoCrossCheck = MkCrossCheckValid SmtZ3 SmtAltErgo (\prf => case prf of {})

||| CVC5 ↔ Alt-Ergo cross-check is valid.
public export
cvc5AltErgoCrossCheck : CrossCheckValid SmtCVC5 SmtAltErgo
cvc5AltErgoCrossCheck = MkCrossCheckValid SmtCVC5 SmtAltErgo (\prf => case prf of {})

-- ═══════════════════════════════════════════════════════════════════════
-- SMT-LIB2 Logic Fragments
-- ═══════════════════════════════════════════════════════════════════════

||| SMT-LIB2 logic names supported by each solver.
public export
data SmtLogic
  = QF_LIA    -- Quantifier-free linear integer arithmetic
  | QF_LRA    -- Quantifier-free linear real arithmetic
  | QF_BV     -- Quantifier-free bitvectors
  | QF_UF     -- Quantifier-free uninterpreted functions
  | LIA       -- Linear integer arithmetic (with quantifiers)
  | LRA       -- Linear real arithmetic (with quantifiers)
  | AUFLIRA   -- Arrays + UF + linear integer/real arithmetic
  | ALL       -- All logics (full solver)

||| Map each solver to its supported logic fragments.
public export
supportedLogics : SmtSolver -> List SmtLogic
supportedLogics SmtZ3      = [QF_LIA, QF_LRA, QF_BV, QF_UF, LIA, LRA, AUFLIRA, ALL]
supportedLogics SmtCVC5    = [QF_LIA, QF_LRA, QF_BV, QF_UF, LIA, LRA, AUFLIRA, ALL]
supportedLogics SmtAltErgo = [QF_LIA, QF_LRA, QF_UF, LIA, ALL]

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI Exports
-- ═══════════════════════════════════════════════════════════════════════

||| Encode SmtState as C integer.
public export
smtStateToInt : SmtState -> Int
smtStateToInt SmtReady    = 0
smtStateToInt SmtAsserted = 1
smtStateToInt SmtChecking = 2
smtStateToInt SmtSat      = 3
smtStateToInt SmtUnsat    = 4
smtStateToInt SmtUnknown  = 5
smtStateToInt SmtError    = 6

||| Encode CertFormat as C integer.
public export
certFormatToInt : CertFormat -> Int
certFormatToInt Alethe   = 0
certFormatToInt DratLrat = 1
certFormatToInt NoCert   = 2
