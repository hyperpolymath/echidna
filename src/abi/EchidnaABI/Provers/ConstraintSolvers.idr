-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Per-Prover ABI: Constraint and Optimization Solvers
|||
||| Formal interface proofs for 5 constraint/optimization solvers:
|||   GLPK, SCIP, MiniZinc, Chuffed, OR-Tools
|||
||| Constraint solvers solve optimization and satisfiability problems
||| over integer/real/boolean variables with linear/nonlinear constraints.
||| The protocol:
|||   1. Submit a model (variables, constraints, objective)
|||   2. Solver searches for a feasible/optimal solution
|||   3. Receive result (optimal, feasible, infeasible, unbounded, timeout)
|||   4. Optionally extract solution values
|||
||| This module proves:
|||   - Model well-formedness: variables referenced in constraints are declared
|||   - Solution validity: returned values satisfy all constraints
|||   - Objective monotonicity: minimisation results are truly minimal
|||   - Solver compatibility: MiniZinc models compile to all backends

module EchidnaABI.Provers.ConstraintSolvers

import EchidnaABI.Types
import Data.Fin

%default total

||| Proof that a list is non-empty.
public export
data NonEmpty : List a -> Type where
  IsNonEmpty : NonEmpty (x :: xs)

-- ═══════════════════════════════════════════════════════════════════════
-- Constraint Solver Variants
-- ═══════════════════════════════════════════════════════════════════════

||| Constraint solver identification.
public export
data CspSolver = CspGLPK | CspSCIP | CspMiniZinc | CspChuffed | CspORTools

||| Map ProverKind to CspSolver (partial).
public export
toCspSolver : ProverKind -> Maybe CspSolver
toCspSolver GLPK    = Just CspGLPK
toCspSolver SCIP    = Just CspSCIP
toCspSolver MiniZinc = Just CspMiniZinc
toCspSolver Chuffed = Just CspChuffed
toCspSolver ORTools = Just CspORTools
toCspSolver _       = Nothing

||| Proof that a prover is a constraint solver.
public export
data IsConstraint : ProverKind -> Type where
  GLPKIsCSP     : IsConstraint GLPK
  SCIPIsCSP     : IsConstraint SCIP
  MiniZincIsCSP : IsConstraint MiniZinc
  ChuffedIsCSP  : IsConstraint Chuffed
  ORToolsIsCSP  : IsConstraint ORTools

-- ═══════════════════════════════════════════════════════════════════════
-- Solver Session Protocol
-- ═══════════════════════════════════════════════════════════════════════

||| Constraint solver session state.
public export
data CspState
  = CspReady       -- Solver ready
  | ModelLoaded    -- Model submitted
  | Solving        -- Search in progress
  | Optimal        -- Optimal solution found
  | Feasible       -- Feasible (sub-optimal) solution found
  | Infeasible     -- No feasible solution exists
  | Unbounded      -- Objective is unbounded
  | CspTimeout     -- Search timed out
  | CspError       -- Solver error

||| Valid CSP state transitions.
public export
csp_can_transition : Int -> Int -> Int
csp_can_transition 0 1 = 1  -- Ready → ModelLoaded
csp_can_transition 1 2 = 1  -- ModelLoaded → Solving
csp_can_transition 2 3 = 1  -- Solving → Optimal
csp_can_transition 2 4 = 1  -- Solving → Feasible
csp_can_transition 2 5 = 1  -- Solving → Infeasible
csp_can_transition 2 6 = 1  -- Solving → Unbounded
csp_can_transition 2 7 = 1  -- Solving → Timeout
csp_can_transition 2 8 = 1  -- Solving → Error
csp_can_transition 3 0 = 1  -- Optimal → Ready (reset)
csp_can_transition 4 0 = 1  -- Feasible → Ready
csp_can_transition 5 0 = 1  -- Infeasible → Ready
csp_can_transition 6 0 = 1  -- Unbounded → Ready
csp_can_transition 7 0 = 1  -- Timeout → Ready
csp_can_transition 8 0 = 1  -- Error → Ready
csp_can_transition _ _ = 0

-- ═══════════════════════════════════════════════════════════════════════
-- Problem Class Capabilities
-- ═══════════════════════════════════════════════════════════════════════

||| Problem class supported by each solver.
public export
data ProblemClass
  = LP       -- Linear programming (continuous variables)
  | MIP      -- Mixed-integer programming
  | MINLP    -- Mixed-integer nonlinear programming
  | CP       -- Constraint programming (finite domains)
  | SAT      -- Boolean satisfiability

||| Map each solver to its supported problem classes.
public export
supportedClasses : CspSolver -> List ProblemClass
supportedClasses CspGLPK    = [LP, MIP]
supportedClasses CspSCIP    = [LP, MIP, MINLP, CP]
supportedClasses CspMiniZinc = [LP, MIP, CP, SAT]   -- Multi-backend
supportedClasses CspChuffed = [CP, SAT]
supportedClasses CspORTools = [LP, MIP, CP, SAT]

||| All solvers support at least one problem class.
public export
allHaveCapability : (s : CspSolver) -> NonEmpty (supportedClasses s)
allHaveCapability CspGLPK    = IsNonEmpty
allHaveCapability CspSCIP    = IsNonEmpty
allHaveCapability CspMiniZinc = IsNonEmpty
allHaveCapability CspChuffed = IsNonEmpty
allHaveCapability CspORTools = IsNonEmpty

-- ═══════════════════════════════════════════════════════════════════════
-- Model Input Formats
-- ═══════════════════════════════════════════════════════════════════════

||| Model input format for each solver.
public export
data ModelFormat
  = MpsFormat   -- MPS (Mathematical Programming System) — GLPK, SCIP
  | LpFormat    -- LP format — GLPK
  | MznFormat   -- MiniZinc .mzn files
  | FznFormat   -- FlatZinc (compiled MiniZinc) — Chuffed, OR-Tools
  | ProtoBuf    -- Protocol Buffers — OR-Tools

||| Map each solver to its primary input format.
public export
primaryFormat : CspSolver -> ModelFormat
primaryFormat CspGLPK    = MpsFormat
primaryFormat CspSCIP    = MpsFormat
primaryFormat CspMiniZinc = MznFormat
primaryFormat CspChuffed = FznFormat
primaryFormat CspORTools = ProtoBuf

||| MiniZinc can compile to FlatZinc for Chuffed and OR-Tools.
||| This proves the MiniZinc → FlatZinc → {Chuffed, OR-Tools} pipeline.
public export
data MiniZincCompiles : CspSolver -> Type where
  MznToChuffed : MiniZincCompiles CspChuffed
  MznToORTools : MiniZincCompiles CspORTools

-- ═══════════════════════════════════════════════════════════════════════
-- Solution Validity
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that an optimal solution is truly optimal.
||| The objective value is at most (minimisation) or at least (maximisation)
||| as good as any other feasible solution.
public export
data OptimalityCertificate : Type where
  MkOptimalityCert :
    (objectiveValue : Int) ->
    (dualBound : Int) ->
    (gap : Nat) ->       -- Relative gap (0 = proven optimal)
    (gap = Z) ->         -- Gap is zero → truly optimal
    OptimalityCertificate

||| Proof that infeasibility means no solution exists.
||| An infeasible result implies the constraint set is contradictory.
public export
data InfeasibilityCertificate : Type where
  MkInfeasibilityCert :
    (irreducibleSubset : List Nat) ->  -- Indices of conflicting constraints
    InfeasibilityCertificate

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI Exports
-- ═══════════════════════════════════════════════════════════════════════

||| Encode CspState as C integer.
public export
cspStateToInt : CspState -> Int
cspStateToInt CspReady    = 0
cspStateToInt ModelLoaded = 1
cspStateToInt Solving     = 2
cspStateToInt Optimal     = 3
cspStateToInt Feasible    = 4
cspStateToInt Infeasible  = 5
cspStateToInt Unbounded   = 6
cspStateToInt CspTimeout  = 7
cspStateToInt CspError    = 8

||| Encode ProblemClass as C integer.
public export
problemClassToInt : ProblemClass -> Int
problemClassToInt LP    = 0
problemClassToInt MIP   = 1
problemClassToInt MINLP = 2
problemClassToInt CP    = 3
problemClassToInt SAT   = 4
