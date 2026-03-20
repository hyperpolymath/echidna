-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Per-Prover ABI: Top-Level Module
|||
||| Re-exports all 6 per-category prover ABI modules, covering the full
||| 30 prover backends in ECHIDNA with dependent type proofs for:
|||   - Protocol state machines (valid transitions only)
|||   - Tactic/command typing per prover family
|||   - Trust properties (kernel size, certificate formats)
|||   - Cross-prover compatibility (portfolio, delegation)
|||
||| Categories:
|||   InteractiveAssistants — 10 provers (Agda, Coq, Lean, Isabelle, Idris2,
|||                           F*, HOL4, HOL Light, Nuprl, Minlog)
|||   SmtSolvers           — 3 provers (Z3, CVC5, Alt-Ergo)
|||   FirstOrderAtp        — 3 provers (Vampire, E Prover, SPASS)
|||   DeclarativeProvers   — 7 provers (Metamath, Mizar, PVS, ACL2, TLAPS,
|||                           Twelf, Imandra)
|||   AutoActive           — 2 provers (Dafny, Why3)
|||   ConstraintSolvers    — 5 provers (GLPK, SCIP, MiniZinc, Chuffed, OR-Tools)
|||
||| Total: 30 provers, each with proven protocol correctness.

module EchidnaABI.Provers

import public EchidnaABI.Provers.InteractiveAssistants
import public EchidnaABI.Provers.SmtSolvers
import public EchidnaABI.Provers.FirstOrderAtp
import public EchidnaABI.Provers.DeclarativeProvers
import public EchidnaABI.Provers.AutoActive
import public EchidnaABI.Provers.ConstraintSolvers

import EchidnaABI.Types

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Prover Category Classification
-- ═══════════════════════════════════════════════════════════════════════

||| The category a prover belongs to.
public export
data ProverCategory
  = Interactive
  | Smt
  | Atp
  | Declarative
  | AutoActiveCat
  | Constraint

||| Classify every prover into its category.
public export
proverCategory : ProverKind -> ProverCategory
proverCategory Agda     = Interactive
proverCategory Coq      = Interactive
proverCategory Lean     = Interactive
proverCategory Isabelle  = Interactive
proverCategory Idris2   = Interactive
proverCategory FStar    = Interactive
proverCategory HOL4     = Interactive
proverCategory HOLLight = Interactive
proverCategory Nuprl    = Interactive
proverCategory Minlog   = Interactive
proverCategory Z3       = Smt
proverCategory CVC5     = Smt
proverCategory AltErgo  = Smt
proverCategory Vampire  = Atp
proverCategory EProver  = Atp
proverCategory SPASS    = Atp
proverCategory Metamath = Declarative
proverCategory Mizar    = Declarative
proverCategory PVS      = Declarative
proverCategory ACL2     = Declarative
proverCategory TLAPS    = Declarative
proverCategory Twelf    = Declarative
proverCategory Imandra  = Declarative
proverCategory Dafny    = AutoActiveCat
proverCategory Why3     = AutoActiveCat
proverCategory GLPK     = Constraint
proverCategory SCIP     = Constraint
proverCategory MiniZinc = Constraint
proverCategory Chuffed  = Constraint
proverCategory ORTools  = Constraint

||| Encode ProverCategory as C integer.
public export
proverCategoryToInt : ProverCategory -> Int
proverCategoryToInt Interactive   = 0
proverCategoryToInt Smt           = 1
proverCategoryToInt Atp           = 2
proverCategoryToInt Declarative   = 3
proverCategoryToInt AutoActiveCat = 4
proverCategoryToInt Constraint    = 5

-- ═══════════════════════════════════════════════════════════════════════
-- Universal State Transition Dispatcher
-- ═══════════════════════════════════════════════════════════════════════

||| Universal state transition validator.
||| Routes to the appropriate category-specific validator based on prover.
||| C ABI: returns 1 if valid, 0 if not.
public export
prover_can_transition : Int -> Int -> Int -> Int
prover_can_transition category from to =
  case category of
    0 => interactive_can_transition from to
    1 => smt_can_transition from to
    2 => atp_can_transition from to
    3 => verify_can_transition from to
    4 => pipeline_can_transition from to
    5 => csp_can_transition from to
    _ => 0
