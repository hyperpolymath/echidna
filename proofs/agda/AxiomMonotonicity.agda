-- SPDX-License-Identifier: PMPL-1.0-or-later
-- AxiomMonotonicity.agda — danger-level order and monotonicity of maxDanger.
--
-- Models ECHIDNA's 4-tier axiom-danger system (Safe < Noted < Warning < Reject)
-- and proves:
--   (a) maxDanger is monotone under list extension: prepending a higher-danger
--       axiom cannot decrease the running maximum.
--   (b) The worst function is idempotent on singleton lists:
--       worst [d] ≡ worst [worst [d]].

module AxiomMonotonicity where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)

------------------------------------------------------------------------
-- 1.  DangerLevel type and order
------------------------------------------------------------------------

data DangerLevel : Set where
  Safe    : DangerLevel   -- axiom is unrestricted
  Noted   : DangerLevel   -- axiom is unusual but allowed
  Warning : DangerLevel   -- axiom is suspicious, logged
  Reject  : DangerLevel   -- axiom triggers proof rejection

-- Reflexive order _≤ᴰ_: Safe ≤ Noted ≤ Warning ≤ Reject.
data _≤ᴰ_ : DangerLevel → DangerLevel → Set where
  safe-safe    : Safe    ≤ᴰ Safe
  safe-noted   : Safe    ≤ᴰ Noted
  safe-warn    : Safe    ≤ᴰ Warning
  safe-reject  : Safe    ≤ᴰ Reject
  noted-noted  : Noted   ≤ᴰ Noted
  noted-warn   : Noted   ≤ᴰ Warning
  noted-reject : Noted   ≤ᴰ Reject
  warn-warn    : Warning ≤ᴰ Warning
  warn-reject  : Warning ≤ᴰ Reject
  reject-rej   : Reject  ≤ᴰ Reject

infix 4 _≤ᴰ_

------------------------------------------------------------------------
-- 2.  Maximum of two danger levels
------------------------------------------------------------------------

-- maxD returns the higher of two DangerLevels.
maxD : DangerLevel → DangerLevel → DangerLevel
maxD Safe    d       = d
maxD Noted   Safe    = Noted
maxD Noted   Noted   = Noted
maxD Noted   Warning = Warning
maxD Noted   Reject  = Reject
maxD Warning Safe    = Warning
maxD Warning Noted   = Warning
maxD Warning Warning = Warning
maxD Warning Reject  = Reject
maxD Reject  _       = Reject

------------------------------------------------------------------------
-- 3.  maxD is an upper bound for both arguments
------------------------------------------------------------------------

maxD-ub-l : (a b : DangerLevel) → a ≤ᴰ maxD a b
-- maxD Safe b = b, so we need Safe ≤ b; dispatch on b.
maxD-ub-l Safe    Safe    = safe-safe
maxD-ub-l Safe    Noted   = safe-noted
maxD-ub-l Safe    Warning = safe-warn
maxD-ub-l Safe    Reject  = safe-reject
maxD-ub-l Noted   Safe    = noted-noted
maxD-ub-l Noted   Noted   = noted-noted
maxD-ub-l Noted   Warning = noted-warn
maxD-ub-l Noted   Reject  = noted-reject
maxD-ub-l Warning Safe    = warn-warn
maxD-ub-l Warning Noted   = warn-warn
maxD-ub-l Warning Warning = warn-warn
maxD-ub-l Warning Reject  = warn-reject
maxD-ub-l Reject  _       = reject-rej

maxD-ub-r : (a b : DangerLevel) → b ≤ᴰ maxD a b
maxD-ub-r Safe    b       = ≤ᴰ-refl b
  where
    ≤ᴰ-refl : (d : DangerLevel) → d ≤ᴰ d
    ≤ᴰ-refl Safe    = safe-safe
    ≤ᴰ-refl Noted   = noted-noted
    ≤ᴰ-refl Warning = warn-warn
    ≤ᴰ-refl Reject  = reject-rej
maxD-ub-r Noted   Safe    = safe-noted
maxD-ub-r Noted   Noted   = noted-noted
maxD-ub-r Noted   Warning = warn-warn
maxD-ub-r Noted   Reject  = reject-rej
maxD-ub-r Warning Safe    = safe-warn
maxD-ub-r Warning Noted   = noted-warn
maxD-ub-r Warning Warning = warn-warn
maxD-ub-r Warning Reject  = reject-rej
maxD-ub-r Reject  Safe    = safe-reject
maxD-ub-r Reject  Noted   = noted-reject
maxD-ub-r Reject  Warning = warn-reject
maxD-ub-r Reject  Reject  = reject-rej

------------------------------------------------------------------------
-- 4.  maxDanger: fold a list into its maximum DangerLevel
------------------------------------------------------------------------

-- Base case: an empty axiom list is Safe by convention.
maxDanger : List DangerLevel → DangerLevel
maxDanger []       = Safe
maxDanger (d ∷ ds) = maxD d (maxDanger ds)

------------------------------------------------------------------------
-- 5.  Transitivity helper for ≤ᴰ
------------------------------------------------------------------------

≤ᴰ-trans : {a b c : DangerLevel} → a ≤ᴰ b → b ≤ᴰ c → a ≤ᴰ c
≤ᴰ-trans safe-safe    p           = p
≤ᴰ-trans safe-noted   noted-noted = safe-noted
≤ᴰ-trans safe-noted   noted-warn  = safe-warn
≤ᴰ-trans safe-noted   noted-reject = safe-reject
≤ᴰ-trans safe-warn    warn-warn   = safe-warn
≤ᴰ-trans safe-warn    warn-reject = safe-reject
≤ᴰ-trans safe-reject  reject-rej  = safe-reject
≤ᴰ-trans noted-noted  p           = p
≤ᴰ-trans noted-warn   warn-warn   = noted-warn
≤ᴰ-trans noted-warn   warn-reject = noted-reject
≤ᴰ-trans noted-reject reject-rej  = noted-reject
≤ᴰ-trans warn-warn    p           = p
≤ᴰ-trans warn-reject  reject-rej  = warn-reject
≤ᴰ-trans reject-rej   reject-rej  = reject-rej

------------------------------------------------------------------------
-- 6.  (a) Monotonicity: prepending a higher-danger element cannot
--         decrease the maximum.
--
--     Formally: ∀ d ds → maxDanger ds ≤ᴰ maxDanger (d ∷ ds)
------------------------------------------------------------------------

-- First establish that maxD a b ≥ b (already have maxD-ub-r above).

-- Monotonicity: the maximum over a list can only grow when we prepend.
maxDanger-mono : (d : DangerLevel) (ds : List DangerLevel)
               → maxDanger ds ≤ᴰ maxDanger (d ∷ ds)
maxDanger-mono d ds = maxD-ub-r d (maxDanger ds)

------------------------------------------------------------------------
-- 7.  (b) worst on singleton lists is idempotent.
--
--     worst is just maxDanger.  On a singleton [d]:
--       worst [d]          = maxDanger [d]       = maxD d Safe = d   (by cases)
--       worst [worst [d]]  = worst [d]            = d
--     So worst [d] ≡ worst [worst [d]].
------------------------------------------------------------------------

-- Helper: maxDanger of a singleton equals the element.
-- maxDanger (d ∷ []) = maxD d (maxDanger []) = maxD d Safe
-- maxD Safe    Safe = Safe  ✓
-- maxD Noted   Safe = Noted ✓
-- maxD Warning Safe = Warning ✓
-- maxD Reject  Safe = Reject ✓
maxDanger-singleton : (d : DangerLevel) → maxDanger (d ∷ []) ≡ d
maxDanger-singleton Safe    = refl   -- maxD Safe Safe = Safe
maxDanger-singleton Noted   = refl   -- maxD Noted Safe = Noted (by definition)
maxDanger-singleton Warning = refl   -- maxD Warning Safe = Warning
maxDanger-singleton Reject  = refl   -- maxD Reject Safe = Reject

-- Idempotence of worst on singletons.
-- Proof by explicit case analysis: each case reduces definitionally.
worst-singleton-idempotent : (d : DangerLevel)
  → maxDanger (d ∷ []) ≡ maxDanger (maxDanger (d ∷ []) ∷ [])
worst-singleton-idempotent Safe    = refl
worst-singleton-idempotent Noted   = refl
worst-singleton-idempotent Warning = refl
worst-singleton-idempotent Reject  = refl
