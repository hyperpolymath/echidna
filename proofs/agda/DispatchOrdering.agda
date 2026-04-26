-- SPDX-License-Identifier: PMPL-1.0-or-later
-- DispatchOrdering.agda — strict total order on the 6-stage trust pipeline.
--
-- Models ECHIDNA's dispatch pipeline stages (dispatch.rs) as a Fin 6 type and
-- proves:
--   1. The strict order _<_ on Fin 6 is irreflexive, asymmetric, and transitive
--      (strict partial order), and has trichotomy (strict total order).
--   2. The Integrity stage (zero : Fin 6) strictly precedes every other stage.
--
-- All proofs delegate to the existing Data.Fin / Data.Fin.Properties machinery.

module DispatchOrdering where

open import Data.Fin       using (Fin; zero; suc; toℕ; _<_)
open import Data.Fin.Properties
  using (<-irrefl; <-trans; <-cmp; <-isStrictTotalOrder)
open import Data.Nat.Base  using (z<s; s<s)
open import Relation.Binary.Definitions
  using (Irreflexive; Transitive; Trichotomous; Asymmetric)
open import Relation.Binary.Structures
  using (IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_)
open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- 1.  Stage names (aliases for elements of Fin 6)
------------------------------------------------------------------------

-- The six pipeline stages in execution order.
Stage : Set
Stage = Fin 6

Integrity   : Stage
Integrity   = zero                 -- 0 : first gate — hash-check solver binary

Sandbox     : Stage
Sandbox     = suc zero             -- 1 : bubblewrap / Podman sandbox

Verify      : Stage
Verify      = suc (suc zero)       -- 2 : proof certificate checking

Certs       : Stage
Certs       = suc (suc (suc zero)) -- 3 : certificate chain validation

Axioms      : Stage
Axioms      = suc (suc (suc (suc zero)))           -- 4 : axiom danger tracking

Confidence  : Stage
Confidence  = suc (suc (suc (suc (suc zero))))     -- 5 : portfolio confidence

------------------------------------------------------------------------
-- 2.  The ordering is a strict total order (from Data.Fin.Properties)
------------------------------------------------------------------------

-- Irreflexivity: no stage precedes itself.
stage-<-irrefl : Irreflexive {A = Stage} _≡_ _<_
stage-<-irrefl = <-irrefl

-- Transitivity: if stage i precedes stage j and j precedes k then i precedes k.
stage-<-trans : Transitive {A = Stage} _<_
stage-<-trans = <-trans

-- Asymmetry: derived from irreflexivity + transitivity.
stage-<-asym : Asymmetric {A = Stage} _<_
stage-<-asym {i} {j} i<j j<i = <-irrefl refl (<-trans i<j j<i)

-- Trichotomy: for any two stages exactly one of i < j, i ≡ j, j < i holds.
stage-<-trichotomous : Trichotomous {A = Stage} _≡_ _<_
stage-<-trichotomous = <-cmp

-- Convenience: the standard-library IsStrictTotalOrder record.
stage-strictTotalOrder : IsStrictTotalOrder {A = Stage} _≡_ _<_
stage-strictTotalOrder = <-isStrictTotalOrder

------------------------------------------------------------------------
-- 3.  Integrity precedes every other stage
------------------------------------------------------------------------

-- Integrity strictly precedes Sandbox.
integrity-before-sandbox : Integrity < Sandbox
integrity-before-sandbox = z<s

-- Integrity strictly precedes Verify.
integrity-before-verify : Integrity < Verify
integrity-before-verify = z<s

-- Integrity strictly precedes Certs.
integrity-before-certs : Integrity < Certs
integrity-before-certs = z<s

-- Integrity strictly precedes Axioms.
integrity-before-axioms : Integrity < Axioms
integrity-before-axioms = z<s

-- Integrity strictly precedes Confidence.
integrity-before-confidence : Integrity < Confidence
integrity-before-confidence = z<s

-- The general statement: for any stage that is not Integrity, Integrity precedes it.
-- We pattern-match: zero would give h refl : ⊥ (absurd); any suc s gives z<s.
integrity-precedes : (s : Stage) → Integrity ≢ s → Integrity < s
integrity-precedes zero    h = ⊥-elim (h refl)
integrity-precedes (suc s) _ = z<s
