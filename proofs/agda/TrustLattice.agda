-- SPDX-License-Identifier: AGPL-3.0-or-later
-- TrustLattice.agda — bounded poset on TrustLevel (5-element type).
--
-- Models the ECHIDNA trust hierarchy as an ordered type and proves the
-- four poset laws:  reflexivity, antisymmetry, transitivity, and that
-- Level1 (lowest) is bottom and Level5 (highest) is top.
--
-- TrustLevel is defined inductively here rather than as Fin 5 so that
-- the constructors carry the domain names from dispatch.rs.

module TrustLattice where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)
open import Data.Empty using (⊥; ⊥-elim)

------------------------------------------------------------------------
-- 1.  The TrustLevel type (5 levels, ordered low → high)
------------------------------------------------------------------------

data TrustLevel : Set where
  Level1 : TrustLevel   -- untrusted / minimal
  Level2 : TrustLevel
  Level3 : TrustLevel
  Level4 : TrustLevel
  Level5 : TrustLevel   -- fully verified / maximum trust

------------------------------------------------------------------------
-- 2.  Order relation  _≤ᵀ_
--     Defined as a data type so Agda can check coverage exhaustively.
------------------------------------------------------------------------

data _≤ᵀ_ : TrustLevel → TrustLevel → Set where
  ≤ᵀ-11 : Level1 ≤ᵀ Level1
  ≤ᵀ-12 : Level1 ≤ᵀ Level2
  ≤ᵀ-13 : Level1 ≤ᵀ Level3
  ≤ᵀ-14 : Level1 ≤ᵀ Level4
  ≤ᵀ-15 : Level1 ≤ᵀ Level5
  ≤ᵀ-22 : Level2 ≤ᵀ Level2
  ≤ᵀ-23 : Level2 ≤ᵀ Level3
  ≤ᵀ-24 : Level2 ≤ᵀ Level4
  ≤ᵀ-25 : Level2 ≤ᵀ Level5
  ≤ᵀ-33 : Level3 ≤ᵀ Level3
  ≤ᵀ-34 : Level3 ≤ᵀ Level4
  ≤ᵀ-35 : Level3 ≤ᵀ Level5
  ≤ᵀ-44 : Level4 ≤ᵀ Level4
  ≤ᵀ-45 : Level4 ≤ᵀ Level5
  ≤ᵀ-55 : Level5 ≤ᵀ Level5

infix 4 _≤ᵀ_

------------------------------------------------------------------------
-- 3.  Reflexivity
------------------------------------------------------------------------

-- Every trust level is at least as trusted as itself.
≤ᵀ-refl : (a : TrustLevel) → a ≤ᵀ a
≤ᵀ-refl Level1 = ≤ᵀ-11
≤ᵀ-refl Level2 = ≤ᵀ-22
≤ᵀ-refl Level3 = ≤ᵀ-33
≤ᵀ-refl Level4 = ≤ᵀ-44
≤ᵀ-refl Level5 = ≤ᵀ-55

------------------------------------------------------------------------
-- 4.  Antisymmetry
------------------------------------------------------------------------

-- If a ≤ b and b ≤ a then a and b are the same level.
≤ᵀ-antisym : {a b : TrustLevel} → a ≤ᵀ b → b ≤ᵀ a → a ≡ b
≤ᵀ-antisym ≤ᵀ-11 ≤ᵀ-11 = refl
≤ᵀ-antisym ≤ᵀ-22 ≤ᵀ-22 = refl
≤ᵀ-antisym ≤ᵀ-33 ≤ᵀ-33 = refl
≤ᵀ-antisym ≤ᵀ-44 ≤ᵀ-44 = refl
≤ᵀ-antisym ≤ᵀ-55 ≤ᵀ-55 = refl
-- All cross-level cases are impossible: if i < j then j ≤ i has no constructor.
≤ᵀ-antisym ≤ᵀ-12 ()
≤ᵀ-antisym ≤ᵀ-13 ()
≤ᵀ-antisym ≤ᵀ-14 ()
≤ᵀ-antisym ≤ᵀ-15 ()
≤ᵀ-antisym ≤ᵀ-23 ()
≤ᵀ-antisym ≤ᵀ-24 ()
≤ᵀ-antisym ≤ᵀ-25 ()
≤ᵀ-antisym ≤ᵀ-34 ()
≤ᵀ-antisym ≤ᵀ-35 ()
≤ᵀ-antisym ≤ᵀ-45 ()

------------------------------------------------------------------------
-- 5.  Transitivity
------------------------------------------------------------------------

-- Ordering is transitive: a ≤ b → b ≤ c → a ≤ c.
≤ᵀ-trans : {a b c : TrustLevel} → a ≤ᵀ b → b ≤ᵀ c → a ≤ᵀ c
≤ᵀ-trans ≤ᵀ-11 p       = p
≤ᵀ-trans ≤ᵀ-12 ≤ᵀ-22   = ≤ᵀ-12
≤ᵀ-trans ≤ᵀ-12 ≤ᵀ-23   = ≤ᵀ-13
≤ᵀ-trans ≤ᵀ-12 ≤ᵀ-24   = ≤ᵀ-14
≤ᵀ-trans ≤ᵀ-12 ≤ᵀ-25   = ≤ᵀ-15
≤ᵀ-trans ≤ᵀ-13 ≤ᵀ-33   = ≤ᵀ-13
≤ᵀ-trans ≤ᵀ-13 ≤ᵀ-34   = ≤ᵀ-14
≤ᵀ-trans ≤ᵀ-13 ≤ᵀ-35   = ≤ᵀ-15
≤ᵀ-trans ≤ᵀ-14 ≤ᵀ-44   = ≤ᵀ-14
≤ᵀ-trans ≤ᵀ-14 ≤ᵀ-45   = ≤ᵀ-15
≤ᵀ-trans ≤ᵀ-15 ≤ᵀ-55   = ≤ᵀ-15
≤ᵀ-trans ≤ᵀ-22 p       = p
≤ᵀ-trans ≤ᵀ-23 ≤ᵀ-33   = ≤ᵀ-23
≤ᵀ-trans ≤ᵀ-23 ≤ᵀ-34   = ≤ᵀ-24
≤ᵀ-trans ≤ᵀ-23 ≤ᵀ-35   = ≤ᵀ-25
≤ᵀ-trans ≤ᵀ-24 ≤ᵀ-44   = ≤ᵀ-24
≤ᵀ-trans ≤ᵀ-24 ≤ᵀ-45   = ≤ᵀ-25
≤ᵀ-trans ≤ᵀ-25 ≤ᵀ-55   = ≤ᵀ-25
≤ᵀ-trans ≤ᵀ-33 p       = p
≤ᵀ-trans ≤ᵀ-34 ≤ᵀ-44   = ≤ᵀ-34
≤ᵀ-trans ≤ᵀ-34 ≤ᵀ-45   = ≤ᵀ-35
≤ᵀ-trans ≤ᵀ-35 ≤ᵀ-55   = ≤ᵀ-35
≤ᵀ-trans ≤ᵀ-44 p       = p
≤ᵀ-trans ≤ᵀ-45 ≤ᵀ-55   = ≤ᵀ-45
≤ᵀ-trans ≤ᵀ-55 ≤ᵀ-55   = ≤ᵀ-55

------------------------------------------------------------------------
-- 6.  Bounded poset: bottom and top
------------------------------------------------------------------------

-- Level1 is the bottom element: every level is at least Level1.
Level1-bottom : (a : TrustLevel) → Level1 ≤ᵀ a
Level1-bottom Level1 = ≤ᵀ-11
Level1-bottom Level2 = ≤ᵀ-12
Level1-bottom Level3 = ≤ᵀ-13
Level1-bottom Level4 = ≤ᵀ-14
Level1-bottom Level5 = ≤ᵀ-15

-- Level5 is the top element: every level is at most Level5.
Level5-top : (a : TrustLevel) → a ≤ᵀ Level5
Level5-top Level1 = ≤ᵀ-15
Level5-top Level2 = ≤ᵀ-25
Level5-top Level3 = ≤ᵀ-35
Level5-top Level4 = ≤ᵀ-45
Level5-top Level5 = ≤ᵀ-55
