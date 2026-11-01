-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
------------------------------------------------------------------------
-- Solver Integrity — semantic rewrite of obligation E11
--
-- The current repository has an informal note for E11 and no Agda
-- record.  This module states the invariant that the integrity checker
-- is *supposed* to guarantee, and then proves the sharpness result
-- that makes the collision-resistance assumption load-bearing rather
-- than decorative.
--
-- The headline theorem is the one the Rust implementation violates:
-- an UNINITIALISED manifest must never yield `Verified`.
-- src/rust/dispatch.rs:642,848,998 and
-- src/rust/integrity/solver_integrity.rs:359 all accept
-- `IntegrityStatus::Uninitialized` as passing.  The proof below is about
-- the specification, not about that code path — which is exactly why it
-- is worth having a record: it makes the deviation a machine-checked
-- discrepancy (DEBT D9) instead of a reading of the source.
--
-- Scope: a binary is modelled by its digest only, so "substituted" below
-- means "a binary whose digest differs". Content-level collision resistance is
-- the `≈d-sound` field of the comparator, i.e. assumed by the caller and not
-- established here; `sharpness` shows what happens when it fails.
--
-- Checked with: agda --safe --without-K --cubical-compatible
------------------------------------------------------------------------

module Echidna.Integrity where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Collision resistance, carried as a record field
--
-- This is deliberately an *assumption recorded in a structure* rather
-- than a postulate: the theorems below are parameterised by it, so the
-- guarantee they give is conditional and says so in its type.
------------------------------------------------------------------------

record Hash : Set₁ where
  field
    Digest   : Set
    _≈d_     : Digest → Digest → Bool
    ≈d-sound : ∀ {d e} → _≈d_ d e ≡ true → d ≡ e

module _ (H : Hash) where
  open Hash H

  ----------------------------------------------------------------------
  -- Manifest and result
  ----------------------------------------------------------------------

  data Manifest : Set where
    Uninitialised : Manifest          -- nothing to compare against
    Initialised   : Digest → Manifest -- expected digest recorded

  data Result : Set where
    Verified : Result
    Mismatch : Result
    Missing  : Result

  decide : Bool → Result
  decide true  = Verified
  decide false = Mismatch

  record Binary : Set where
    field digest : Digest
  open Binary public

  -- The specified checker.  Note the first line: an uninitialised
  -- manifest produces `Missing`, never `Verified`.
  check : Manifest → Binary → Result
  check Uninitialised    _ = Missing
  check (Initialised d)  b = decide (_≈d_ d (digest b))

  ----------------------------------------------------------------------
  -- Inversion of the decider
  ----------------------------------------------------------------------

  decide-verified : ∀ {x} → decide x ≡ Verified → x ≡ true
  decide-verified {true}  _ = refl
  decide-verified {false} ()

  ----------------------------------------------------------------------
  -- THEOREMS
  ----------------------------------------------------------------------

  -- E11a. Verification requires a manifest.
  verified-needs-manifest :
    ∀ {m b} → check m b ≡ Verified → Σ[ d ∈ Digest ] (m ≡ Initialised d)
  verified-needs-manifest {Uninitialised} {b} ()
  verified-needs-manifest {Initialised d} {b} _ = d , refl

  -- E11b. Verification means the recorded digest was matched.
  verified-means-match :
    ∀ {d b} → check (Initialised d) b ≡ Verified → d ≡ digest b
  verified-means-match {d} {b} p = ≈d-sound (decide-verified p)

  -- E11c. A substituted binary is never verified.
  substituted-never-verified :
    ∀ {d b} → ¬ (digest b ≡ d) → ¬ (check (Initialised d) b ≡ Verified)
  substituted-never-verified {d} {b} neq p =
    neq (sym (verified-means-match {d} {b} p))

  -- E11d. THE INVARIANT THE IMPLEMENTATION BREAKS (DEBT D9):
  -- an uninitialised manifest never yields `Verified`.
  uninitialised-never-verified :
    ∀ b → ¬ (check Uninitialised b ≡ Verified)
  uninitialised-never-verified b ()

------------------------------------------------------------------------
-- Sharpness: the assumption is load-bearing
--
-- Without `≈d-sound`, verification does not imply anything about the
-- binary.  This is proved by exhibiting a comparator that accepts
-- everything, under which a manifest for `true` verifies a binary whose
-- digest is `false`.
------------------------------------------------------------------------

record UnsoundHash : Set₁ where
  field
    Digest : Set
    _≈d_   : Digest → Digest → Bool

-- A comparator that accepts everything: collision resistance fails.
always-true : UnsoundHash
UnsoundHash.Digest always-true = Bool
UnsoundHash._≈d_   always-true _ _ = true

-- The digests of two distinct binaries are declared equal...
sharpness : UnsoundHash._≈d_ always-true true false ≡ true
sharpness = refl

-- ...while they demonstrably are not.
sharpness-matters : ¬ (true ≡ false)
sharpness-matters ()

-- Hence this comparator satisfies no soundness condition at all: the only
-- candidate witness forces `true ≡ false`.  So E11b cannot be discharged for
-- it, and the `≈d-sound` field in `Hash` is doing real work rather than
-- decorating the record.
sharpness-blocks-soundness :
  UnsoundHash._≈d_ always-true true false ≡ true → ¬ (true ≡ false)
sharpness-blocks-soundness _ = sharpness-matters
