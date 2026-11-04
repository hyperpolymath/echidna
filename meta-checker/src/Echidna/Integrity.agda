-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
------------------------------------------------------------------------
-- Solver Integrity — semantic rewrite of obligation E11
--
-- The current repository has an informal note for E11 and no Agda
-- record.  This module states the invariant that the integrity checker
-- is *supposed* to guarantee, and then proves the sharpness result
-- that makes the digest-comparison soundness hypothesis load-bearing rather
-- than decorative.
--
-- The model's headline theorem says an UNINITIALISED manifest never
-- yields `Verified`.
-- src/rust/dispatch.rs:642,848,998 and
-- src/rust/integrity/solver_integrity.rs:359 all accept
-- `IntegrityStatus::Uninitialized` as permitting dispatch.  Rust does not
-- report `Verified` in that case.  The model has no dispatch-permission
-- decision: DEBT D9 is a source comparison with this specification, not
-- a machine-checked refinement theorem about the Rust implementation.
--
-- Scope: a binary is modelled by its digest only, so "substituted" below
-- means "a binary whose digest differs".  `≈d-sound` requires an accepted
-- comparison to imply equal digests.  There are no binary contents or
-- hashing function in the model, so content-level collision resistance
-- is outside its scope.  Equal-digest substitutions remain indistinguishable.
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
-- Digest-comparison soundness, carried as a record field
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

  -- Check a binary against the recorded digest using the supplied comparator.
  -- An uninitialised manifest yields `Missing`; otherwise a true comparison
  -- yields `Verified` and a false comparison yields `Mismatch`.
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

  -- E11c. A binary with a different digest is never verified.
  substituted-never-verified :
    ∀ {d b} → ¬ (digest b ≡ d) → ¬ (check (Initialised d) b ≡ Verified)
  substituted-never-verified {d} {b} neq p =
    neq (sym (verified-means-match {d} {b} p))

  -- E11d. An uninitialised manifest never yields `Verified` in this model.
  -- Dispatch permission in Rust is a separate, unverified property (D9).
  uninitialised-never-verified :
    ∀ b → ¬ (check Uninitialised b ≡ Verified)
  uninitialised-never-verified b ()

------------------------------------------------------------------------
-- Sharpness: the assumption is load-bearing
--
-- An accept-everything comparator accepts distinct digests.  Its
-- soundness property is explicitly refuted below; therefore it cannot
-- supply the `≈d-sound` field required by `Hash` and E11b.  No `check`
-- function over UnsoundHash, or binary-content theorem, is claimed here.
------------------------------------------------------------------------

record UnsoundHash : Set₁ where
  field
    Digest : Set
    _≈d_   : Digest → Digest → Bool

-- A comparator that accepts everything: digest-comparison soundness fails.
always-true : UnsoundHash
UnsoundHash.Digest always-true = Bool
UnsoundHash._≈d_   always-true _ _ = true

-- The digests of two distinct binaries are declared equal...
sharpness : UnsoundHash._≈d_ always-true true false ≡ true
sharpness = refl

-- ...while they demonstrably are not.
sharpness-matters : ¬ (true ≡ false)
sharpness-matters ()

-- Refute precisely the property required by Hash, not merely Bool
-- inequality: any proposed soundness witness makes true equal false.
sharpness-blocks-soundness :
  ¬ (∀ {d e : Bool} →
       UnsoundHash._≈d_ always-true d e ≡ true → d ≡ e)
sharpness-blocks-soundness sound-comparison =
  sharpness-matters (sound-comparison {true} {false} refl)
