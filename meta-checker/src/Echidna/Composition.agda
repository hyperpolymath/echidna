-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
------------------------------------------------------------------------
-- Proof composition soundness and why conflict detection matters (E9)
--
-- Theory, stated for an arbitrary logic: a type of formulae, a type of
-- models and a satisfaction relation are module parameters (not
-- postulates). A proof is the semantic certificate a trusted kernel is
-- assumed to give: every model of its axioms satisfies its goal. The
-- kernel's own soundness is the ASSUMED boundary; this module proves what
-- composing such certificates preserves, and what it does not.
--
--   cut                  composition is sound: if Γ₁ entails φ and φ,Γ₂
--                        entails ψ, then Γ₁,Γ₂ entails ψ. Both premises
--                        are used; neither is ignored.
--   weaken-left/right    adding axioms never breaks an entailment.
--   explosion            an inconsistent axiom set entails everything, so
--                        soundness preservation alone says nothing once the
--                        composed axioms conflict;
--   compose-realised     with a conflict detector that is sound (no reported
--                        conflict ⇒ the joined axioms have a model), the
--                        composite's axioms and goal hold together in some
--                        model: the composition is not vacuously "sound";
--   detector-cannot-miss for any sound detector, "no conflict" is refutable
--                        whenever the joined axioms are inconsistent
--                        (only a double negation, for an arbitrary relation);
--   detector-must-flag   a sound detector that DECIDES its conflict relation
--                        returns a conflict witness, the reportable flag,
--                        whenever the joined axioms are inconsistent;
--   Literals.*           a concrete logic in which pos 0 and neg 0 clash,
--                        and that clash entails an unrelated goal.
--
-- This replaces proofs/agda/SoundnessPreservation.agda as E9's evidence:
-- that file's `compose-sound` discharged a Bool flag with `∧` and never
-- used its conflict hypothesis. No ECHIDNA Rust code composes proofs
-- today, so nothing here verifies an implementation; it states the
-- obligation a future composer and its conflict detector must meet.
--
-- Checked with: agda --safe --without-K --cubical-compatible
-- No postulates.
------------------------------------------------------------------------

module Echidna.Composition where

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- Every element satisfies P (defined here to avoid library-version drift).
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

module Semantics (Form Model : Set) (_⊨_ : Model → Form → Set) where

  Ctx : Set
  Ctx = List Form

  _⊨*_ : Model → Ctx → Set
  M ⊨* Γ = All (M ⊨_) Γ

  -- Semantic entailment: every model of Γ satisfies φ.
  _⊩_ : Ctx → Form → Set
  Γ ⊩ φ = (M : Model) → M ⊨* Γ → M ⊨ φ

  Consistent : Ctx → Set
  Consistent Γ = Σ Model (λ M → M ⊨* Γ)

  ----------------------------------------------------------------------
  -- Splitting and joining satisfaction across _++_
  ----------------------------------------------------------------------

  join : {M : Model} (Γ Δ : Ctx) → M ⊨* Γ → M ⊨* Δ → M ⊨* (Γ ++ Δ)
  join []      Δ []       d = d
  join (_ ∷ Γ) Δ (p ∷ g)  d = p ∷ join Γ Δ g d

  left : {M : Model} (Γ Δ : Ctx) → M ⊨* (Γ ++ Δ) → M ⊨* Γ
  left []      Δ _       = []
  left (_ ∷ Γ) Δ (p ∷ h) = p ∷ left Γ Δ h

  right : {M : Model} (Γ Δ : Ctx) → M ⊨* (Γ ++ Δ) → M ⊨* Δ
  right []      Δ h       = h
  right (_ ∷ Γ) Δ (_ ∷ h) = right Γ Δ h

  ----------------------------------------------------------------------
  -- Composition preserves soundness
  ----------------------------------------------------------------------

  -- A certified proof: axioms, goal, and the kernel's semantic certificate.
  record Proof : Set where
    constructor certified
    field
      axioms : Ctx
      goal   : Form
      sound  : axioms ⊩ goal
  open Proof public

  -- Cut: the second proof uses the first one's goal as a lemma.
  cut : {Γ₁ Γ₂ : Ctx} {φ ψ : Form} → Γ₁ ⊩ φ → (φ ∷ Γ₂) ⊩ ψ → (Γ₁ ++ Γ₂) ⊩ ψ
  cut {Γ₁} {Γ₂} h₁ h₂ M m = h₂ M (h₁ M (left Γ₁ Γ₂ m) ∷ right Γ₁ Γ₂ m)

  compose : (p : Proof) (Γ₂ : Ctx) (ψ : Form) → (goal p ∷ Γ₂) ⊩ ψ → Proof
  compose p Γ₂ ψ h = certified (axioms p ++ Γ₂) ψ (cut (sound p) h)

  weaken-right : {Γ : Ctx} (Δ : Ctx) {φ : Form} → Γ ⊩ φ → (Γ ++ Δ) ⊩ φ
  weaken-right {Γ} Δ h M m = h M (left Γ Δ m)

  weaken-left : (Δ : Ctx) {Γ : Ctx} {φ : Form} → Γ ⊩ φ → (Δ ++ Γ) ⊩ φ
  weaken-left Δ {Γ} h M m = h M (right Δ Γ m)

  ----------------------------------------------------------------------
  -- Why the conflict check is load-bearing
  ----------------------------------------------------------------------

  -- Inconsistent axioms entail every formula: "sound" becomes vacuous.
  explosion : {Γ : Ctx} → ¬ Consistent Γ → (φ : Form) → Γ ⊩ φ
  explosion nc φ M m = ⊥-elim (nc (M , m))

  -- A conflict detector is sound when "no conflict" guarantees a model of
  -- the joined axiom sets.
  SoundDetector : (Ctx → Ctx → Set) → Set
  SoundDetector Conflicts = (Γ Δ : Ctx) → ¬ Conflicts Γ Δ → Consistent (Γ ++ Δ)

  -- With a sound detector and no reported conflict, the composite is
  -- realised: one model satisfies all its axioms and its goal.
  compose-realised : {Conflicts : Ctx → Ctx → Set} → SoundDetector Conflicts
                   → {Γ₁ Γ₂ : Ctx} {φ ψ : Form}
                   → Γ₁ ⊩ φ → (φ ∷ Γ₂) ⊩ ψ → ¬ Conflicts Γ₁ Γ₂
                   → Σ Model (λ M → M ⊨* (Γ₁ ++ Γ₂) × M ⊨ ψ)
  compose-realised det {Γ₁} {Γ₂} h₁ h₂ nc with det Γ₁ Γ₂ nc
  ... | M , m = M , m , cut h₁ h₂ M m

  -- For an arbitrary relation, soundness only refutes "no conflict": a
  -- double negation, not a witness a checker could report.
  detector-cannot-miss : {Conflicts : Ctx → Ctx → Set} → SoundDetector Conflicts
                       → (Γ Δ : Ctx) → ¬ Consistent (Γ ++ Δ) → ¬ ¬ Conflicts Γ Δ
  detector-cannot-miss det Γ Δ inc noc = inc (det Γ Δ noc)

  -- A detector is a decision procedure. A sound one returns the conflict
  -- witness itself for every inconsistent composition: the reportable flag.
  detector-must-flag : {Conflicts : Ctx → Ctx → Set} → SoundDetector Conflicts
                     → ((Γ Δ : Ctx) → Dec (Conflicts Γ Δ))
                     → (Γ Δ : Ctx) → ¬ Consistent (Γ ++ Δ) → Conflicts Γ Δ
  detector-must-flag det decide Γ Δ inc with decide Γ Δ
  ... | yes c  = c
  ... | no  nc = ⊥-elim (inc (det Γ Δ nc))

------------------------------------------------------------------------
-- A concrete logic: literals over a Boolean valuation
------------------------------------------------------------------------

module Literals where

  data Lit : Set where
    pos neg : ℕ → Lit

  _⊨ₗ_ : (ℕ → Bool) → Lit → Set
  v ⊨ₗ pos n = v n ≡ true
  v ⊨ₗ neg n = v n ≡ false

  open Semantics Lit (ℕ → Bool) _⊨ₗ_ public

  true≢false : true ≡ false → ⊥
  true≢false ()

  -- pos 0 and neg 0 have no common model …
  clash : ¬ Consistent (pos 0 ∷ neg 0 ∷ [])
  clash (v , (p ∷ (q ∷ []))) = true≢false (trans (sym p) q)

  -- … so their composition "proves" an unrelated goal.
  clash-entails-anything : (pos 0 ∷ neg 0 ∷ []) ⊩ pos 1
  clash-entails-anything = explosion clash (pos 1)

  -- A genuine composition: from pos 0, and from pos 0 with pos 1, derive
  -- pos 1; the composite's axioms are pos 0, pos 1 and it is realised.
  lemma₁ : (pos 0 ∷ []) ⊩ pos 0
  lemma₁ M (p ∷ []) = p

  lemma₂ : (pos 0 ∷ pos 1 ∷ []) ⊩ pos 1
  lemma₂ M (_ ∷ (q ∷ [])) = q

  composed : (pos 0 ∷ pos 1 ∷ []) ⊩ pos 1
  composed = cut {Γ₁ = pos 0 ∷ []} {Γ₂ = pos 1 ∷ []} {φ = pos 0} {ψ = pos 1} lemma₁ lemma₂
