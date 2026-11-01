------------------------------------------------------------------------
-- Receipt vs Warrant
--
-- Semantic rewrite (not a mechanical port) of the receipt/warrant
-- distinction developed in the strict-safe Agda development at
-- epistemic-types@5422cd5.  There, "warrant" and "receipt" are kept
-- distinct: a warrant is evidence *about* a claim, a receipt is the
-- claim's proof.  This module carries that distinction into ECHIDNA's
-- proof vocabulary, where per PROOF-POLICY §5 only `proven` may assert
-- the proposition and `argued` must not.
--
-- The argument is a two-world Kripke countermodel: an agent holding a
-- warrant cannot distinguish the world in which the verdict is sound
-- from one in which it is not.  A receipt is exactly what closes that
-- gap — a discriminating check, not more of the same evidence.
--
-- Checked with: agda --safe --without-K --cubical-compatible
-- (no postulates, no assumptions; the only hypothesis is the
--  discriminating check in the final section, and it is a parameter)
------------------------------------------------------------------------

module Echidna.Receipt where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Kripke frame
--
-- Two worlds that the agent cannot tell apart.  `w-here` is the world
-- the run actually happened in; `w-there` is an indistinguishable
-- alternative — e.g. the world in which the solver was substituted, or
-- the manifest was uninitialised, and the verdict is unsound.
------------------------------------------------------------------------

data World : Set where
  w-here  : World
  w-there : World

data _≈_ : World → World → Set where
  ≈-here   : w-here  ≈ w-here
  ≈-there  : w-there ≈ w-there
  ≈-cross  : w-here  ≈ w-there
  ≈-cross′ : w-there ≈ w-here

≈-refl : ∀ w → w ≈ w
≈-refl w-here  = ≈-here
≈-refl w-there = ≈-there

------------------------------------------------------------------------
-- One proposition: "the prover's verdict is sound"
------------------------------------------------------------------------

data Atom : Set where
  sound : Atom

⟦_⟧ : Atom → World → Set
⟦ sound ⟧ w-here  = ⊤
⟦ sound ⟧ w-there = ⊥

------------------------------------------------------------------------
-- Receipts: agent-invariant
--
-- A receipt is a proof the agent can carry: it holds at every world the
-- agent cannot rule out.  This is the Kripke reading of "checked".
------------------------------------------------------------------------

Receipt : Atom → World → Set
Receipt φ w = ∀ {w′} → w ≈ w′ → ⟦ φ ⟧ w′

-- A receipt is factive.  This is the property `proven` asserts and
-- `argued` does not.
receipt-factive : ∀ {φ w} → Receipt φ w → ⟦ φ ⟧ w
receipt-factive r = r (≈-refl _)

------------------------------------------------------------------------
-- Warrants: agent-relative
--
-- A warrant is evidence collected somewhere, plus the fact that the
-- agent cannot rule that somewhere out.  It is deliberately *not*
-- indexed by success: it is a claim about the evidence, not about the
-- world.
------------------------------------------------------------------------

data Evidence : Atom → Set where
  ev-sound : Evidence sound        -- e.g. a certificate the prover emitted

-- Where the evidence came from.  The agent hopes it is `w-here`.
grounds : ∀ {φ} → Evidence φ → World
grounds {φ} _ = w-here

Warrant : Atom → World → Set
Warrant φ w = Σ[ e ∈ Evidence φ ] (w ≈ grounds e) × ⟦ φ ⟧ (grounds e)

-- An agent standing at `w-there` holds a warrant for `sound`.
warrant-elsewhere : Warrant sound w-there
warrant-elsewhere = ev-sound , ≈-cross′ , tt

------------------------------------------------------------------------
-- THEOREM (non-factivity): a warrant does not entail its claim
--
-- There is a world in which the agent is warranted in asserting the
-- claim and the claim is false.  So `argued` may never be read as
-- `proven`, however many times the evidence is re-run.
------------------------------------------------------------------------

warrant-not-factive :
  Σ[ w ∈ World ] (Warrant sound w × (⟦ sound ⟧ w → ⊥))
warrant-not-factive = w-there , warrant-elsewhere , λ z → z

------------------------------------------------------------------------
-- THEOREM (no free promotion): a warrant is not a receipt
------------------------------------------------------------------------

warrant-not-receipt : Warrant sound w-there → Receipt sound w-there → ⊥
warrant-not-receipt _ r = r ≈-there

-- Stronger: because the agent cannot exclude `w-there`, no receipt for
-- `sound` exists at *either* world.  Accumulating more evidence of the
-- same kind cannot produce one; only a check that discriminates can.
no-receipt-anywhere : ∀ w → Receipt sound w → ⊥
no-receipt-anywhere w-here  r = r ≈-cross
no-receipt-anywhere w-there r = r ≈-there

------------------------------------------------------------------------
-- Constructive counterpart: a discriminating check yields a receipt
--
-- The hypothesis is a *parameter*, not a postulate: any caller that
-- supplies such a check gets a receipt for free.  In ECHIDNA terms this
-- is an independently checked certificate (Rocq/Lean re-check, or
-- statement comparison across two kernels) — precisely the evidence
-- R5 is missing.
------------------------------------------------------------------------

module _ (discriminates : w-here ≈ w-there → ⊥) where

  receipt-from-check : Receipt sound w-here
  receipt-from-check {w-here}  _ = tt
  receipt-from-check {w-there} r = ⊥-elim (discriminates r)

------------------------------------------------------------------------
-- Token discipline
--
-- What each PROOF-POLICY §5 token asserts, as a function of the
-- proposition it is about, and the theorem that strengthening a token
-- is not free.
------------------------------------------------------------------------

data Verdict : Set where
  proven               : Verdict
  proven-with-postulates : Verdict
  tested-only          : Verdict
  argued               : Verdict
  no-claim             : Verdict   -- the `open` token (`open` is a keyword)

Asserts : Verdict → (φ : Atom) → World → Set
Asserts proven                 φ w = Receipt φ w
Asserts proven-with-postulates φ w = Receipt φ w
Asserts tested-only            φ w = Warrant φ w
Asserts argued                 φ w = Warrant φ w
Asserts no-claim               φ w = ⊤

-- The same warrant never licences the stronger token.
no-free-promotion :
  ∀ {φ w} → Asserts argued φ w → Asserts proven φ w → ⊥
no-free-promotion {sound} {w-here}  _ r = r ≈-cross
no-free-promotion {sound} {w-there} _ r = r ≈-there
