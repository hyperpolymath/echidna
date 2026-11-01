-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
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
-- (no postulates and no hypotheses: every result here is unconditional,
--  including the sharpened frame, which is a second model rather than an
--  assumption added to the first)
------------------------------------------------------------------------

module Echidna.Receipt where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
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
-- The sharpened frame: excluding the alternative is what buys a receipt
--
-- Crucially this is a *second model*, not a hypothesis bolted onto the
-- first.  A function `w-here ≈ w-there → ⊥` cannot exist in the coarse
-- frame — `≈-cross` inhabits its domain — so taking one as a parameter
-- would be vacuous, and would say nothing about what a receipt is.  Here
-- the same two worlds keep their identity and only the accessibility
-- changes: the agent can now tell them apart.  That is what a
-- discriminating check buys, and unlike the impossible hypothesis it is
-- inhabited.
------------------------------------------------------------------------

data _≈′_ : World → World → Set where
  ≈′-here  : w-here  ≈′ w-here
  ≈′-there : w-there ≈′ w-there

≈′-refl : ∀ w → w ≈′ w
≈′-refl w-here  = ≈′-here
≈′-refl w-there = ≈′-there

Receipt′ : Atom → World → Set
Receipt′ φ w = ∀ {w′} → w ≈′ w′ → ⟦ φ ⟧ w′

-- A receipt exists in this frame...
receipt-in-sharpened-frame : Receipt′ sound w-here
receipt-in-sharpened-frame {w-here}  _ = tt
receipt-in-sharpened-frame {w-there} ()

-- ...and it is still factive, so the token means the same thing in both
-- frames: what changed is the evidence, not the standard of proof.
receipt′-factive : ∀ {φ w} → Receipt′ φ w → ⟦ φ ⟧ w
receipt′-factive r = r (≈′-refl _)

-- THE CONTRAST, and the point of the whole module: identical worlds,
-- identical proposition, no receipt in the coarse frame and a receipt in
-- the sharpened one.  Nothing about the *claim* changed; what changed is
-- whether the alternative world was excluded.
coarse-yet-sharpened :
  (Receipt sound w-here → ⊥) × Receipt′ sound w-here
coarse-yet-sharpened = no-receipt-anywhere w-here , receipt-in-sharpened-frame

------------------------------------------------------------------------
-- Token discipline
--
-- What each PROOF-POLICY §5 token asserts, as a function of the
-- proposition it is about, and the theorem that strengthening a token
-- is not free.
------------------------------------------------------------------------

-- The axioms the policy's PROVEN-WITH-AXIOMS token is *about*.  Naming one
-- is the entire difference between that token and `proven`: asserting the
-- proposition alone would make the two indistinguishable, which is the
-- accounting §5 exists to keep.
data Axiom : Set where
  funext : Axiom
  choice : Axiom
  em     : Axiom

data Verdict : Set where
  proven               : Verdict
  proven-with-postulates : Verdict
  tested-only          : Verdict
  argued               : Verdict
  no-claim             : Verdict   -- the `open` token (`open` is a keyword)

Asserts : Verdict → (φ : Atom) → World → Set
Asserts proven                 φ w = Receipt φ w
Asserts proven-with-postulates φ w = Axiom × Receipt φ w
Asserts tested-only            φ w = Warrant φ w
Asserts argued                 φ w = Warrant φ w
Asserts no-claim               φ w = ⊤

-- A `proven-with-postulates` assertion carries the axiom it rests on; a
-- `proven` assertion carries none, which is why they are different types.
postulates-name-an-axiom :
  ∀ {φ w} → Asserts proven-with-postulates φ w → Axiom
postulates-name-an-axiom = proj₁

-- The same warrant never licences the stronger token.
no-free-promotion :
  ∀ {φ w} → Asserts argued φ w → Asserts proven φ w → ⊥
no-free-promotion {sound} {w-here}  _ r = r ≈-cross
no-free-promotion {sound} {w-there} _ r = r ≈-there
