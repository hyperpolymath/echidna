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
-- from one in which it is not.  A second, sharpened frame admits a
-- receipt.  This is a comparison of models: no runtime check or
-- transition between those frames is implemented or verified here.
--
-- Checked with: agda --safe --without-K --cubical-compatible
-- No postulates.  The token interpretation takes an explicit family of
-- named assumptions; a conditional receipt requires the corresponding
-- assumption before it can be discharged.  The theorems below prove
-- properties of this model, not the admission of external evidence.
------------------------------------------------------------------------

module Echidna.Receipt where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

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
-- same kind cannot produce one within this frame.
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
-- changes: the agent can now tell them apart.  The receipt is inhabited
-- in this frame; proving that a real check justifies this change is a
-- separate obligation outside this model.
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
-- frames: accessibility changed, while factivity still holds.
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

-- The applicable frame is part of a receipt's type.  Keeping the coarse
-- countermodel does not make successful assertions in the sharpened
-- frame impossible.
data Frame : Set where
  coarse sharpened : Frame

Accessible : Frame → World → World → Set
Accessible coarse    = _≈_
Accessible sharpened = _≈′_

FrameReceipt : Frame → Atom → World → Set
FrameReceipt coarse    = Receipt
FrameReceipt sharpened = Receipt′

frame-receipt-factive :
  ∀ {frame φ w} → FrameReceipt frame φ w → ⟦ φ ⟧ w
frame-receipt-factive {coarse}    = receipt-factive
frame-receipt-factive {sharpened} = receipt′-factive

FrameWarrant : Frame → Atom → World → Set
FrameWarrant frame φ w =
  Σ[ e ∈ Evidence φ ] (Accessible frame w (grounds e)) × ⟦ φ ⟧ (grounds e)

-- A bounded check has a nonempty, explicitly enumerated population and
-- a result for every sample.  This is semantic test evidence in the
-- model, not an attestation that an external test runner executed.
-- Its results establish the claim only at the sampled worlds.
record TestEvidence (φ : Atom) : Set where
  constructor checked-samples
  field
    extra-samples : ℕ
    samples       : Vec World (suc extra-samples)
    passed        : All (λ w → ⟦ φ ⟧ w) samples

one-passing-sample : TestEvidence sound
one-passing-sample = checked-samples zero (w-here ∷ []) (tt ∷ [])

-- A false sample cannot be hidden inside an all-passing result.
false-sample-rejected :
  ∀ {n} {rest : Vec World n} →
  All (λ w → ⟦ sound ⟧ w) (w-there ∷ rest) → ⊥
false-sample-rejected (() ∷ _)

-- These are names, not proofs of the named axioms.  The interpretation
-- `assumptions` is supplied explicitly at the boundary.  A postulated
-- assertion stores a function from that proposition to a receipt, not
-- an unconditional receipt paired with an inert label.
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

Asserts : (Axiom → Set) → Frame → Verdict → (φ : Atom) → World → Set
Asserts assumptions frame proven                 φ w = FrameReceipt frame φ w
Asserts assumptions frame proven-with-postulates φ w =
  Σ[ ax ∈ Axiom ] (assumptions ax → FrameReceipt frame φ w)
Asserts assumptions frame tested-only            φ w = TestEvidence φ
Asserts assumptions frame argued                 φ w = FrameWarrant frame φ w
Asserts assumptions frame no-claim               φ w = ⊤

postulates-name-an-axiom :
  ∀ {assumptions frame φ w} →
  Asserts assumptions frame proven-with-postulates φ w → Axiom
postulates-name-an-axiom = proj₁

discharge-postulates :
  ∀ {assumptions frame φ w}
  (claim : Asserts assumptions frame proven-with-postulates φ w) →
  assumptions (proj₁ claim) → Asserts assumptions frame proven φ w
discharge-postulates claim premise = proj₂ claim premise

-- A positive control: the stronger token is inhabited in the sharpened
-- frame.  Warrant and receipt may coexist; the theorem below rejects a
-- uniform conversion, not the coexistence of the two kinds of evidence.
proven-in-sharpened-frame :
  ∀ {assumptions} → Asserts assumptions sharpened proven sound w-here
proven-in-sharpened-frame = receipt-in-sharpened-frame

warrant-and-receipt :
  ∀ {assumptions} →
  Asserts assumptions sharpened argued sound w-here ×
  Asserts assumptions sharpened proven sound w-here
warrant-and-receipt =
  (ev-sound , ≈′-here , tt) , receipt-in-sharpened-frame

-- No operation may promote every warrant in every frame.  The coarse
-- false-world witness refutes such an operation without making the
-- sharpened positive control impossible.
no-free-promotion :
  ∀ {assumptions} →
  (∀ {frame φ w} → Asserts assumptions frame argued φ w →
                    Asserts assumptions frame proven φ w) → ⊥
no-free-promotion promote =
  promote {coarse} {sound} {w-there} warrant-elsewhere ≈-there

-- The opaque names do not supply their interpretations.  In particular,
-- an implication from an unavailable premise cannot be projected into
-- an unconditional receipt.  This countermodel does not assert that
-- any actual mathematical axiom is false.
no-unconditional-postulate-promotion :
  (∀ {assumptions frame φ w} →
    Asserts assumptions frame proven-with-postulates φ w →
    Asserts assumptions frame proven φ w) → ⊥
no-unconditional-postulate-promotion promote =
  promote {λ _ → ⊥} {sharpened} {sound} {w-there}
    (em , λ impossible → ⊥-elim impossible) ≈′-there

-- A sample at w-here can pass while the unsampled w-there is false.
-- Explicit bounds prevent a tested-only claim from becoming universal.
no-test-promotion :
  ∀ {assumptions} →
  (∀ {frame φ w} → Asserts assumptions frame tested-only φ w →
                    Asserts assumptions frame proven φ w) → ⊥
no-test-promotion promote =
  promote {sharpened} {sound} {w-there} one-passing-sample ≈′-there
