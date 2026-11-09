-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- TrustRule.agda — a line-for-line model of `compute_trust_level`
-- (src/rust/verification/confidence.rs) and what it guarantees.
--
-- `Echidna.Dispatch.compute-trust` models the same function more coarsely:
-- one flag stands for both "a certificate was produced" and "it was
-- verified", and a cross-check without a certificate yields Level2 there,
-- where the Rust code yields Level3 (`confirming_provers >= 2`).
-- `dispatch-model-diverges` below exhibits that input. This module keeps
-- the two certificate flags and the confirming count apart, as Rust does.
--
-- Proved here, about the model:
--
--   1. guards        — dangerous axioms or a failed integrity check give
--                      Level1, whatever else holds;
--   2. level5-sound  — Level5 implies a small-kernel prover, a verified
--                      certificate, at least two confirming provers, a
--                      passed integrity check and no dangerous axiom;
--   3. compute-mono  — improving any factor never lowers the level;
--   4. two witnesses — Level5 with no certificate produced
--                      (`level5-without-certificate`), and the input on
--                      which `Dispatch.compute-trust` disagrees with the
--                      Rust rule (`dispatch-model-diverges`).
--
-- Not provable here, and recorded as a finding: Level5 is documented as
-- "cross-checked by 2+ independent small-kernel systems", but the Rust
-- factors carry only the PRIMARY prover's kernel and a count of agreeing
-- provers. Nothing in `TrustFactors` says the other provers have small
-- kernels, so the code cannot enforce the documented condition.
--
-- The correspondence between this model and the Rust source is a
-- transcription that no kernel checked: PROOF-POLICY records it as ASSUMED.

module Echidna.TrustRule where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-pred)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echidna.TrustLevel
open import Echidna.AxiomSafety using (DangerClass; DC-Safe)
import Echidna.Dispatch as Dispatch

------------------------------------------------------------------------
-- The factors, as in `TrustFactors` (confidence.rs). `small-kernel` is
-- `is_small_kernel_prover(prover)`; the portfolio field is unused by
-- `compute_trust_level` and is left out.
------------------------------------------------------------------------

record Factors : Set where
  field
    small-kernel         : Bool
    confirming           : ℕ
    has-certificate      : Bool
    certificate-verified : Bool
    danger               : DangerLevel
    integrity-ok         : Bool

open Factors

-- `confirming_provers >= 2`
cross : ℕ → Bool
cross zero          = false
cross (suc zero)    = false
cross (suc (suc _)) = true

-- Warning and Reject both force Level1 in the Rust code.
dangerous : DangerLevel → Bool
dangerous Safe    = false
dangerous Noted   = false
dangerous Warning = true
dangerous Reject  = true

-- The four rules after the guards, in the Rust order (first match wins):
--   L5: cross ∧ verified ∧ small-kernel;  L4: small-kernel ∧ verified;
--   L3: has ∧ verified;  L3: cross;  otherwise L2.
rule : (sk cc hc cv : Bool) → TrustLevel
rule sk cc hc cv =
  if cc ∧ cv ∧ sk then Level5 else
  if sk ∧ cv      then Level4 else
  if hc ∧ cv      then Level3 else
  if cc           then Level3 else Level2

bad : Factors → Bool
bad f = dangerous (danger f) ∨ not (integrity-ok f)

compute : Factors → TrustLevel
compute f = if bad f then Level1
            else rule (small-kernel f) (cross (confirming f))
                      (has-certificate f) (certificate-verified f)

------------------------------------------------------------------------
-- 1. Guards
------------------------------------------------------------------------

dangerous-gives-level1 : ∀ f → dangerous (danger f) ≡ true → compute f ≡ Level1
dangerous-gives-level1 f p with dangerous (danger f)
... | true = refl

integrity-failure-gives-level1 : ∀ f → integrity-ok f ≡ false → compute f ≡ Level1
integrity-failure-gives-level1 f p with dangerous (danger f) | integrity-ok f
... | true  | _     = refl
... | false | false = refl

------------------------------------------------------------------------
-- 2. What Level5 requires
------------------------------------------------------------------------

cross-sound : ∀ n → cross n ≡ true → 2 ≤ n
-- Only absurd patterns touch the equality proof: no constructor-injectivity
-- match, so no UnsupportedIndexedMatch warning under --cubical-compatible.
cross-sound zero          ()
cross-sound (suc zero)    ()
cross-sound (suc (suc n)) _ = s≤s (s≤s z≤n)

-- Of the four rules, only the first yields Level5.
rule-level5 : ∀ sk cc hc cv → rule sk cc hc cv ≡ Level5 →
  sk ≡ true × cc ≡ true × cv ≡ true
rule-level5 true  true  _     true  _  = refl , refl , refl
rule-level5 true  true  true  false ()
rule-level5 true  true  false false ()
rule-level5 true  false _     true  ()
rule-level5 true  false true  false ()
rule-level5 true  false false false ()
rule-level5 false true  true  true  ()
rule-level5 false true  false true  ()
rule-level5 false true  true  false ()
rule-level5 false true  false false ()
rule-level5 false false true  true  ()
rule-level5 false false false true  ()
rule-level5 false false true  false ()
rule-level5 false false false false ()

level5-sound : ∀ f → compute f ≡ Level5 →
  small-kernel f ≡ true × certificate-verified f ≡ true ×
  2 ≤ confirming f × integrity-ok f ≡ true × dangerous (danger f) ≡ false
level5-sound f p with dangerous (danger f) in ed | integrity-ok f in ei
level5-sound f () | true  | _
level5-sound f () | false | false
level5-sound f p  | false | true
  with rule-level5 (small-kernel f) (cross (confirming f))
                   (has-certificate f) (certificate-verified f) p
... | sk , cc , cv = sk , cv , cross-sound (confirming f) cc , refl , refl

------------------------------------------------------------------------
-- 3. Monotonicity
------------------------------------------------------------------------

-- false ≤ true on Bool
data _≤B_ : Bool → Bool → Set where
  f≤f : false ≤B false
  f≤t : false ≤B true
  t≤t : true  ≤B true

cross-mono : ∀ {m n} → m ≤ n → cross m ≤B cross n
-- As in cross-sound, the order proof is matched only in absurd clauses.
cross-mono {zero}        {zero}        _ = f≤f
cross-mono {zero}        {suc zero}    _ = f≤f
cross-mono {zero}        {suc (suc _)} _ = f≤t
cross-mono {suc zero}    {zero}        ()
cross-mono {suc zero}    {suc zero}    _ = f≤f
cross-mono {suc zero}    {suc (suc _)} _ = f≤t
cross-mono {suc (suc _)} {zero}        ()
cross-mono {suc (suc _)} {suc zero}    p with ≤-pred p
... | ()
cross-mono {suc (suc _)} {suc (suc _)} _ = t≤t

-- rule with the varying argument first, so each lemma below is one table
rule-at-sk rule-at-cc rule-at-hc rule-at-cv : Bool → Bool → Bool → Bool → TrustLevel
rule-at-sk x a b c = rule x a b c
rule-at-cc x a b c = rule a x b c
rule-at-hc x a b c = rule a b x c
rule-at-cv x a b c = rule a b c x

-- rule is monotone in sk (false ≤ true), the other three fixed.
rule-mono-sk : ∀ a b c → rule-at-sk false a b c ≤ₜ rule-at-sk true a b c
rule-mono-sk false false false = ≤ₜ-refl Level2
rule-mono-sk false false true  = l2≤4
rule-mono-sk false true  false = ≤ₜ-refl Level2
rule-mono-sk false true  true  = l3≤4
rule-mono-sk true  false false = ≤ₜ-refl Level3
rule-mono-sk true  false true  = l3≤5
rule-mono-sk true  true  false = ≤ₜ-refl Level3
rule-mono-sk true  true  true  = l3≤5

-- rule is monotone in cc (false ≤ true), the other three fixed.
rule-mono-cc : ∀ a b c → rule-at-cc false a b c ≤ₜ rule-at-cc true a b c
rule-mono-cc false false false = l2≤3
rule-mono-cc false false true  = l2≤3
rule-mono-cc false true  false = l2≤3
rule-mono-cc false true  true  = ≤ₜ-refl Level3
rule-mono-cc true  false false = l2≤3
rule-mono-cc true  false true  = l4≤5
rule-mono-cc true  true  false = l2≤3
rule-mono-cc true  true  true  = l4≤5

-- rule is monotone in hc (false ≤ true), the other three fixed.
rule-mono-hc : ∀ a b c → rule-at-hc false a b c ≤ₜ rule-at-hc true a b c
rule-mono-hc false false false = ≤ₜ-refl Level2
rule-mono-hc false false true  = l2≤3
rule-mono-hc false true  false = ≤ₜ-refl Level3
rule-mono-hc false true  true  = ≤ₜ-refl Level3
rule-mono-hc true  false false = ≤ₜ-refl Level2
rule-mono-hc true  false true  = ≤ₜ-refl Level4
rule-mono-hc true  true  false = ≤ₜ-refl Level3
rule-mono-hc true  true  true  = ≤ₜ-refl Level5

-- rule is monotone in cv (false ≤ true), the other three fixed.
rule-mono-cv : ∀ a b c → rule-at-cv false a b c ≤ₜ rule-at-cv true a b c
rule-mono-cv false false false = ≤ₜ-refl Level2
rule-mono-cv false false true  = l2≤3
rule-mono-cv false true  false = ≤ₜ-refl Level3
rule-mono-cv false true  true  = ≤ₜ-refl Level3
rule-mono-cv true  false false = l2≤4
rule-mono-cv true  false true  = l2≤4
rule-mono-cv true  true  false = l3≤5
rule-mono-cv true  true  true  = l3≤5

rule-mono : ∀ {sk sk′ cc cc′ hc hc′ cv cv′} →
  sk ≤B sk′ → cc ≤B cc′ → hc ≤B hc′ → cv ≤B cv′ →
  rule sk cc hc cv ≤ₜ rule sk′ cc′ hc′ cv′
rule-mono {sk} {sk′} {cc} {cc′} {hc} {hc′} {cv} {cv′} psk pcc phc pcv =
  ≤ₜ-trans (step-sk psk) (≤ₜ-trans (step-cc pcc) (≤ₜ-trans (step-hc phc) (step-cv pcv)))
  where
  step-sk : sk ≤B sk′ → rule sk cc hc cv ≤ₜ rule sk′ cc hc cv
  step-sk f≤f = ≤ₜ-refl _
  step-sk f≤t = rule-mono-sk cc hc cv
  step-sk t≤t = ≤ₜ-refl _
  step-cc : cc ≤B cc′ → rule sk′ cc hc cv ≤ₜ rule sk′ cc′ hc cv
  step-cc f≤f = ≤ₜ-refl _
  step-cc f≤t = rule-mono-cc sk′ hc cv
  step-cc t≤t = ≤ₜ-refl _
  step-hc : hc ≤B hc′ → rule sk′ cc′ hc cv ≤ₜ rule sk′ cc′ hc′ cv
  step-hc f≤f = ≤ₜ-refl _
  step-hc f≤t = rule-mono-hc sk′ cc′ cv
  step-hc t≤t = ≤ₜ-refl _
  step-cv : cv ≤B cv′ → rule sk′ cc′ hc′ cv ≤ₜ rule sk′ cc′ hc′ cv′
  step-cv f≤f = ≤ₜ-refl _
  step-cv f≤t = rule-mono-cv sk′ cc′ hc′
  step-cv t≤t = ≤ₜ-refl _

-- g is at least as good as f in every factor: no worse axioms, and every
-- flag and the confirming count at least as high.
record _⊑_ (f g : Factors) : Set where
  field
    sk-≤   : small-kernel f ≤B small-kernel g
    conf-≤ : confirming f ≤ confirming g
    hc-≤   : has-certificate f ≤B has-certificate g
    cv-≤   : certificate-verified f ≤B certificate-verified g
    io-≤   : integrity-ok f ≤B integrity-ok g
    dg-≤   : dangerous (danger g) ≤B dangerous (danger f)

-- If g fails a guard, so does f (it is no better on either guard factor).
bad-anti : ∀ {f g} → f ⊑ g → bad g ≡ true → bad f ≡ true
bad-anti {f} {g} le p with dangerous (danger f) | dangerous (danger g)
                         | integrity-ok f | integrity-ok g
                         | _⊑_.dg-≤ le | _⊑_.io-≤ le
... | true  | _     | _     | _     | _   | _   = refl
... | false | true  | _     | _     | ()  | _
... | false | false | false | _     | _   | _   = refl
... | false | false | true  | false | _   | ()
... | false | false | true  | true  | _   | _   with p
...   | ()

compute-mono : ∀ {f g} → f ⊑ g → compute f ≤ₜ compute g
compute-mono {f} {g} le with bad f in ef | bad g in eg
... | true  | _     = l1≤
... | false | true  with bad-anti le eg
...   | bf rewrite ef with bf
...     | ()
compute-mono {f} {g} le | false | false =
  rule-mono (_⊑_.sk-≤ le) (cross-mono (_⊑_.conf-≤ le)) (_⊑_.hc-≤ le) (_⊑_.cv-≤ le)

------------------------------------------------------------------------
-- 4. Witnesses
------------------------------------------------------------------------

-- Level5 is reached with no certificate produced: the Level5 and Level4
-- rules test `certificate_verified` but not `has_certificate`.
level5-without-certificate :
  compute record { small-kernel = true ; confirming = 2 ; has-certificate = false
                 ; certificate-verified = true ; danger = Safe ; integrity-ok = true }
    ≡ Level5
level5-without-certificate = refl

-- A cross-check by two provers with no certificate: the Rust rule gives
-- Level3; Dispatch.compute-trust gives Level2 for the same situation.
dispatch-model-diverges :
  compute record { small-kernel = false ; confirming = 2 ; has-certificate = false
                 ; certificate-verified = false ; danger = Safe ; integrity-ok = true }
    ≡ Level3
  × Dispatch.compute-trust
      record { integrity-ok = true ; has-certificate = false ; small-kernel = false
             ; axiom-danger = DC-Safe ; cross-checked = true }
    ≡ Level2
dispatch-model-diverges = refl , refl
