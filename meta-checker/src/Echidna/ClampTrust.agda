------------------------------------------------------------------------
-- Clamp Trust Bounds — semantic rewrite of the Idris2 obligation
--
-- verification/proofs/idris2/ClampTrustBounds.idr states four
-- obligations for `clamp_trust : Nat → TrustLevel`.  That corpus is out
-- of policy per PROOF-POLICY §3 (engineering claims about this
-- repository's own types are Idris2/Agda territory, but the corpus is
-- not wired into any gate and there is no `idris2` binary in CI that
-- runs it).  This module restates the same obligations over the
-- trust-level type that the meta-checker already proves things about,
-- so that they are checked by the gate that actually runs.
--
-- Obligations covered:
--   clamp-lower      : trust-to-ℕ (clamp-trust n) ≥ 1
--   clamp-upper      : trust-to-ℕ (clamp-trust n) ≤ 5
--   clamp-monotone   : n ≤ m → clamp-trust n ≤ₜ clamp-trust m
--   clamp-fixed-1    : clamp-trust 1 ≡ Level1
--   clamp-fixed-5    : clamp-trust 5 ≡ Level5
--   clamp-fixed-10   : clamp-trust 10 ≡ Level5
--   clamp-roundtrip  : the clamp lands on a real level, not between two
--
-- Checked with: agda --safe --without-K --cubical-compatible
------------------------------------------------------------------------

module Echidna.ClampTrust where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Echidna.TrustLevel using
  ( TrustLevel
  ; Level1; Level2; Level3; Level4; Level5
  ; _≤ₜ_; ≤ₜ-refl; ≤ₜ-trans; l1≤; l2≤3; l3≤4; l4≤5; l5≤5
  ; trust-to-ℕ
  )

------------------------------------------------------------------------
-- The clamp, exactly as the Idris2 model defines it
------------------------------------------------------------------------

clamp-trust : ℕ → TrustLevel
clamp-trust zero                                  = Level1
clamp-trust (suc zero)                            = Level1
clamp-trust (suc (suc zero))                      = Level2
clamp-trust (suc (suc (suc zero)))                = Level3
clamp-trust (suc (suc (suc (suc zero))))          = Level4
clamp-trust (suc (suc (suc (suc (suc _)))))       = Level5

------------------------------------------------------------------------
-- Bounds
------------------------------------------------------------------------

clamp-lower : ∀ n → suc zero ≤ trust-to-ℕ (clamp-trust n)
clamp-lower zero                            = s≤s z≤n
clamp-lower (suc zero)                      = s≤s z≤n
clamp-lower (suc (suc zero))                = s≤s z≤n
clamp-lower (suc (suc (suc zero)))          = s≤s z≤n
clamp-lower (suc (suc (suc (suc zero))))    = s≤s z≤n
clamp-lower (suc (suc (suc (suc (suc _))))) = s≤s z≤n

clamp-upper :
  ∀ n → trust-to-ℕ (clamp-trust n) ≤ suc (suc (suc (suc (suc zero))))
clamp-upper zero                            = s≤s z≤n
clamp-upper (suc zero)                      = s≤s z≤n
clamp-upper (suc (suc zero))                = s≤s (s≤s z≤n)
clamp-upper (suc (suc (suc zero)))          = s≤s (s≤s (s≤s z≤n))
clamp-upper (suc (suc (suc (suc zero))))    = s≤s (s≤s (s≤s (s≤s z≤n)))
clamp-upper (suc (suc (suc (suc (suc _))))) = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- Monotonicity
--
-- The clamp is not suc-closed in the trust order, so induction on the
-- `≤` witness does not go through.  Instead: every `n ≤ m` decomposes as
-- `m ≡ k + n`, and the clamp advances by one `clamp-step` per successor.
------------------------------------------------------------------------

-- One step never decreases trust.
clamp-step : ∀ n → clamp-trust n ≤ₜ clamp-trust (suc n)
clamp-step zero                            = l1≤
clamp-step (suc zero)                      = l1≤
clamp-step (suc (suc zero))                = l2≤3
clamp-step (suc (suc (suc zero)))          = l3≤4
clamp-step (suc (suc (suc (suc zero))))    = l4≤5
clamp-step (suc (suc (suc (suc (suc _))))) = l5≤5

-- Difference decomposition: n ≤ m means m is n plus some k.
≤-difference : ∀ {n m} → n ≤ m → ∃[ k ] (m ≡ k + n)
-- helper keeps the Σ witness explicit, so no with-abstraction surprises
≤-difference-step : ∀ {a b} → ∃[ k ] (b ≡ k + a) → ∃[ k ] (suc b ≡ k + suc a)
≤-difference-step {a} (k , eq) =
  k , trans (cong suc eq) (sym (+-suc k a))

≤-difference {zero}  {m}    z≤n      = m , sym (+-identityʳ m)
≤-difference {suc a} {suc b} (s≤s p) = ≤-difference-step {a} (≤-difference p)

-- k successor steps
clamp-chain : ∀ n k → clamp-trust n ≤ₜ clamp-trust (k + n)
clamp-chain n zero    = ≤ₜ-refl (clamp-trust n)
clamp-chain n (suc k) = ≤ₜ-trans (clamp-chain n k) (clamp-step (k + n))

clamp-monotone : ∀ {n m} → n ≤ m → clamp-trust n ≤ₜ clamp-trust m
clamp-monotone {n} p with ≤-difference p
... | k , eq =
  subst (λ z → clamp-trust n ≤ₜ clamp-trust z) (sym eq) (clamp-chain n k)


------------------------------------------------------------------------
-- Fixed points
------------------------------------------------------------------------

clamp-fixed-1  : clamp-trust (suc zero) ≡ Level1
clamp-fixed-1  = refl

clamp-fixed-0  : clamp-trust zero ≡ Level1
clamp-fixed-0  = refl

clamp-fixed-5  : clamp-trust (suc (suc (suc (suc (suc zero))))) ≡ Level5
clamp-fixed-5  = refl

clamp-fixed-10 :
  clamp-trust (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ≡ Level5
clamp-fixed-10 = refl

clamp-above : ∀ k →
  clamp-trust (suc (suc (suc (suc (suc k))))) ≡ Level5
clamp-above k = refl

------------------------------------------------------------------------
-- Totality into the enumeration
--
-- The point of clamping is that the result is a real trust level, not a
-- number sitting between two of them.  Idempotence of the numeric
-- projection is that statement.
------------------------------------------------------------------------

clamp-idempotent : ∀ n → trust-to-ℕ (clamp-trust (trust-to-ℕ (clamp-trust n)))
                            ≡ trust-to-ℕ (clamp-trust n)
clamp-idempotent zero                            = refl
clamp-idempotent (suc zero)                      = refl
clamp-idempotent (suc (suc zero))                = refl
clamp-idempotent (suc (suc (suc zero)))          = refl
clamp-idempotent (suc (suc (suc (suc zero))))    = refl
clamp-idempotent (suc (suc (suc (suc (suc _))))) = refl
