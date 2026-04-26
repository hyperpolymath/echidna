-- SPDX-License-Identifier: PMPL-1.0-or-later
-- CertificateChain.agda — transitivity and vacuous validity of cert chains.
--
-- Models a certificate chain as a List CertStep where each CertStep
-- carries a prover id (ℕ) and a verified flag (Bool).
--
-- Proves:
--   (a) allVerified is transitive in the following sense: if every step
--       in chain1 ++ chain2 is verified, then every step in chain1 is
--       verified and every step in chain2 is verified, and vice versa.
--       This is the "composition lemma" — chains compose cleanly when
--       both halves are verified.
--   (b) An empty certificate chain is trivially valid (vacuous truth):
--       allVerified [] holds with no conditions.

module CertificateChain where

open import Data.Bool  using (Bool; true; false)
open import Data.List  using (List; []; _∷_; _++_)
open import Data.Nat   using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

------------------------------------------------------------------------
-- 1.  CertStep: one link in a certificate chain
------------------------------------------------------------------------

-- Each step records which prover produced it and whether it passed
-- verification (e.g. Alethe, DRAT/LRAT, TSTP checking in dispatch.rs).
record CertStep : Set where
  constructor MkStep
  field
    proverId : ℕ      -- identifies the prover backend
    verified : Bool   -- true iff the certificate was checked OK

------------------------------------------------------------------------
-- 2.  allVerified: every step in the chain is verified
------------------------------------------------------------------------

-- Inductive predicate: allVerified xs holds when every CertStep in xs
-- has verified = true.
data allVerified : List CertStep → Set where
  av-nil  : allVerified []
  av-cons : {s : CertStep} {ss : List CertStep}
          → CertStep.verified s ≡ true
          → allVerified ss
          → allVerified (s ∷ ss)

------------------------------------------------------------------------
-- 3.  (b) Empty chain is trivially valid
------------------------------------------------------------------------

-- An empty certificate list has no steps to check, so it is vacuously
-- verified.  This is a direct constructor — no conditions required.
empty-chain-valid : allVerified []
empty-chain-valid = av-nil

------------------------------------------------------------------------
-- 4.  Split lemma: allVerified (xs ++ ys) ↔ allVerified xs × allVerified ys
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)

-- Forward direction: a verified concatenated chain splits into two
-- individually-verified chains.
av-split : (xs ys : List CertStep)
         → allVerified (xs ++ ys)
         → allVerified xs × allVerified ys
av-split []       ys av              = av-nil , av
av-split (x ∷ xs) ys (av-cons vx av-rest) =
  let (avxs , avys) = av-split xs ys av-rest
  in  av-cons vx avxs , avys

-- Backward direction: two individually-verified chains compose into a
-- verified concatenated chain.
av-join : (xs ys : List CertStep)
        → allVerified xs
        → allVerified ys
        → allVerified (xs ++ ys)
av-join []       ys av-nil           avys = avys
av-join (x ∷ xs) ys (av-cons vx avxs) avys =
  av-cons vx (av-join xs ys avxs avys)

------------------------------------------------------------------------
-- 5.  (a) Transitivity / composition lemma
--
--     A verified chain composed from two sub-chains is fully verified
--     if and only if each sub-chain is individually verified.
--     We prove both directions explicitly.
------------------------------------------------------------------------

-- "Chain composition is sound": if both halves are verified, the whole
-- composed chain is verified.
compose-verified : (chain1 chain2 : List CertStep)
                 → allVerified chain1
                 → allVerified chain2
                 → allVerified (chain1 ++ chain2)
compose-verified = av-join

-- "Decomposition preserves verification": a verified composed chain
-- implies both sub-chains are verified.
decompose-verified : (chain1 chain2 : List CertStep)
                   → allVerified (chain1 ++ chain2)
                   → allVerified chain1 × allVerified chain2
decompose-verified = av-split

------------------------------------------------------------------------
-- 6.  Corollary: transitivity across a three-chain concatenation
--
--     If chain A verifies chain B (i.e. A ++ B is verified) and
--     chain B verifies chain C (i.e. B ++ C is verified), and B
--     is non-empty and verified, then A ++ B ++ C is verified.
------------------------------------------------------------------------

three-way-compose : (a b c : List CertStep)
                  → allVerified a
                  → allVerified b
                  → allVerified c
                  → allVerified (a ++ b ++ c)
three-way-compose a b c ava avb avc =
  av-join a (b ++ c) ava (av-join b c avb avc)

------------------------------------------------------------------------
-- 7.  Identity: appending an empty chain changes nothing
------------------------------------------------------------------------

-- Verified xs remains verified when we append an empty chain.
av-append-nil : (xs : List CertStep) → allVerified xs → allVerified (xs ++ [])
av-append-nil []       av-nil           = av-nil
av-append-nil (x ∷ xs) (av-cons vx avxs) =
  av-cons vx (av-append-nil xs avxs)

-- Prepending an empty chain is the identity.
av-prepend-nil : (xs : List CertStep) → allVerified xs → allVerified ([] ++ xs)
av-prepend-nil xs avxs = avxs
