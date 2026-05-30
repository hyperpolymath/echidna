-- SPDX-License-Identifier: MPL-2.0
-- ParallelSoundness.agda — Speculative parallel proof-search soundness.
--
-- Models the Chapel `parallelProofSearchSpeculative` function
-- (src/chapel/parallel_proof_search.chpl) as a pure first-success-wins
-- fold over a vector of single-prover outcomes, and proves three
-- semantic invariants of the aggregation:
--
--   1.  Soundness                — `speculative xs = true → Any IsTrue xs`
--                                  (no spurious portfolio successes;
--                                   if the verdict is true, at least one
--                                   prover individually said true)
--   2.  Completeness             — `Any IsTrue xs → speculative xs = true`
--                                  (no real success is silently dropped)
--   3.  Cancellation-safety      — once a prover position witnesses
--                                  success, the verdict is true regardless
--                                  of what other provers do (the winner is
--                                  insensitive to the losers' state)
--
-- The Chapel implementation uses an atomic compare-and-swap on a
-- shared `winnerIdx` to record the first-completing successful prover.
-- This Agda model captures the same observational semantics — any-true
-- over the result vector — by structural recursion. The CAS protocol
-- is a refinement of this model: it picks ONE successful index out of
-- the (possibly several) provers that succeed, but the aggregation
-- verdict (success or not) is unaffected by which index wins.
--
-- Wave-1 scope: this module proves the AGGREGATION layer. The
-- complementary layer — that `tryProver` itself is sound (i.e. its
-- `success = true` return implies the proof actually checks under the
-- existing trust pipeline) — is the responsibility of SoundnessPreservation
-- and the per-prover Idris2 ABI proofs in `src/abi/`, both of which
-- predate this PR. ParallelSoundness composes with them: an aggregation-
-- sound module over a verifier-sound input remains sound at the
-- portfolio level.

module ParallelSoundness where

open import Data.Bool  using (Bool; true; false; _∨_)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Vec   using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)

------------------------------------------------------------------------
-- 1.  Unit type and IsTrue predicate (shared idiom from
--     PortfolioConsistency.agda; not factored out yet)
------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

IsTrue : Bool → Set
IsTrue true  = ⊤
IsTrue false = ⊥

------------------------------------------------------------------------
-- 2.  Speculative aggregation: any-true over the portfolio
------------------------------------------------------------------------

-- Pure model of `parallelProofSearchSpeculative`. Returns true iff
-- at least one prover in the input vector returned success.
-- Structural recursion stands in for the Chapel-side atomic-CAS:
-- both compute the same predicate (∃ i. xs[i] = true), the latter
-- additionally records which index won the race.
speculative : {n : ℕ} → Vec Bool n → Bool
speculative []       = false
speculative (b ∷ bs) = b ∨ speculative bs

------------------------------------------------------------------------
-- 3.  Soundness — if the portfolio verdict is true, an actual
--                 successful prover exists in the input
------------------------------------------------------------------------

speculative-sound : {n : ℕ} (xs : Vec Bool n)
                  → IsTrue (speculative xs)
                  → Any IsTrue xs
speculative-sound []             ()
speculative-sound (true  ∷ _)    _  = here tt
speculative-sound (false ∷ bs)   p  = there (speculative-sound bs p)

------------------------------------------------------------------------
-- 4.  Completeness — if any prover succeeded, the aggregation
--                    cannot silently swallow the success
------------------------------------------------------------------------

speculative-complete : {n : ℕ} (xs : Vec Bool n)
                     → Any IsTrue xs
                     → IsTrue (speculative xs)
speculative-complete (true  ∷ _)  _          = tt
speculative-complete (false ∷ _)  (here ())
speculative-complete (false ∷ bs) (there p)  = speculative-complete bs p

------------------------------------------------------------------------
-- 5.  Cancellation-safety — a successful head wins regardless of
--                            the tail
--
-- Interpretation: in the Wave-1 speculative implementation no mid-flight
-- preemption happens. Even so, the FIRST observed success determines
-- the verdict; subsequent provers' outcomes (in this model, the tail
-- vector) cannot retroactively invalidate the win. Below: if `b = true`
-- at the head, the speculative result is true for ANY tail `bs`.
------------------------------------------------------------------------

cancellation-safety : {n : ℕ} (bs : Vec Bool n)
                    → IsTrue (speculative (true ∷ bs))
cancellation-safety _ = tt

------------------------------------------------------------------------
-- 6.  Sanity checks (executable; close the loop on the definitions)
------------------------------------------------------------------------

example-empty : speculative (false ∷ false ∷ false ∷ []) ≡ false
example-empty = refl

example-some  : speculative (false ∷ true  ∷ false ∷ []) ≡ true
example-some  = refl

example-head  : speculative (true  ∷ false ∷ false ∷ []) ≡ true
example-head  = refl

-- All-false vector cannot witness Any IsTrue (contrapositive of
-- soundness; useful as an independent sanity check that IsTrue
-- IsTrue false is uninhabited under this encoding).
no-success-2 : ¬ Any IsTrue (false ∷ false ∷ [])
no-success-2 (here ())
no-success-2 (there (here ()))
no-success-2 (there (there ()))
