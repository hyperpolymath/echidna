-- SPDX-License-Identifier: MPL-2.0
-- ParallelSoundness.agda — Speculative parallel proof-search soundness.
--
-- Two layers.
--
-- A.  Aggregation (sections 1–4). `speculative` is the any-true fold over
--     the provers' outcomes, with soundness and completeness. This layer
--     says only that boolean OR is correct; it says nothing about
--     concurrency, and on its own it is NOT a cancellation-safety result.
--
-- B.  Race protocol (sections 5–9). A small-step model of
--     `parallelProofSearchSpeculativeTelemetry` in
--     src/chapel/parallel_proof_search.chpl, run over EVERY interleaving
--     of its events:
--
--       * `done i`  — prover i reaches its CAS, after its `tryProver` call
--                     has returned. A prover that observed the cancel token
--                     before finishing returned a preempted result
--                     (exitCode = -5, success = false). Otherwise it reports
--                     its outcome `rs[i]`, and on success it attempts the
--                     CAS `winnerIdx: -1 → i`. In Chapel the return and the
--                     CAS are separate statements, so a prover can return
--                     and be descheduled before its CAS. Nothing it does in
--                     that gap is visible to the others (`results[i]` and
--                     `attempted[i]` are its own slots, read only after the
--                     join), so the event sits at the CAS, the
--                     linearisation point, and the gap is just a later
--                     `done i`.
--       * `signal`  — the CAS winner's `cancelToken.cancelled.write(true)`.
--                     It is a separate event, so every interleaving of the
--                     CAS and the cancel write with other provers' finishes
--                     is covered.
--
--     Theorems, each for an arbitrary schedule and an arbitrary winner
--     index (the previous version covered index 0 only, by `tt`):
--
--       race-sound          the reported winner really succeeded;
--       winner-stable       once a winner is set, no later event changes it;
--       preempted-inert     after cancellation a finishing prover leaves the
--                           state exactly as it was (exitCode -5 is inert);
--       cancel-after-win    the token is never set without a winner, so no
--                           success is preempted before a winner exists;
--       race-complete       if a successful prover finishes, a winner exists;
--       winner-is-first     the winner is exactly the first successful
--                           prover to reach the CAS in schedule order (any
--                           index). It need not be the first to return from
--                           `tryProver`: one that returns first and is
--                           descheduled before its CAS can lose;
--       race-agrees         on a schedule in which every prover finishes,
--                           "a winner exists" ⇔ `speculative rs` (layer A).
--
-- Assumed boundary (ASSUMED, not proved here):
--   * Chapel atomics are sequentially consistent (Chapel's default memory
--     order), so the CAS and the cancel write are linearisable and every
--     execution corresponds to some schedule `List (Event n)`.
--   * `tryProver` returns `success = false` whenever it observes the token
--     (src/chapel/parallel_proof_search.chpl, the exitCode = -5 branch), and
--     otherwise reports the outcome `rs[i]` modelled here.
--   * `coforall` joins every task before `winnerIdx.read()`.
-- Whether `success = true` means the proof really checks is the job of the
-- per-prover trust pipeline, not of this module.

module ParallelSoundness where

open import Data.Bool    using (Bool; true; false; _∨_; _∧_; not)
open import Data.Nat     using (ℕ)
open import Data.Fin     using (Fin; zero; suc)
open import Data.Vec     using (Vec; []; _∷_; lookup)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (∃; _,_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
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
-- 2.  Layer A — any-true aggregation over the portfolio
------------------------------------------------------------------------

speculative : {n : ℕ} → Vec Bool n → Bool
speculative []       = false
speculative (b ∷ bs) = b ∨ speculative bs

------------------------------------------------------------------------
-- 3.  Layer A soundness — a true verdict has a successful witness
------------------------------------------------------------------------

speculative-sound : {n : ℕ} (xs : Vec Bool n)
                  → IsTrue (speculative xs)
                  → Any IsTrue xs
speculative-sound []             ()
speculative-sound (true  ∷ _)    _  = here tt
speculative-sound (false ∷ bs)   p  = there (speculative-sound bs p)

------------------------------------------------------------------------
-- 4.  Layer A completeness — no success is silently dropped
------------------------------------------------------------------------

speculative-complete : {n : ℕ} (xs : Vec Bool n)
                     → Any IsTrue xs
                     → IsTrue (speculative xs)
speculative-complete (true  ∷ _)  _          = tt
speculative-complete (false ∷ _)  (here ())
speculative-complete (false ∷ bs) (there p)  = speculative-complete bs p

-- Index view of Any, used to connect the two layers.
any→index : {n : ℕ} (xs : Vec Bool n) → Any IsTrue xs → ∃ λ i → lookup xs i ≡ true
any→index (true  ∷ _)  (here _)  = zero , refl
any→index (false ∷ _)  (here ())
any→index (_ ∷ xs)     (there p) with any→index xs p
... | i , eq = suc i , eq

index→any : {n : ℕ} (xs : Vec Bool n) (i : Fin n) → lookup xs i ≡ true → Any IsTrue xs
index→any (true  ∷ _)  zero    _  = here tt
index→any (false ∷ _)  zero    ()
index→any (_ ∷ xs)     (suc i) eq = there (index→any xs i eq)

------------------------------------------------------------------------
-- 5.  Layer B — state, events and the step relation
------------------------------------------------------------------------

-- `winner` is `winnerIdx` (nothing = -1); `cancelled` is the token.
record State (n : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    winner    : Maybe (Fin n)
    cancelled : Bool
open State public

data Event (n : ℕ) : Set where
  done   : Fin n → Event n   -- prover i's tryProver returns
  signal : Event n           -- the CAS winner writes the cancel token

start : {n : ℕ} → State n
start = ⟨ nothing , false ⟩

-- compareAndSwap(-1, i): succeeds only when no winner is recorded.
cas : {n : ℕ} → Maybe (Fin n) → Fin n → Maybe (Fin n)
cas nothing  i = just i
cas (just w) _ = just w

-- A finishing prover attempts the CAS only if its observed result is a
-- success; the observed result is `false` once the token is set (exitCode -5).
finish : {n : ℕ} → Bool → Maybe (Fin n) → Fin n → Maybe (Fin n)
finish true  w i = cas w i
finish false w _ = w

-- Only a CAS winner writes the token; with no winner the event is a no-op.
signalled : {n : ℕ} → Maybe (Fin n) → Bool → Bool
signalled (just _) _ = true
signalled nothing  c = c

step : {n : ℕ} → Vec Bool n → State n → Event n → State n
step rs ⟨ w , c ⟩ (done i) = ⟨ finish (not c ∧ lookup rs i) w i , c ⟩
step rs ⟨ w , c ⟩ signal   = ⟨ w , signalled w c ⟩

-- An execution: any interleaving of events, applied in order.
run : {n : ℕ} → Vec Bool n → State n → List (Event n) → State n
run rs s []       = s
run rs s (e ∷ es) = run rs (step rs s e) es

------------------------------------------------------------------------
-- 6.  The protocol invariant: winners succeeded, and the token is set
--     only after a win
------------------------------------------------------------------------

Good : {n : ℕ} → Vec Bool n → Maybe (Fin n) → Set
Good rs nothing  = ⊤
Good rs (just w) = lookup rs w ≡ true

Armed : {n : ℕ} → Maybe (Fin n) → Bool → Set
Armed nothing  c = c ≡ false
Armed (just _) _ = ⊤

record Inv {n : ℕ} (rs : Vec Bool n) (s : State n) : Set where
  field
    good  : Good rs (winner s)
    armed : Armed (winner s) (cancelled s)
open Inv public

start-inv : {n : ℕ} (rs : Vec Bool n) → Inv rs start
start-inv rs = record { good = tt ; armed = refl }

finish-just : {n : ℕ} (b : Bool) (v i : Fin n) → finish b (just v) i ≡ just v
finish-just true  v i = refl
finish-just false v i = refl

done-from-nothing : {n : ℕ} (rs : Vec Bool n) (i : Fin n) (b : Bool)
                  → lookup rs i ≡ b
                  → Inv rs ⟨ finish b nothing i , false ⟩
done-from-nothing rs i true  eq = record { good = eq ; armed = tt }
done-from-nothing rs i false _  = record { good = tt ; armed = refl }

step-inv : {n : ℕ} (rs : Vec Bool n) (s : State n) (e : Event n)
         → Inv rs s → Inv rs (step rs s e)
step-inv rs ⟨ just v , c ⟩ (done i) inv
  rewrite finish-just (not c ∧ lookup rs i) v i = record { good = good inv ; armed = tt }
step-inv rs ⟨ nothing , true ⟩  (done i) record { armed = () }
step-inv rs ⟨ nothing , false ⟩ (done i) inv = done-from-nothing rs i (lookup rs i) refl
step-inv rs ⟨ just v  , c ⟩ signal inv = record { good = good inv ; armed = tt }
step-inv rs ⟨ nothing , c ⟩ signal inv = inv

run-inv : {n : ℕ} (rs : Vec Bool n) (s : State n) (es : List (Event n))
        → Inv rs s → Inv rs (run rs s es)
run-inv rs s []       inv = inv
run-inv rs s (e ∷ es) inv = run-inv rs (step rs s e) es (step-inv rs s e inv)

------------------------------------------------------------------------
-- 7.  Soundness, stability and cancellation-safety over every schedule
------------------------------------------------------------------------

-- The reported winner, at ANY index, genuinely succeeded.
race-sound : {n : ℕ} (rs : Vec Bool n) (es : List (Event n)) {w : Fin n}
           → winner (run rs start es) ≡ just w → lookup rs w ≡ true
race-sound rs es eq = subst (Good rs) eq (good (run-inv rs start es (start-inv rs)))

step-keeps : {n : ℕ} (rs : Vec Bool n) (s : State n) (e : Event n) {w : Fin n}
           → winner s ≡ just w → winner (step rs s e) ≡ just w
step-keeps rs ⟨ just v , c ⟩ (done i) refl = finish-just (not c ∧ lookup rs i) v i
step-keeps rs ⟨ just v , c ⟩ signal   refl = refl

-- Cancellation-safety (1): once a winner is recorded, no later event —
-- a loser's success, a preempted loser, or the cancel write — changes it.
winner-stable : {n : ℕ} (rs : Vec Bool n) (s : State n) (es : List (Event n)) {w : Fin n}
              → winner s ≡ just w → winner (run rs s es) ≡ just w
winner-stable rs s []       eq = eq
winner-stable rs s (e ∷ es) eq = winner-stable rs (step rs s e) es (step-keeps rs s e eq)

-- Cancellation-safety (2): after the token is set, a finishing prover
-- (preempted, exitCode -5) leaves the whole state unchanged.
preempted-inert : {n : ℕ} (rs : Vec Bool n) (w : Maybe (Fin n)) (i : Fin n)
                → step rs ⟨ w , true ⟩ (done i) ≡ ⟨ w , true ⟩
preempted-inert rs w i = refl

-- Cancellation-safety (3): in every reachable state the token is set only
-- if a winner exists, so a success is never preempted before a win.
cancel-after-win : {n : ℕ} (rs : Vec Bool n) (es : List (Event n))
                 → Armed (winner (run rs start es)) (cancelled (run rs start es))
cancel-after-win rs es = armed (run-inv rs start es (start-inv rs))

------------------------------------------------------------------------
-- 8.  Completeness and the winner's identity
------------------------------------------------------------------------

data _∈_ {n : ℕ} (e : Event n) : List (Event n) → Set where
  now   : {es : List (Event n)} → e ∈ (e ∷ es)
  later : {e′ : Event n} {es : List (Event n)} → e ∈ es → e ∈ (e′ ∷ es)

IsSet : {n : ℕ} → Maybe (Fin n) → Set
IsSet nothing  = ⊥
IsSet (just _) = ⊤

set-stays : {n : ℕ} (rs : Vec Bool n) (s : State n) (es : List (Event n)) {w : Fin n}
          → winner s ≡ just w → IsSet (winner (run rs s es))
set-stays rs s es eq with winner (run rs s es) | winner-stable rs s es eq
... | just _ | _ = tt

done-sets : {n : ℕ} (rs : Vec Bool n) (s : State n) (i : Fin n)
          → Inv rs s → lookup rs i ≡ true
          → ∃ λ w → winner (step rs s (done i)) ≡ just w
done-sets rs ⟨ just v , c ⟩    i _ _ = v , finish-just (not c ∧ lookup rs i) v i
done-sets rs ⟨ nothing , true ⟩  i record { armed = () } _
done-sets rs ⟨ nothing , false ⟩ i _ eq rewrite eq = i , refl

-- If a successful prover finishes at any point of any schedule, there is
-- a winner at the end — whatever else happened before or after.
race-complete : {n : ℕ} (rs : Vec Bool n) (s : State n) (es : List (Event n)) {i : Fin n}
              → Inv rs s → lookup rs i ≡ true → done i ∈ es
              → IsSet (winner (run rs s es))
race-complete rs s (done i ∷ es) inv ok now with done-sets rs s i inv ok
... | _ , eq = set-stays rs (step rs s (done i)) es eq
race-complete rs s (e ∷ es) inv ok (later p) =
  race-complete rs (step rs s e) es (step-inv rs s e inv) ok p

-- The first successful prover to reach the CAS, in schedule order.
pick : {n : ℕ} → Bool → Fin n → Maybe (Fin n) → Maybe (Fin n)
pick true  i _    = just i
pick false _ rest = rest

first : {n : ℕ} → Vec Bool n → List (Event n) → Maybe (Fin n)
first rs []            = nothing
first rs (signal ∷ es) = first rs es
first rs (done i ∷ es) = pick (lookup rs i) i (first rs es)

-- The winner is exactly the first successful prover to reach the CAS (not
-- necessarily the first to return from `tryProver`): any index can win,
-- and the result is determined by the schedule alone.
winner-is-first : {n : ℕ} (rs : Vec Bool n) (es : List (Event n))
                → winner (run rs start es) ≡ first rs es
winner-is-first rs []            = refl
winner-is-first rs (signal ∷ es) = winner-is-first rs es
winner-is-first rs (done i ∷ es) = go (lookup rs i)
  where
  go : (b : Bool) → winner (run rs ⟨ finish b nothing i , false ⟩ es) ≡ pick b i (first rs es)
  go true  = winner-stable rs ⟨ just i , false ⟩ es refl
  go false = winner-is-first rs es

------------------------------------------------------------------------
-- 9.  Agreement with layer A on schedules where every prover finishes
------------------------------------------------------------------------

Covers : {n : ℕ} → List (Event n) → Set
Covers {n} es = (i : Fin n) → done i ∈ es

isSet→just : {n : ℕ} (m : Maybe (Fin n)) → IsSet m → ∃ λ w → m ≡ just w
isSet→just (just w) _ = w , refl
isSet→just nothing  ()

race-agrees : {n : ℕ} (rs : Vec Bool n) (es : List (Event n)) → Covers es
            → IsTrue (speculative rs) → IsSet (winner (run rs start es))
race-agrees rs es cov p with any→index rs (speculative-sound rs p)
... | i , ok = race-complete rs start es (start-inv rs) ok (cov i)

race-agrees-sound : {n : ℕ} (rs : Vec Bool n) (es : List (Event n))
                  → IsSet (winner (run rs start es)) → IsTrue (speculative rs)
race-agrees-sound rs es set with isSet→just (winner (run rs start es)) set
... | w , eq = speculative-complete rs (index→any rs w (race-sound rs es eq))

------------------------------------------------------------------------
-- 10.  Sanity checks (executable; close the loop on the definitions)
------------------------------------------------------------------------

example-empty : speculative (false ∷ false ∷ false ∷ []) ≡ false
example-empty = refl

example-some  : speculative (false ∷ true  ∷ false ∷ []) ≡ true
example-some  = refl

-- Two successes race; prover 2 finishes first and wins, the token is set,
-- and prover 1's later success is preempted. The winner is index 2, not 0.
race-example : winner (run (false ∷ true ∷ true ∷ [])
                           start
                           (done (suc (suc zero)) ∷ signal ∷ done (suc zero) ∷ done zero ∷ []))
             ≡ just (suc (suc zero))
race-example = refl

-- A success that finishes BEFORE the winner's cancel write still loses the
-- CAS: the winner is unchanged.
cas-race-example : winner (run (true ∷ true ∷ [])
                               start
                               (done zero ∷ done (suc zero) ∷ signal ∷ []))
                 ≡ just zero
cas-race-example = refl

-- No success, no winner, on any schedule shape used here.
no-winner-example : winner (run (false ∷ false ∷ []) start (done zero ∷ signal ∷ done (suc zero) ∷ []))
                  ≡ nothing
no-winner-example = refl

no-success-2 : ¬ Any IsTrue (false ∷ false ∷ [])
no-success-2 (here ())
no-success-2 (there (here ()))
no-success-2 (there (there ()))
