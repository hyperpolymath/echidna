-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- SPARK companion spec for src/rust/integrity/solver_integrity.rs
--
-- Proved properties
--   1. Classify_Verification is total over (Binary_Found, Expected_Is_Placeholder,
--      Compute_Succeeded, Hashes_Match) and never returns Unchecked.
--   2. Hash mismatch monotonicity: binary found AND expected is a real hash
--      AND compute succeeded AND hashes don't match  =>  status is Tampered.
--      (This is the load-bearing "hash mismatch => Failed" obligation from
--      hyperpolymath/echidna#40 roadmap.)
--   3. Is_Safe excludes Tampered and Missing exactly:
--      Is_Safe(S) = (S in {Verified, Uninitialized, Unchecked}).
--   4. Quick_Reverify is the boolean-pure restatement of BLAKE3 cached==current.
--   5. Aggregate_Safe is cap-at-Tampered monotonic: any Tampered member
--      forces the aggregate unsafe (Has_Tampered => not Aggregate_Safe).
--
-- SPARK does not model file IO, async, tokio, or cryptographic primitives,
-- so this companion is intentionally a pure-decision mirror.  The Rust impl's
-- find_solver_binary / compute_shake3_512 / compute_blake3 / RwLock layer is
-- abstracted into the four boolean inputs of Classify_Verification, and the
-- crypto guarantees come from the Keccak / BLAKE3 crates.  The SPARK proof
-- establishes that the *decision tree above the crypto layer* is correct.

pragma Ada_2022;

package Solver_Integrity
  with SPARK_Mode => On
is
   -- ── IntegrityStatus ────────────────────────────────────────────────
   -- Mirrors Rust enum IntegrityStatus (declared in the same positional
   -- order: Verified, Tampered, Missing, Uninitialized, Unchecked).
   type Integrity_Status is
     (Verified, Tampered, Missing, Uninitialized, Unchecked);

   -- ── Reverify_Outcome ───────────────────────────────────────────────
   -- Quick_reverify returns a Result<bool, _> in Rust; the pure logical
   -- content is a two-valued outcome.
   type Reverify_Outcome is (Unchanged, Changed);

   -- ── Classify_Verification ──────────────────────────────────────────
   -- Mirrors verify_solver's decision tree from src/rust/integrity/
   -- solver_integrity.rs:212-311.
   --
   -- Inputs encode the verify_solver pipeline:
   --   Binary_Found            -- find_solver_binary returned Some(_)
   --   Expected_Is_Placeholder -- entry.shake3_512.starts_with("PLACEHOLDER")
   --   Compute_Succeeded       -- compute_shake3_512(actual_path).is_ok()
   --   Hashes_Match            -- computed == entry.shake3_512
   --
   -- Decision tree (top-to-bottom precedence, mirroring the Rust source):
   --   1. not Binary_Found                       => Missing  (line 222)
   --   2. Expected_Is_Placeholder                => Uninitialized (line 257)
   --   3. not Compute_Succeeded                  => Missing  (line 302)
   --   4. Hashes_Match                           => Verified (line 279)
   --   5. otherwise (computed /= expected)       => Tampered (line 285)
   function Classify_Verification
     (Binary_Found            : Boolean;
      Expected_Is_Placeholder : Boolean;
      Compute_Succeeded       : Boolean;
      Hashes_Match            : Boolean) return Integrity_Status
     with Post =>
       (case Classify_Verification'Result is
          when Verified =>
            Binary_Found and not Expected_Is_Placeholder
            and Compute_Succeeded and Hashes_Match,
          when Tampered =>
            Binary_Found and not Expected_Is_Placeholder
            and Compute_Succeeded and not Hashes_Match,
          when Uninitialized =>
            Binary_Found and Expected_Is_Placeholder,
          when Missing =>
            (not Binary_Found)
            or (Binary_Found and not Expected_Is_Placeholder
                and not Compute_Succeeded),
          when Unchecked => False);

   -- ── Is_Safe ────────────────────────────────────────────────────────
   -- Mirrors IntegrityChecker::is_solver_safe (Rust line 355-361):
   --   matches!(status, Verified | Uninitialized | Unchecked)
   --
   -- Expressed as an expression function so callers can use it freely
   -- in their own Pre/Post contracts.
   function Is_Safe (S : Integrity_Status) return Boolean is
     (S = Verified or S = Uninitialized or S = Unchecked);

   -- ── Quick_Reverify ─────────────────────────────────────────────────
   -- Mirrors IntegrityChecker::quick_reverify's decision (Rust line 334):
   --   if current_hash != cached_hash { Changed } else { Unchanged }
   --
   -- SPARK abstracts the actual BLAKE3 comparison into Cached_Match.
   function Quick_Reverify (Cached_Match : Boolean) return Reverify_Outcome
     with Post =>
       (Quick_Reverify'Result = Unchanged) = Cached_Match;

   -- ── Bounded status array ───────────────────────────────────────────
   -- Mirrors verify_all's Vec<SolverIntegrityReport>, projected to just
   -- the status field (the rest is informational).  256 solvers covers
   -- any realistic deployment.
   Max_Solvers : constant := 256;
   subtype Solver_Index is Positive range 1 .. Max_Solvers;
   type Status_Array is array (Solver_Index range <>) of Integrity_Status;

   -- ── Aggregate_Safe ─────────────────────────────────────────────────
   -- A set of solvers is safe iff every member is safe.  Expression
   -- function — the body IS the postcondition, no separate VC needed.
   function Aggregate_Safe (Statuses : Status_Array) return Boolean is
     (for all I in Statuses'Range => Is_Safe (Statuses (I)));

   -- ── Has_Tampered (ghost) ───────────────────────────────────────────
   -- Predicate: does any solver in the set have status Tampered?
   -- Stated as ghost so callers can use it in their own contracts.
   function Has_Tampered (Statuses : Status_Array) return Boolean is
     (for some I in Statuses'Range => Statuses (I) = Tampered)
     with Ghost;

   -- ── Cap_At_Tampered (ghost lemma) ──────────────────────────────────
   -- Cap-at-Tampered monotonicity: if any solver is Tampered, the
   -- aggregate is unsafe.  Mirrors axiom_tracker's cap-at-Reject
   -- monotonicity for the integrity domain.
   --
   -- Proof: Has_Tampered (S) => (exists I, S(I) = Tampered)
   --                          => (exists I, not Is_Safe (S(I)))
   --                          => not (forall I, Is_Safe (S(I)))
   --                          => not Aggregate_Safe (S).
   procedure Cap_At_Tampered (Statuses : Status_Array)
     with Ghost,
          Pre  => Has_Tampered (Statuses),
          Post => not Aggregate_Safe (Statuses);

   -- ── Hash_Mismatch_Means_Tampered (ghost lemma) ─────────────────────
   -- Direct named restatement of issue #40's load-bearing obligation
   -- ("hash mismatch => Failed").  Proof: Classify_Verification's Post.
   procedure Hash_Mismatch_Means_Tampered
     (Binary_Found            : Boolean;
      Expected_Is_Placeholder : Boolean;
      Compute_Succeeded       : Boolean;
      Hashes_Match            : Boolean)
     with Ghost,
          Pre  => Binary_Found and not Expected_Is_Placeholder
                  and Compute_Succeeded and not Hashes_Match,
          Post => Classify_Verification
                    (Binary_Found, Expected_Is_Placeholder,
                     Compute_Succeeded, Hashes_Match) = Tampered;

end Solver_Integrity;
