-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- SPARK companion body for solver_integrity.ads
--
-- Implementation strategy
-- -----------------------
-- Classify_Verification is a 5-arm if-chain mirroring the Rust decision tree
-- top-to-bottom.  Each return statement closes exactly one Post case;
-- gnatprove substitutes the case-branch predicate at the return site and
-- discharges at --level=0/1.
--
-- The ghost lemmas (Cap_At_Tampered, Hash_Mismatch_Means_Tampered) are
-- named restatements with null bodies — gnatprove derives the conclusion
-- from the spec's Post-condition + the standard quantifier dualities.

pragma Ada_2022;

package body Solver_Integrity
  with SPARK_Mode => On
is

   function Classify_Verification
     (Binary_Found            : Boolean;
      Expected_Is_Placeholder : Boolean;
      Compute_Succeeded       : Boolean;
      Hashes_Match            : Boolean) return Integrity_Status is
   begin
      -- (1) Mirrors Rust line 222: find_solver_binary returned None.
      if not Binary_Found then
         return Missing;
      end if;

      -- (2) Mirrors Rust line 240: entry.shake3_512.starts_with("PLACEHOLDER").
      if Expected_Is_Placeholder then
         return Uninitialized;
      end if;

      -- (3) Mirrors Rust line 298-309: compute_shake3_512 returned Err.
      if not Compute_Succeeded then
         return Missing;
      end if;

      -- (4) Mirrors Rust line 277-286: computed == expected.
      if Hashes_Match then
         return Verified;
      else
         return Tampered;
      end if;
   end Classify_Verification;

   function Quick_Reverify (Cached_Match : Boolean) return Reverify_Outcome is
   begin
      if Cached_Match then
         return Unchanged;
      else
         return Changed;
      end if;
   end Quick_Reverify;

   -- ── Cap_At_Tampered ────────────────────────────────────────────────
   -- Ghost lemma; gnatprove discharges from definitions:
   --   Has_Tampered (S) = (for some I, S(I) = Tampered)
   --   Is_Safe (Tampered) = False  (by Is_Safe expression function)
   --   => (for some I, not Is_Safe (S(I)))
   --   => not (for all I, Is_Safe (S(I)))
   --   => not Aggregate_Safe (S).
   -- Null body is sufficient — Post follows from Pre by SMT.
   procedure Cap_At_Tampered (Statuses : Status_Array) is
   begin
      null;
   end Cap_At_Tampered;

   -- ── Hash_Mismatch_Means_Tampered ───────────────────────────────────
   -- Ghost lemma; the four-fold conjunction in Pre is exactly the case
   -- arm of Classify_Verification's Post that maps to Tampered, so the
   -- conclusion follows by post-condition application + the disjointness
   -- of the case arms.
   procedure Hash_Mismatch_Means_Tampered
     (Binary_Found            : Boolean;
      Expected_Is_Placeholder : Boolean;
      Compute_Succeeded       : Boolean;
      Hashes_Match            : Boolean) is
   begin
      null;
   end Hash_Mismatch_Means_Tampered;

end Solver_Integrity;
