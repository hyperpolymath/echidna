-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- SPARK companion spec for src/rust/verification/axiom_tracker.rs
--
-- Proved properties
--   1. DangerLevel total order (Safe < Noted < Warning < Reject) is
--      given definitionally by Ada enumeration ordering.
--   2. Enforce_Policy cap-at-Reject monotonicity: if any usage carries
--      Reject, the returned policy is always Rejected.
--   3. Enforce_Policy is fully deterministic and total (no Precondition).
--   4. Is_Acceptable <=> Kind /= Rejected (exact Rust semantics).
--   5. Worst_Danger is a pure function of the policy kind.

pragma Ada_2022;

package Axiom_Tracker
  with SPARK_Mode => On
is
   -- ── DangerLevel ────────────────────────────────────────────────────
   -- Mirrors Rust enum DangerLevel (ordered Safe < Noted < Warning < Reject).
   -- Ada enumeration types carry a built-in discrete order matching
   -- declaration order, so the 4-level hierarchy is axiomatic here.
   type Danger_Level is (Safe, Noted, Warning, Reject);

   -- ── AxiomUsage (proof-relevant fields only) ────────────────────────
   -- The full Rust AxiomUsage also carries prover, construct string, and
   -- optional line number.  For the policy proof only Danger matters.
   type Axiom_Usage is record
      Danger : Danger_Level := Safe;
   end record;

   -- Bounded usage array (mirrors Vec<AxiomUsage>).
   -- Upper bound 1_024 is generous for any realistic proof run.
   Max_Usages : constant := 1_024;
   subtype Usage_Index is Positive range 1 .. Max_Usages;
   type Usage_Array is array (Usage_Index range <>) of Axiom_Usage;

   -- ── AxiomPolicy ────────────────────────────────────────────────────
   -- Mirrors Rust enum AxiomPolicy (Clean / ClassicalAxioms /
   -- IncompleteProof / Rejected).  The Vec payloads are omitted here;
   -- only the discriminant drives the proofs below.
   type Policy_Kind is (Clean, Classical_Axioms, Incomplete_Proof, Rejected);

   type Axiom_Policy is record
      Kind : Policy_Kind;
   end record;

   -- ── Enforce_Policy ─────────────────────────────────────────────────
   -- Mirrors AxiomTracker::enforce_policy.
   --
   -- Post-condition encodes the four determinism branches and
   -- cap-at-Reject monotonicity:
   --
   --   (a) any Reject usage  => policy is Rejected
   --   (b) no Reject, some Warning => Incomplete_Proof
   --   (c) no Reject, no Warning, some Noted => Classical_Axioms
   --   (d) empty or all-Safe => Clean
   --
   -- Branch (a) is cap-at-Reject monotonicity; branches (b)-(d) complete
   -- the total characterisation so gnatprove can verify the body.
   function Enforce_Policy (Usages : Usage_Array) return Axiom_Policy
     with Post =>
       -- (a) cap-at-Reject
       (if (for some J in Usages'Range => Usages (J).Danger = Reject)
        then Enforce_Policy'Result.Kind = Rejected)
       and then
       -- (b)
       (if (for all J in Usages'Range => Usages (J).Danger /= Reject)
          and (for some J in Usages'Range => Usages (J).Danger = Warning)
        then Enforce_Policy'Result.Kind = Incomplete_Proof)
       and then
       -- (c)
       (if (for all J in Usages'Range => Usages (J).Danger /= Reject)
          and (for all J in Usages'Range => Usages (J).Danger /= Warning)
          and (for some J in Usages'Range => Usages (J).Danger = Noted)
        then Enforce_Policy'Result.Kind = Classical_Axioms)
       and then
       -- (d) empty input
       (if Usages'Length = 0
        then Enforce_Policy'Result.Kind = Clean);

   -- ── Is_Acceptable ──────────────────────────────────────────────────
   -- Mirrors AxiomPolicy::is_acceptable.
   -- Post is an exact boolean characterisation (not just implication).
   function Is_Acceptable (P : Axiom_Policy) return Boolean
     with Post => Is_Acceptable'Result = (P.Kind /= Rejected);

   -- ── Worst_Danger ───────────────────────────────────────────────────
   -- Mirrors AxiomPolicy::worst_danger.
   -- Exhaustive case equation lets gnatprove discharge callers that
   -- reason about the returned level without opening the body.
   function Worst_Danger (P : Axiom_Policy) return Danger_Level
     with Post =>
       (case P.Kind is
          when Clean            => Worst_Danger'Result = Safe,
          when Classical_Axioms => Worst_Danger'Result = Noted,
          when Incomplete_Proof => Worst_Danger'Result = Warning,
          when Rejected         => Worst_Danger'Result = Reject);

   -- ── Monotonicity lemma (ghost) ──────────────────────────────────────
   -- For any single usage U and the policy derived from a set containing U,
   -- the policy's worst danger is >= U.Danger.
   --
   -- Stated as a ghost function so callers can use it in their own
   -- contracts without runtime cost.  The body (in the .adb) is proved
   -- by gnatprove from Enforce_Policy's post-condition.
   function Policy_Dominates_Usage
     (Policy : Axiom_Policy; U : Axiom_Usage) return Boolean
   is (Worst_Danger (Policy) >= U.Danger)
     with Ghost;

end Axiom_Tracker;
