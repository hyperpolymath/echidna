-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Axiom_Policy — SPARK-verified policy enforcement for echidna axiom scanning.
--
-- This package specifies and proves the two central soundness invariants of
-- the axiom tracker:
--
--   1. Soundness  — if any usage carries danger level Reject, the output
--                   policy MUST be Policy_Rejected.
--                   (A Reject construct can never be silently accepted.)
--
--   2. Precision  — if no usage carries danger level Reject, the output
--                   policy MUST NOT be Policy_Rejected.
--                   (No false positives on clean proofs.)
--
-- GNATprove (SPARK toolset) discharges both properties automatically from
-- the body in axiom_policy.adb — no manual ghost proofs required.
--
-- The Ada/SPARK code is called from the Zig bridge layer
-- (src/zig/ffi/axiom_spark_bridge.zig) which in turn is linked by Rust
-- under the `spark` Cargo feature.

with Axiom_Types; use Axiom_Types;

package Axiom_Policy with SPARK_Mode => On is

   --  Maximum number of axiom usages we handle in a single scan.
   --  Matches ECHIDNA_MAX_AXIOM_USAGES in the Zig/Rust headers.
   Max_Usages : constant := 1024;

   subtype Usage_Count is Natural range 0 .. Max_Usages;
   type Danger_Array is array (Natural range <>) of Danger_Level;

   --  -----------------------------------------------------------------------
   --  Enforce
   --
   --  Replicate the logic of AxiomTracker::enforce_policy in Rust, with
   --  formal SPARK Post-condition contracts that GNATprove verifies.
   --
   --  Contract:
   --    (∃ i ∈ Usages. Usages(i) = Reject) → result = Policy_Rejected
   --    (∀ i ∈ Usages. Usages(i) ≠ Reject) → result ≠ Policy_Rejected
   --  -----------------------------------------------------------------------
   function Enforce (Usages : Danger_Array) return Axiom_Policy
   with
     Pre  => Usages'Length <= Max_Usages,
     Post =>
       --  Soundness: reject-in → rejected-out
       (if (for some I in Usages'Range => Usages (I) = Reject)
        then Enforce'Result = Policy_Rejected)
       and then
       --  Precision: no-reject-in → not-rejected-out
       (if (for all I in Usages'Range => Usages (I) /= Reject)
        then Enforce'Result /= Policy_Rejected);

   --  -----------------------------------------------------------------------
   --  Worst_Danger
   --
   --  Return the highest danger level among all usages, or Safe for empty.
   --  Proven: result = Reject iff any usage carries Reject.
   --  -----------------------------------------------------------------------
   function Worst_Danger (Usages : Danger_Array) return Danger_Level
   with
     Pre  => Usages'Length <= Max_Usages,
     Post =>
       (Worst_Danger'Result = Reject) =
       (for some I in Usages'Range => Usages (I) = Reject);

end Axiom_Policy;
