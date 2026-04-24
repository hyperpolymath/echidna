-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Axiom_Types — shared type definitions for the SPARK axiom-policy layer.
--
-- These types mirror the Rust enum layout in
-- src/rust/verification/axiom_tracker.rs exactly.
-- The C-ABI encoding (u8 discriminants) is fixed here and must not
-- change without a corresponding bump in the Idris2 ABI spec
-- (src/abi/EchidnaABI/AxiomTracker.idr) and the Zig bridge.

package Axiom_Types with SPARK_Mode => On is

   --  -----------------------------------------------------------------------
   --  DangerLevel  (Rust: DangerLevel, repr(u8))
   --
   --  Ordering: Safe < Noted < Warning < Reject
   --  This is a strict total order — SPARK verifies that Enforce_Policy
   --  respects it.
   --  -----------------------------------------------------------------------
   type Danger_Level is (Safe, Noted, Warning, Reject);
   --  Encoding matches Rust PartialOrd derivation order:
   --    Safe=0, Noted=1, Warning=2, Reject=3

   --  -----------------------------------------------------------------------
   --  Axiom_Policy  (Rust: AxiomPolicy, repr discriminant)
   --  -----------------------------------------------------------------------
   type Axiom_Policy is
     (Policy_Clean,       -- only Safe axioms; proof accepted unconditionally
      Policy_Classical,   -- classical axioms noted; proof accepted with note
      Policy_Incomplete,  -- sorry/Admitted/postulate found; accepted + warning
      Policy_Rejected);   -- unsound construct detected; proof REJECTED

   --  -----------------------------------------------------------------------
   --  C-ABI discriminants (must match Zig/Rust extern "C" bindings)
   --  -----------------------------------------------------------------------
   --  These representation clauses pin the C-visible values; changing them
   --  is an ABI break.
   for Danger_Level use (Safe => 0, Noted => 1, Warning => 2, Reject => 3);
   for Axiom_Policy use
     (Policy_Clean      => 0,
      Policy_Classical  => 1,
      Policy_Incomplete => 2,
      Policy_Rejected   => 3);

end Axiom_Types;
