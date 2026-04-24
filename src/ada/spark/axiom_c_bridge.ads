-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Axiom_C_Bridge — C-callable wrapper around the SPARK Enforce function.
--
-- SPARK_Mode is OFF here: we cross the Ada/C boundary using Interfaces.C and
-- System.Address, which SPARK cannot reason about. The correctness of the
-- *policy decision itself* is guaranteed by the SPARK contracts in
-- Axiom_Policy — this file is only a thin, manually-reviewed bridge.
--
-- C signature (matches axiom_spark_bridge.zig and src/rust/ffi/spark_axiom.rs):
--
--   int32_t echidna_spark_enforce_policy(
--       const uint8_t *danger_levels,   -- 0=Safe 1=Noted 2=Warning 3=Reject
--       size_t         count,
--       int32_t       *policy_out       -- 0=Clean 1=Classical 2=Incomplete 3=Rejected
--   );
--   returns 0 on success, -1 on invalid input.

with Interfaces.C; use Interfaces.C;
with System;

package Axiom_C_Bridge with SPARK_Mode => Off is

   --  Exported C function: echidna_spark_enforce_policy
   procedure C_Enforce_Policy
     (Danger_Levels : System.Address;
      Count         : Interfaces.C.size_t;
      Policy_Out    : access Interfaces.C.int;
      Status_Out    : access Interfaces.C.int)
   with Export     => True,
        Convention => C,
        External_Name => "echidna_spark_enforce_policy_inner";

   --  Exported C function: echidna_spark_worst_danger
   procedure C_Worst_Danger
     (Danger_Levels : System.Address;
      Count         : Interfaces.C.size_t;
      Danger_Out    : access Interfaces.C.int;
      Status_Out    : access Interfaces.C.int)
   with Export     => True,
        Convention => C,
        External_Name => "echidna_spark_worst_danger_inner";

end Axiom_C_Bridge;
