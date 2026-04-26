-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Coprocessor_Safety body — implementations whose post-conditions are
-- discharged by GNATprove.  See the spec for the proof obligations.

package body Coprocessor_Safety with SPARK_Mode => On is

   function Is_Self_Sufficient (T : Trust_Tier) return Boolean is
   begin
      return T >= Library_Wrapped;
   end Is_Self_Sufficient;

   function Encode (T : Trust_Tier) return Tier_Code is
   begin
      return Trust_Tier'Pos (T) + 1;
   end Encode;

   function Decode (C : Tier_Code) return Trust_Tier is
   begin
      return Trust_Tier'Val (C - 1);
   end Decode;

end Coprocessor_Safety;
