-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Axiom_Policy body — pure SPARK implementation of enforce_policy.
--
-- GNATprove verifies all Post-conditions automatically via flow analysis and
-- SMT-backed proof. No manual ghost proofs or pragma Assume are required.

package body Axiom_Policy with SPARK_Mode => On is

   --  -----------------------------------------------------------------------
   --  Worst_Danger
   --  -----------------------------------------------------------------------
   function Worst_Danger (Usages : Danger_Array) return Danger_Level is
      Worst : Danger_Level := Safe;
   begin
      for I in Usages'Range loop
         if Usages (I) > Worst then
            Worst := Usages (I);
         end if;
         --  Short-circuit: nothing worse than Reject
         pragma Loop_Invariant
           (Worst = Reject or else
            (for all J in Usages'First .. I => Usages (J) /= Reject));
         exit when Worst = Reject;
      end loop;
      return Worst;
   end Worst_Danger;

   --  -----------------------------------------------------------------------
   --  Enforce
   --
   --  Mirrors AxiomTracker::enforce_policy exactly:
   --    Reject  → Policy_Rejected
   --    Warning → Policy_Incomplete  (no Reject present)
   --    Noted   → Policy_Classical   (no Reject/Warning present)
   --    else    → Policy_Clean
   --  -----------------------------------------------------------------------
   function Enforce (Usages : Danger_Array) return Axiom_Policy is
      Has_Reject  : Boolean := False;
      Has_Warning : Boolean := False;
      Has_Noted   : Boolean := False;
   begin
      for I in Usages'Range loop
         case Usages (I) is
            when Reject  => Has_Reject  := True;
            when Warning => Has_Warning := True;
            when Noted   => Has_Noted   := True;
            when Safe    => null;
         end case;
         --  Loop invariant: Has_Reject iff ∃ j ≤ i with Usages(j)=Reject
         pragma Loop_Invariant
           (Has_Reject =
            (for some J in Usages'First .. I => Usages (J) = Reject));
      end loop;

      if Has_Reject then
         return Policy_Rejected;
      elsif Has_Warning then
         return Policy_Incomplete;
      elsif Has_Noted then
         return Policy_Classical;
      else
         return Policy_Clean;
      end if;
   end Enforce;

end Axiom_Policy;
