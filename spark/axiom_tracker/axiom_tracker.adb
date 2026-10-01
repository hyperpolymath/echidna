-- SPDX-License-Identifier: MPL-2.0
--
-- SPARK companion body for axiom_tracker.ads
--
-- Implementation strategy for Enforce_Policy
-- -------------------------------------------
-- Single forward scan with three boolean accumulators.  A Loop_Invariant
-- after each iteration re-establishes the exact relationship between each
-- boolean and the elements seen so far.  At loop exit (I = Usages'Last)
-- the invariant collapses to the full-range quantifier in the post-condition,
-- so gnatprove can close each branch without additional lemmas.

pragma Ada_2022;

package body Axiom_Tracker
  with SPARK_Mode => On
is

   function Enforce_Policy (Usages : Usage_Array) return Axiom_Policy is
      Has_Reject  : Boolean := False;
      Has_Warning : Boolean := False;
      Has_Noted   : Boolean := False;
   begin
      for I in Usages'Range loop
         case Usages (I).Danger is
            when Reject  => Has_Reject  := True;
            when Warning => Has_Warning := True;
            when Noted   => Has_Noted   := True;
            when Safe    => null;
         end case;

         -- The invariant is a running snapshot: each boolean equals the
         -- disjunction of the matching condition over elements First..I.
         -- At I = Last this is the full-range quantifier in the spec.
         pragma Loop_Invariant
           (Has_Reject  = (for some J in Usages'First .. I =>
                             Usages (J).Danger = Reject)
            and then
            Has_Warning = (for some J in Usages'First .. I =>
                             Usages (J).Danger = Warning)
            and then
            Has_Noted   = (for some J in Usages'First .. I =>
                             Usages (J).Danger = Noted));
      end loop;

      -- Priority: Reject > Warning > Noted > Clean.
      -- Mirrors the if-chain in AxiomTracker::enforce_policy (Rust).
      if Has_Reject then
         return (Kind => Rejected);
      elsif Has_Warning then
         return (Kind => Incomplete_Proof);
      elsif Has_Noted then
         return (Kind => Classical_Axioms);
      else
         return (Kind => Clean);
      end if;
   end Enforce_Policy;

   function Is_Acceptable (P : Axiom_Policy) return Boolean is
   begin
      return P.Kind /= Rejected;
   end Is_Acceptable;

   function Worst_Danger (P : Axiom_Policy) return Danger_Level is
   begin
      case P.Kind is
         when Clean            => return Safe;
         when Classical_Axioms => return Noted;
         when Incomplete_Proof => return Warning;
         when Rejected         => return Reject;
      end case;
   end Worst_Danger;

end Axiom_Tracker;
