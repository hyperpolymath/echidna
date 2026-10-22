--  SPDX-License-Identifier: MPL-2.0
--  Body side of the spark_ada smoke fixture.

package body Smoke with SPARK_Mode is

   procedure Clamp (X : Integer; Lo, Hi : Integer; R : out Integer) is
   begin
      if X < Lo then
         R := Lo;
      elsif X > Hi then
         R := Hi;
      else
         R := X;
      end if;
   end Clamp;

   procedure Lemma_Clamp_Bounds (X : Integer; Lo, Hi : Integer) is null;

   procedure Trusted_Step (X : Integer) is
      pragma Assume (X in Integer'First .. Integer'Last);
   begin
      null;
   end Trusted_Step;

end Smoke;
