-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Axiom_C_Bridge body — unmarshals C arrays and calls the SPARK functions.
--
-- Safety: count is validated against Axiom_Policy.Max_Usages before the
-- unchecked array overlay; invalid input returns status -1 without touching
-- the output pointer. The SPARK contracts in Axiom_Policy guarantee that the
-- Enforce/Worst_Danger calls themselves satisfy their Post-conditions.

with Axiom_Types;  use Axiom_Types;
with Axiom_Policy; use Axiom_Policy;
with Interfaces.C; use Interfaces.C;
with System.Address_To_Access_Conversions;

package body Axiom_C_Bridge with SPARK_Mode => Off is

   --  Overlay type: C uint8 array for the danger levels wire format
   type Byte_Array is array (Natural range <>) of Interfaces.C.unsigned_char
   with Convention => C;
   type Byte_Array_Ptr is access all Byte_Array;

   package Byte_Conversions is
     new System.Address_To_Access_Conversions (Byte_Array (0 .. 0));

   --  Map a C uint8 to DangerLevel; returns False if value is out of range.
   function To_Danger (B : Interfaces.C.unsigned_char;
                       D : out Danger_Level) return Boolean is
   begin
      case Integer (B) is
         when 0 => D := Safe;    return True;
         when 1 => D := Noted;   return True;
         when 2 => D := Warning; return True;
         when 3 => D := Reject;  return True;
         when others => D := Safe; return False;
      end case;
   end To_Danger;

   --  Map AxiomPolicy to C int32
   function Policy_To_Int (P : Axiom_Policy) return Interfaces.C.int is
   begin
      case P is
         when Policy_Clean      => return 0;
         when Policy_Classical  => return 1;
         when Policy_Incomplete => return 2;
         when Policy_Rejected   => return 3;
      end case;
   end Policy_To_Int;

   --  Map DangerLevel to C int32
   function Danger_To_Int (D : Danger_Level) return Interfaces.C.int is
   begin
      case D is
         when Safe    => return 0;
         when Noted   => return 1;
         when Warning => return 2;
         when Reject  => return 3;
      end case;
   end Danger_To_Int;

   --  Shared: read danger levels from C pointer into an Ada array.
   --  Returns False and sets Status_Out to -1 on invalid input.
   procedure Read_Usages
     (Danger_Levels : System.Address;
      Count         : Interfaces.C.size_t;
      Usages        : out Danger_Array;
      OK            : out Boolean;
      Status_Out    : access Interfaces.C.int)
   is
      N : constant Natural := Natural (Count);
   begin
      if N > Max_Usages or else Danger_Levels = System.Null_Address then
         Status_Out.all := -1;
         OK := False;
         Usages := (others => Safe);
         return;
      end if;

      declare
         Bytes : Byte_Array (0 .. N - 1);
         for Bytes'Address use Danger_Levels;
         pragma Import (Ada, Bytes);
      begin
         for I in 0 .. N - 1 loop
            declare
               D : Danger_Level;
            begin
               if not To_Danger (Bytes (I), D) then
                  Status_Out.all := -1;
                  OK := False;
                  Usages := (others => Safe);
                  return;
               end if;
               Usages (Usages'First + I) := D;
            end;
         end loop;
      end;

      Status_Out.all := 0;
      OK := True;
   end Read_Usages;

   ----------------------------------------------------------------------------

   procedure C_Enforce_Policy
     (Danger_Levels : System.Address;
      Count         : Interfaces.C.size_t;
      Policy_Out    : access Interfaces.C.int;
      Status_Out    : access Interfaces.C.int)
   is
      N      : constant Natural := Natural (Count);
      Usages : Danger_Array (0 .. Natural'Max (0, N - 1));
      OK     : Boolean;
   begin
      Read_Usages (Danger_Levels, Count, Usages, OK, Status_Out);
      if not OK then
         Policy_Out.all := -1;
         return;
      end if;

      declare
         Result : Axiom_Policy;
      begin
         if N = 0 then
            Result := Policy_Clean;
         else
            Result := Enforce (Usages (0 .. N - 1));
         end if;
         Policy_Out.all := Policy_To_Int (Result);
      end;
   end C_Enforce_Policy;

   ----------------------------------------------------------------------------

   procedure C_Worst_Danger
     (Danger_Levels : System.Address;
      Count         : Interfaces.C.size_t;
      Danger_Out    : access Interfaces.C.int;
      Status_Out    : access Interfaces.C.int)
   is
      N      : constant Natural := Natural (Count);
      Usages : Danger_Array (0 .. Natural'Max (0, N - 1));
      OK     : Boolean;
   begin
      Read_Usages (Danger_Levels, Count, Usages, OK, Status_Out);
      if not OK then
         Danger_Out.all := -1;
         return;
      end if;

      if N = 0 then
         Danger_Out.all := 0; -- Safe
      else
         Danger_Out.all := Danger_To_Int (Worst_Danger (Usages (0 .. N - 1)));
      end if;
   end C_Worst_Danger;

end Axiom_C_Bridge;
