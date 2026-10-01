-- SPDX-License-Identifier: MPL-2.0
--
-- SPARK companion body for certificates.ads
--
-- Implementation strategy
-- -----------------------
-- Most subprograms are expression functions defined in the spec, so the
-- body contains only:
--   - Get_Format_Extension's case body (mirroring Rust format_extension)
--   - The three ghost lemmas with null bodies; gnatprove derives their
--     conclusions by quantifier instantiation + the definitional
--     equivalences in the spec.

pragma Ada_2022;

package body Certificates
  with SPARK_Mode => On
is

   function Get_Format_Extension (F : Certificate_Format)
                                  return Format_Extension is
   begin
      case F is
         when Alethe       => return Ext_Alethe;
         when DRAT         => return Ext_Drat;
         when LRAT         => return Ext_Lrat;
         when Lean4_Kernel => return Ext_Lean4cert;
         when Coq_Kernel   => return Ext_Coqcert;
         when TSTP         => return Ext_Tstp;
      end case;
   end Get_Format_Extension;

   -- ── Cap_At_Malformed ───────────────────────────────────────────────
   -- Ghost lemma: derived from definitions of Has_Malformed +
   -- Verify_Alethe (both in spec).  Body is null; gnatprove closes
   -- via quantifier duality (¬∀x.P(x) ↔ ∃x.¬P(x)).
   procedure Cap_At_Malformed (Steps : Step_Array) is
   begin
      null;
   end Cap_At_Malformed;

   -- ── Empty_Verifies ─────────────────────────────────────────────────
   -- Ghost lemma: vacuous-quantifier over an empty range.  gnatprove
   -- recognises the empty range and closes immediately.
   procedure Empty_Verifies (Steps : Step_Array) is
   begin
      null;
   end Empty_Verifies;

   -- ── Format_Extension_Is_Injective ──────────────────────────────────
   -- Ghost lemma: case-by-case on F1 (six values), and within each case
   -- the case-arm post of Get_Format_Extension pins down the result, so
   -- F2 /= F1 forces the other arm to be taken, yielding a different
   -- Format_Extension.  gnatprove discharges by exhaustive case-split.
   procedure Format_Extension_Is_Injective
     (F1, F2 : Certificate_Format) is
   begin
      null;
   end Format_Extension_Is_Injective;

end Certificates;
