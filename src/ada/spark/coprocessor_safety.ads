-- SPDX-License-Identifier: PMPL-1.0-or-later
-- (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
--
-- Coprocessor_Safety — SPARK-verified invariants on coprocessor trust-tier
-- ordering and self-sufficiency classification.
--
-- Mirrors:
--   src/rust/coprocessor/trust.rs           (CoprocessorTrustTier)
--   src/abi/CoprocessorForeign.idr          (CoprocessorTrustTier + isSelfSufficient)
--
-- The two soundness obligations GNATprove discharges automatically:
--
--   1. Order_Preserved — the strict total order on tiers is preserved by
--      the u8 encoding (Tier ordering matches numeric ordering).
--
--   2. Self_Sufficient_Iff_Tier_Ge_3 — Is_Self_Sufficient (T) holds iff
--      T's discriminant is at least Library_Wrapped (3).  This is the
--      gate the prover-side trust pipeline checks before folding a
--      coprocessor result into a high-trust verdict.
--
-- The C-ABI bridge in `coprocessor_c_bridge.ads` (added with the Phase 6
-- libechidna_coprocessor surface) will wrap `Is_Self_Sufficient` for the
-- Rust side; for now the SPARK contracts stand on their own and document
-- the invariants the Rust side must obey.

package Coprocessor_Safety with SPARK_Mode => On is

   --  -----------------------------------------------------------------------
   --  Trust tier  (Rust: CoprocessorTrustTier, repr(u8))
   --
   --  Order: External_Subprocess < Julia_Bridged < Library_Wrapped
   --       < Native_Kernel < Pure_Formal
   --
   --  Discriminants pinned to match Rust + Idris2 + Zig:
   --    External_Subprocess = 1
   --    Julia_Bridged       = 2
   --    Library_Wrapped     = 3
   --    Native_Kernel       = 4
   --    Pure_Formal         = 5
   --  -----------------------------------------------------------------------
   type Trust_Tier is
     (External_Subprocess,
      Julia_Bridged,
      Library_Wrapped,
      Native_Kernel,
      Pure_Formal);

   for Trust_Tier use
     (External_Subprocess => 1,
      Julia_Bridged       => 2,
      Library_Wrapped     => 3,
      Native_Kernel       => 4,
      Pure_Formal         => 5);

   --  -----------------------------------------------------------------------
   --  Is_Self_Sufficient
   --
   --  A tier is self-sufficient iff its result can stand alone in the
   --  prover-side trust pipeline without an independent cross-check.
   --  Library_Wrapped (Tier 3) and above qualify; Julia_Bridged and
   --  External_Subprocess require cross-validation.
   --
   --  Proven Post: result ⇔ T ≥ Library_Wrapped.
   --  -----------------------------------------------------------------------
   function Is_Self_Sufficient (T : Trust_Tier) return Boolean
   with
     Post => Is_Self_Sufficient'Result = (T >= Library_Wrapped);

   --  -----------------------------------------------------------------------
   --  Encode / Decode
   --
   --  Round-trip property: Decode (Encode (T)) = T for every T.
   --  Mirrors `encodeDecodeId` in CoprocessorForeign.idr.
   --  -----------------------------------------------------------------------
   subtype Tier_Code is Natural range 1 .. 5;

   function Encode (T : Trust_Tier) return Tier_Code
   with
     Post => Encode'Result = Trust_Tier'Pos (T) + 1;

   function Decode (C : Tier_Code) return Trust_Tier
   with
     Post => Trust_Tier'Pos (Decode'Result) + 1 = C;

end Coprocessor_Safety;
