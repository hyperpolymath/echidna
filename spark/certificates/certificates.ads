-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- SPARK companion spec for src/rust/verification/certificates.rs
--
-- Proved properties
--   1. Get_Format_Extension is total over Certificate_Format and injective.
--   2. Check_Alethe_Step is the exact boolean characterisation of the Rust
--      structural validator:
--        - Assume step: valid iff raw is non-empty
--        - Step      step: valid iff raw has the :rule marker
--      (Issue #40 roadmap obligation: "Alethe / DRAT / TSTP / OpenTheory
--      cert parsing — totality + reject-malformed".  The totality piece
--      is Get_Format_Extension; reject-malformed is encoded by the
--      check predicates + Cap_At_Malformed below.)
--   3. Verify_Alethe returns true iff every step in the input array
--      passes Check_Alethe_Step (cap-at-malformed monotonicity).
--   4. Cap_At_Malformed (ghost): any malformed step ⇒ Verify_Alethe = False.
--   5. Empty_Verifies (ghost): empty input ⇒ Verify_Alethe = True (vacuous
--      quantifier over an empty range).
--
-- SPARK doesn't model strings, subprocess, or external checkers, so the
-- DRAT/LRAT/Lean4/Coq paths (which shell out to drat-trim / lean4checker /
-- coqchk) are outside this companion's scope.  This companion mirrors the
-- pure-decision Alethe structural validator and the format-extension
-- mapping — the parts of certificates.rs that are purely deterministic
-- functions of their inputs and have no IO surface.

pragma Ada_2022;

package Certificates
  with SPARK_Mode => On
is
   -- ── CertificateFormat ──────────────────────────────────────────────
   -- Mirrors Rust enum CertificateFormat (Rust line 20-33).  Same
   -- positional order so Ada and Rust integer encodings agree.
   type Certificate_Format is
     (Alethe, DRAT, LRAT, Lean4_Kernel, Coq_Kernel, TSTP);

   -- ── Format extensions ──────────────────────────────────────────────
   -- Rust format_extension returns `&str` literals.  SPARK doesn't model
   -- strings ergonomically, so we map each format to a tagged extension
   -- enum.  Injectivity is then expressible via the case post-condition.
   type Format_Extension is
     (Ext_Alethe, Ext_Drat, Ext_Lrat, Ext_Lean4cert, Ext_Coqcert, Ext_Tstp);

   function Get_Format_Extension (F : Certificate_Format)
                                  return Format_Extension
     with Post =>
       (case F is
          when Alethe       => Get_Format_Extension'Result = Ext_Alethe,
          when DRAT         => Get_Format_Extension'Result = Ext_Drat,
          when LRAT         => Get_Format_Extension'Result = Ext_Lrat,
          when Lean4_Kernel => Get_Format_Extension'Result = Ext_Lean4cert,
          when Coq_Kernel   => Get_Format_Extension'Result = Ext_Coqcert,
          when TSTP         => Get_Format_Extension'Result = Ext_Tstp);

   -- ── AletheStepKind ─────────────────────────────────────────────────
   -- Mirrors Rust private enum AletheStepKind (Rust line 274).
   type Alethe_Step_Kind is (Assume, Step);

   -- ── AletheStep (abstracted) ────────────────────────────────────────
   -- The Rust struct carries the raw string.  SPARK can't reason about
   -- arbitrary strings, so we abstract to two boolean attributes that
   -- the Rust predicate Check_Alethe_Step consumes:
   --   Raw_Is_Nonempty -- `!step.raw.is_empty()`
   --   Has_Rule_Marker -- `raw.contains(":rule") && raw.starts_with("(step")`
   -- A string-to-AletheStep adapter on the Rust side (not modeled here)
   -- computes these two booleans at parse time.
   type Alethe_Step is record
      Kind            : Alethe_Step_Kind := Assume;
      Raw_Is_Nonempty : Boolean          := False;
      Has_Rule_Marker : Boolean          := False;
   end record;

   -- ── Check_Alethe_Step ──────────────────────────────────────────────
   -- Mirrors check_alethe_step (Rust line 226-234).  Expression function
   -- so the body IS the post-condition.
   function Check_Alethe_Step (S : Alethe_Step) return Boolean is
     (case S.Kind is
        when Assume => S.Raw_Is_Nonempty,
        when Step   => S.Has_Rule_Marker);

   -- ── Bounded step array ─────────────────────────────────────────────
   -- Mirrors the Vec<AletheStep> produced by parse_alethe_steps.  65 536
   -- caps Alethe proofs at an industrial scale (most CVC5 proofs run in
   -- the hundreds-to-thousands range).
   Max_Steps : constant := 65_536;
   subtype Step_Index is Positive range 1 .. Max_Steps;
   type Step_Array is array (Step_Index range <>) of Alethe_Step;

   -- ── Verify_Alethe ──────────────────────────────────────────────────
   -- Mirrors verify_alethe (Rust line 93-124): the result is valid iff
   -- every step passes Check_Alethe_Step.  Expression function — body
   -- IS the post-condition; gnatprove discharges directly without VCs.
   function Verify_Alethe (Steps : Step_Array) return Boolean is
     (for all I in Steps'Range => Check_Alethe_Step (Steps (I)));

   -- ── Has_Malformed (ghost) ──────────────────────────────────────────
   function Has_Malformed (Steps : Step_Array) return Boolean is
     (for some I in Steps'Range => not Check_Alethe_Step (Steps (I)))
     with Ghost;

   -- ── Cap_At_Malformed (ghost lemma) ─────────────────────────────────
   -- Cap-at-malformed monotonicity: any single malformed step forces
   -- the whole certificate to be rejected.  Mirrors axiom_tracker's
   -- cap-at-Reject and solver_integrity's cap-at-Tampered.
   --
   -- Proof: Has_Malformed (S) ≡ (exists I, ¬Check_Alethe_Step (S(I)))
   --                          ≡ ¬(forall I, Check_Alethe_Step (S(I)))
   --                          ≡ ¬Verify_Alethe (S).
   procedure Cap_At_Malformed (Steps : Step_Array)
     with Ghost,
          Pre  => Has_Malformed (Steps),
          Post => not Verify_Alethe (Steps);

   -- ── Empty_Verifies (ghost lemma) ───────────────────────────────────
   -- An empty proof is vacuously valid: the universal quantifier over
   -- an empty range is True.  Stated explicitly to document the
   -- pathological-but-correct edge case (parse_alethe_steps strips all
   -- comments + empty lines; pure-comment input yields zero steps).
   procedure Empty_Verifies (Steps : Step_Array)
     with Ghost,
          Pre  => Steps'Length = 0,
          Post => Verify_Alethe (Steps);

   -- ── Format_Extension_Is_Injective (ghost lemma) ────────────────────
   -- Distinct certificate formats map to distinct extensions.  Documents
   -- the storage-path uniqueness property used by store_certificate
   -- (Rust line 182): different formats yield different filenames, so
   -- two certificates of different formats never collide on disk.
   procedure Format_Extension_Is_Injective
     (F1, F2 : Certificate_Format)
     with Ghost,
          Pre  => F1 /= F2,
          Post => Get_Format_Extension (F1) /= Get_Format_Extension (F2);

end Certificates;
