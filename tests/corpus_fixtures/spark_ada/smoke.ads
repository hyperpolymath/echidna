--  SPDX-License-Identifier: MPL-2.0
--  Smoke fixture for the spark_ada corpus adapter.
--
--  Covers: a package spec, a proved contract (Pre/Post), a Ghost
--  sparklib lemma, and a procedure whose contract is only an assumption.

package Smoke with SPARK_Mode is

   --  Proved contract: GNATprove can discharge both clauses.
   procedure Clamp (X : Integer; Lo, Hi : Integer; R : out Integer)
     with Pre  => Lo <= Hi,
          Post => R in Lo .. Hi;

   --  sparklib convention: a Ghost Lemma_* memoises a fact.
   procedure Lemma_Clamp_Bounds (X : Integer; Lo, Hi : Integer)
     with Ghost,
          Pre  => Lo <= Hi and then X in Lo .. Hi,
          Post => X in Lo .. Hi;

   --  The body of this one asserts its own precondition without proof;
   --  corpus_estate_adapter.rs checks that the body side is flagged.
   procedure Trusted_Step (X : Integer) with Post => X = X;

   type Word is mod 2 ** 32;

end Smoke;
