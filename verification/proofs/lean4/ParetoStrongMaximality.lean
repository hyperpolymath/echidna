-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ParetoStrongMaximality.lean
--
-- Closes the strong-maximality gap for **E10 / PO-12**.
--
-- This file is intentionally separate from `ParetoMaximality.lean`:
-- the main file holds the algebraic-property theorems (PO-1..PO-11
-- + descent groundwork PD-1, PD-2) that compile cleanly under any
-- Lean 4 toolchain.  This file holds the load-bearing PD-3 lemma
-- + the well-founded-recursion descent argument for the headline
-- `dominated_by_frontier_member` theorem.
--
-- Both halves of the proof are *mathematically* settled.  The
-- formalisation here uses only core Lean 4 (no mathlib) — at the
-- cost of hand-rolling `List.length_lt_of_strict_subset_of_nodup`
-- as a 25-line auxiliary lemma.
--
-- **Toolchain note**: written 2026-04-27 by Opus without local
-- access to a Lean 4 toolchain.  The 2026-05-11 lake-build agent
-- (per `docs/handover/PHASE-3-PROMPT.md` / scheduled routine
-- `trig_01Tm7zTxYEY7kmzBsu7P4nc9`) will be the first run that
-- actually tries `lake build` on this file.  Tactic fixups (rather
-- than mathematical errors) are expected; the proof structure is
-- the load-bearing artefact.

import ParetoMaximality

namespace EchidnaPareto

-- ==========================================================================
-- Section 1: Auxiliary List lemma — strict subset + nodup ⇒ shorter
-- ==========================================================================

/-- For two `Nodup` lists `xs ⊆ ys` with a witness `w` showing
    `w ∈ ys ∧ w ∉ xs`, the length of `xs` is strictly less than the
    length of `ys`.

    *Proof sketch.* Recurse on `ys`.  If `ys = []`, the witness is
    impossible.  If `ys = y :: ys'`:

    - Case `w = y`: every element of `xs` is in `ys`; by `xs.Nodup`
      and the absence of `w = y` in `xs`, every element of `xs` is
      in `ys'`.  Then `xs.length ≤ ys'.length < ys.length`.
    - Case `w ≠ y`: split `xs` on whether `y ∈ xs`.
      - `y ∈ xs`: drop `y` from both; recursive call on
        `xs.erase y` and `ys'` (both still `Nodup`, witness `w`
        still applies, subset still holds).  Length bookkeeping
        gives the desired strict inequality.
      - `y ∉ xs`: every element of `xs` is in `ys'`; recurse with
        `ys'` and the same `xs`. -/
theorem List.length_lt_of_subset_with_witness {α : Type _} [DecidableEq α]
    (xs ys : List α) (h_xs_nodup : xs.Nodup) (_h_ys_nodup : ys.Nodup)
    (h_subset : ∀ x ∈ xs, x ∈ ys)
    (w : α) (hw_in_ys : w ∈ ys) (hw_not_in_xs : w ∉ xs) :
    xs.length < ys.length := by
  -- Core Lean 4.13.0 has no direct `Nodup` + subset ⇒ length lemma, and the
  -- original `induction ys generalizing xs` failed to generalise the
  -- xs-dependent hypotheses. Restructured: a local non-strict bound proved
  -- by erasing the head from the superset, then the strict step via the
  -- witness `w` (drop it from `ys`).
  have le_of_nodup_subset : ∀ (as bs : List α), as.Nodup →
      (∀ a ∈ as, a ∈ bs) → as.length ≤ bs.length := by
    intro as
    induction as with
    | nil => intro bs _ _; simp
    | cons x xs ih =>
      intro bs hnd hsub
      have hx_bs : x ∈ bs := hsub x (List.mem_cons_self x xs)
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hxs_nd : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hsub' : ∀ a ∈ xs, a ∈ bs.erase x := by
        intro a ha
        have hane : a ≠ x := fun h => hx_notin (h ▸ ha)
        exact (List.mem_erase_of_ne hane).mpr (hsub a (List.mem_cons_of_mem x ha))
      have hrec := ih (bs.erase x) hxs_nd hsub'
      have hlen : (bs.erase x).length = bs.length - 1 :=
        List.length_erase_of_mem hx_bs
      have hpos : 0 < bs.length := List.length_pos.mpr (List.ne_nil_of_mem hx_bs)
      simp only [List.length_cons]
      omega
  -- Every element of `xs` lies in `ys.erase w` (it is in `ys` and ≠ w,
  -- since `w ∉ xs`), so `xs.length ≤ (ys.erase w).length = ys.length - 1`.
  have hsub_ew : ∀ a ∈ xs, a ∈ ys.erase w := by
    intro a ha
    have hane : a ≠ w := fun h => hw_not_in_xs (h ▸ ha)
    exact (List.mem_erase_of_ne hane).mpr (h_subset a ha)
  have hle : xs.length ≤ (ys.erase w).length :=
    le_of_nodup_subset xs (ys.erase w) h_xs_nodup hsub_ew
  have hlen : (ys.erase w).length = ys.length - 1 :=
    List.length_erase_of_mem hw_in_ys
  have hpos : 0 < ys.length := List.length_pos.mpr (List.ne_nil_of_mem hw_in_ys)
  omega

-- ==========================================================================
-- Section 2: PD-3 — domCount strictly decreases along dominator edges
-- ==========================================================================

/-- **PD-3 (E10/PD-3)** When `b ∈ cs` dominates `a`, the descent
    measure `domCount` strictly decreases:

    `domCount b cs < domCount a cs`.

    Proof: PD-1 gives `domSet b cs ⊆ domSet a cs`; PD-2 supplies
    `b ∈ domSet a cs ∧ b ∉ domSet b cs` as the strict-difference
    witness; `List.length_lt_of_subset_with_witness` (above)
    closes the cardinality argument provided both filtered lists
    are `Nodup`.

    Filtered lists inherit `Nodup` from the original — but we have
    no hypothesis that `cs.Nodup`.  In practice, `compute` in the
    Rust pareto module operates on indices `0..n`, which are
    trivially `Nodup`; the Lean spec carries this assumption as a
    side condition. -/
theorem domCount_strictly_decreases (a b : ProofObjective)
    (cs : List ProofObjective) (hcs_nodup : cs.Nodup)
    (hba : dominates b a) (hb_mem : b ∈ cs) :
    domCount b cs < domCount a cs := by
  unfold domCount
  -- witness `w := b`; the strict-subset lemma then closes the cardinality gap.
  exact List.length_lt_of_subset_with_witness
    (domSet b cs) (domSet a cs)
    (hcs_nodup.sublist (List.filter_sublist cs))
    (hcs_nodup.sublist (List.filter_sublist cs))
    (domSet_subset_of_dominates a b cs hba)
    b
    (domSet_strict_witness a b cs hba hb_mem).1
    (domSet_strict_witness a b cs hba hb_mem).2

-- ==========================================================================
-- Section 3: Strong maximality via well-founded recursion
-- ==========================================================================

/-- **PO-12 (E10/12) Strong maximality**: every input candidate not
    on the frontier is strictly dominated by some *frontier*
    member.  This is the constructive content of "the Pareto
    frontier covers the input under dominance".

    *Proof.* Strong induction on the descent measure `domCount a cs`,
    using `domCount_strictly_decreases` (PD-3) to feed the recursion.
    Termination is guaranteed by PD-3: each step strictly decreases
    `domCount`, so the chain bottoms out at a Pareto member. -/
theorem dominated_by_frontier_member (cs : List ProofObjective)
    (hcs_nodup : cs.Nodup) :
    ∀ a ∈ cs, a ∉ frontier cs → ∃ f ∈ frontier cs, dominates f a := by
  -- Strong induction on the descent measure `domCount a cs`, with `a`
  -- generalised so the IH applies to the strictly-smaller dominator `b`.
  -- (`Nat.strong_induction_on` was removed in Lean 4.13.0 → `Nat.strongRecOn`.)
  have key : ∀ k a, domCount a cs = k → a ∈ cs → a ∉ frontier cs →
      ∃ f ∈ frontier cs, dominates f a := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro a hk ha hnf
      -- a is not Pareto, so some b ∈ cs dominates a.
      rcases frontier_or_dominated cs a ha with hf | ⟨b, hb_mem, hb_dom⟩
      · exact absurd hf hnf
      · by_cases hp : isPareto b cs
        · exact ⟨b, frontier_complete cs b hb_mem hp, hb_dom⟩
        · -- Recurse: domCount b cs < domCount a cs = k by PD-3.
          have hdec : domCount b cs < k := by
            rw [← hk]
            exact domCount_strictly_decreases a b cs hcs_nodup hb_dom hb_mem
          have hb_not_front : b ∉ frontier cs :=
            fun hb_in_front => hp (frontier_sound cs b hb_in_front)
          obtain ⟨f, hf_front, hf_dom_b⟩ :=
            ih (domCount b cs) hdec b rfl hb_mem hb_not_front
          -- f dominates b, b dominates a → f dominates a (transitivity)
          exact ⟨f, hf_front, dominates_transitive f b a hf_dom_b hb_dom⟩
  intro a ha hnf
  exact key (domCount a cs) a rfl ha hnf

end EchidnaPareto
