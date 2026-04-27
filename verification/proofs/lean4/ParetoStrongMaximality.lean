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

import EchidnaPareto.ParetoMaximality

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
theorem List.length_lt_of_subset_with_witness {α : Type*} [DecidableEq α]
    (xs ys : List α) (h_xs_nodup : xs.Nodup) (h_ys_nodup : ys.Nodup)
    (h_subset : ∀ x ∈ xs, x ∈ ys)
    (w : α) (hw_in_ys : w ∈ ys) (hw_not_in_xs : w ∉ xs) :
    xs.length < ys.length := by
  induction ys generalizing xs with
  | nil =>
    -- ys = []: hw_in_ys says w ∈ [], impossible.
    exact absurd hw_in_ys (List.not_mem_nil w)
  | cons y ys' ih =>
    -- Use Nodup of (y :: ys') to get y ∉ ys' and ys'.Nodup
    have hy_not_in_ys' : y ∉ ys' := List.Nodup.not_mem h_ys_nodup
    have h_ys'_nodup : ys'.Nodup := List.Nodup.of_cons h_ys_nodup
    -- Case-split on y ∈ xs.
    by_cases hy_in_xs : y ∈ xs
    · -- y ∈ xs: shrink both lists.
      let xs' := xs.erase y
      have h_xs'_nodup : xs'.Nodup := List.Nodup.erase y h_xs_nodup
      have h_xs'_subset : ∀ x ∈ xs', x ∈ ys' := by
        intro x hx
        have hx_in_xs : x ∈ xs := List.mem_of_mem_erase hx
        have hx_ne_y : x ≠ y := by
          intro heq
          rw [heq] at hx
          exact (List.Nodup.not_mem_erase h_xs_nodup) hx
        have hx_in_yys' : x ∈ y :: ys' := h_subset x hx_in_xs
        rcases List.mem_cons.mp hx_in_yys' with h | h
        · exact absurd h hx_ne_y
        · exact h
      -- Witness: w is still in ys' (we know w ≠ y because hw_not_in_xs vs hy_in_xs)
      have hw_ne_y : w ≠ y := by
        intro heq; rw [heq] at hw_not_in_xs; exact hw_not_in_xs hy_in_xs
      have hw_in_ys' : w ∈ ys' := by
        rcases List.mem_cons.mp hw_in_ys with h | h
        · exact absurd h hw_ne_y
        · exact h
      have hw_not_in_xs' : w ∉ xs' := by
        intro h
        exact hw_not_in_xs (List.mem_of_mem_erase h)
      -- Recursive call
      have ih_app : xs'.length < ys'.length :=
        ih xs' h_xs'_nodup h_ys'_nodup h_xs'_subset w hw_in_ys' hw_not_in_xs'
      -- xs.length = xs'.length + 1 (since y ∈ xs and xs.Nodup)
      have h_xs_len : xs.length = xs'.length + 1 :=
        List.length_erase_of_mem hy_in_xs |>.symm ▸ by simp [xs']; omega
      -- ys.length = ys'.length + 1
      have h_ys_len : (y :: ys').length = ys'.length + 1 := by
        simp [List.length_cons]
      rw [h_xs_len, h_ys_len]
      omega
    · -- y ∉ xs: xs is fully a sublist of ys'.
      have h_xs_subset_ys' : ∀ x ∈ xs, x ∈ ys' := by
        intro x hx
        have hx_in_yys' : x ∈ y :: ys' := h_subset x hx
        have hx_ne_y : x ≠ y := fun heq => hy_in_xs (heq ▸ hx)
        rcases List.mem_cons.mp hx_in_yys' with h | h
        · exact absurd h hx_ne_y
        · exact h
      -- Decide: is the witness w in ys'?
      have hw_ne_y_or : w = y ∨ w ≠ y := Decidable.em _
      rcases hw_ne_y_or with hw_eq_y | hw_ne_y
      · -- w = y: subset xs ⊆ ys' is the strict-shorter proof since
        -- y ∈ ys but y ∉ xs and y ∉ ys'.
        have h_xs_le_ys' : xs.length ≤ ys'.length :=
          List.Sublist.length_le
            (List.sublist_of_subset_of_nodup h_xs_subset_ys' h_xs_nodup h_ys'_nodup)
        have : (y :: ys').length = ys'.length + 1 := by simp [List.length_cons]
        rw [this]
        omega
      · -- w ≠ y: recurse on ys'.
        have hw_in_ys' : w ∈ ys' := by
          rcases List.mem_cons.mp hw_in_ys with h | h
          · exact absurd h hw_ne_y
          · exact h
        have ih_app : xs.length < ys'.length :=
          ih xs h_xs_nodup h_ys'_nodup h_xs_subset_ys' w hw_in_ys' hw_not_in_xs
        have : (y :: ys').length = ys'.length + 1 := by simp [List.length_cons]
        rw [this]
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
  apply List.length_lt_of_subset_with_witness
    (domSet b cs) (domSet a cs)
  · -- (domSet b cs).Nodup follows from cs.Nodup via filter preservation
    exact List.Nodup.filter _ hcs_nodup
  · exact List.Nodup.filter _ hcs_nodup
  · exact domSet_subset_of_dominates a b cs hba
  · exact b
  · exact (domSet_strict_witness a b cs hba hb_mem).1
  · exact (domSet_strict_witness a b cs hba hb_mem).2

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
  -- Strong induction on `domCount a cs`.
  intro a
  induction hk : domCount a cs using Nat.strong_induction_on with
  | _ k ih =>
    intro ha hnf
    -- a is not Pareto, so some b ∈ cs dominates a.
    rcases frontier_or_dominated cs a ha with hf | ⟨b, hb_mem, hb_dom⟩
    · exact absurd hf hnf
    -- Either b is Pareto (done) or recurse on b with smaller domCount.
    by_cases hp : isPareto b cs
    · exact ⟨b, frontier_complete cs b hb_mem hp, hb_dom⟩
    · -- Recurse: domCount b cs < domCount a cs by PD-3.
      have hdec : domCount b cs < k := by
        rw [← hk]
        exact domCount_strictly_decreases a b cs hcs_nodup hb_dom hb_mem
      have hb_not_front : b ∉ frontier cs := by
        intro hb_in_front
        exact hp (frontier_sound cs b hb_in_front)
      obtain ⟨f, hf_front, hf_dom_b⟩ :=
        ih (domCount b cs) hdec b rfl hb_mem hb_not_front
      -- f dominates b, b dominates a → f dominates a (transitivity)
      exact ⟨f, hf_front, dominates_transitive f b a hf_dom_b hb_dom⟩

end EchidnaPareto
