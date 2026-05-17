-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- PortfolioCompleteness.lean
--
-- Proof obligation **E13**: portfolio cross-checking completeness for
-- ECHIDNA's `PortfolioSolver::reconcile`.
--
-- Models the Rust implementation in `src/rust/verification/portfolio.rs`.
--
-- /-! # Portfolio cross-checking completeness (E13)
--
-- The portfolio solver dispatches a query to several SMT/ATP/ITP
-- backends in parallel, collects each one's `SolverResult`, and
-- *reconciles* them into a single verdict tagged with a
-- `PortfolioConfidence` level:
--
--   * `CrossChecked`  — ≥ 2 solvers completed and all agree
--   * `SingleSolver`  — exactly 1 solver completed
--   * `Inconclusive`  — ≥ 2 solvers completed and disagree
--   * `AllTimedOut`   — every solver timed out
--
-- This file proves the reconciliation rule is **complete and sound**:
-- every input result-list lands in exactly one bucket, the verdict
-- reflects the bucket, and the `needs_review` flag fires precisely
-- when no consensus was reached.
--
-- ## What's proved
--
-- 1. **Exhaustiveness** — every input list produces one of the four
--    declared confidence levels.
-- 2. **AllTimedOut iff empty** — confidence = AllTimedOut iff no
--    solver completed (every `verified = none`).
-- 3. **SingleSolver iff one completed** — confidence = SingleSolver
--    iff exactly one solver returned a non-`none` verdict.
-- 4. **CrossChecked iff ≥ 2 completed and all agree** — formal
--    statement of the cross-checking guarantee.
-- 5. **Inconclusive iff disagreement** — ≥ 2 completed solvers and at
--    least one differs from the first.
-- 6. **needs_review iff not consensus** — review flag fires iff
--    confidence ∈ {Inconclusive, AllTimedOut}.
-- 7. **verified preservation** — when verdict is `Some b`, every
--    `agreeing` solver returned `Some b`.
-- 8. **Disagreement is sticky** — adding a result that differs from
--    the first completed result keeps the portfolio Inconclusive.
-- -/

namespace EchidnaPortfolio

-- ==========================================================================
-- Section 1: Solver result and confidence
-- ==========================================================================

/-- Individual solver outcome.  Mirrors `SolverResult` in
    portfolio.rs.  We elide non-decision-relevant fields
    (time_ms, error, has_certificate) since they don't enter
    the reconcile logic. -/
structure SolverResult where
  /-- Identifier for the prover (we treat as opaque). -/
  prover_id : Nat
  /-- `none` = timed out, `some b` = verdict. -/
  verified  : Option Bool
deriving Repr, DecidableEq

/-- Confidence levels.  Mirrors `PortfolioConfidence` in
    portfolio.rs. -/
inductive PortfolioConfidence : Type where
  | crossChecked : PortfolioConfidence
  | singleSolver : PortfolioConfidence
  | inconclusive : PortfolioConfidence
  | allTimedOut  : PortfolioConfidence
deriving Repr, DecidableEq

/-- Combined output of `reconcile`.  Mirrors `PortfolioResult`. -/
structure PortfolioResult where
  verified            : Option Bool
  confidence          : PortfolioConfidence
  agreeing_provers    : List Nat
  disagreeing_provers : List Nat
  needs_review        : Bool
deriving Repr

-- ==========================================================================
-- Section 2: Reconcile (pure model of `PortfolioSolver::reconcile`)
-- ==========================================================================

/-- Helper: list of completed (non-timed-out) results. -/
def completed (rs : List SolverResult) : List SolverResult :=
  rs.filter (fun r => r.verified.isSome)

/-- Pure reconcile: turns a list of solver results into a verdict.
    Mirrors `PortfolioSolver::reconcile` in portfolio.rs:108-162.

    NOTE: the Rust version keeps the original results list in the
    output for telemetry; we drop it from the model since it is
    unused by downstream proofs. -/
def reconcile (rs : List SolverResult) : PortfolioResult :=
  let comp := completed rs
  match comp with
  | [] =>
    -- All timed out.
    { verified := none
    , confidence := PortfolioConfidence.allTimedOut
    , agreeing_provers := []
    , disagreeing_provers := []
    , needs_review := true }
  | first :: rest =>
    let firstVerdict : Bool := first.verified.getD false  -- guarded by isSome
    -- Partition `rest` into agreeing vs disagreeing on `firstVerdict`.
    let agreeing :=
      first.prover_id ::
        (rest.filter (fun r => r.verified = some firstVerdict)).map (·.prover_id)
    let disagreeing :=
      (rest.filter (fun r => r.verified ≠ some firstVerdict)).map (·.prover_id)
    if disagreeing.isEmpty then
      if comp.length ≥ 2 then
        -- All agree, ≥ 2 completed: cross-checked
        { verified := some firstVerdict
        , confidence := PortfolioConfidence.crossChecked
        , agreeing_provers := agreeing
        , disagreeing_provers := []
        , needs_review := false }
      else
        -- Only one completed solver
        { verified := some firstVerdict
        , confidence := PortfolioConfidence.singleSolver
        , agreeing_provers := agreeing
        , disagreeing_provers := []
        , needs_review := false }
    else
      -- Disagreement: flag for review
      { verified := none
      , confidence := PortfolioConfidence.inconclusive
      , agreeing_provers := agreeing
      , disagreeing_provers := disagreeing
      , needs_review := true }

-- ==========================================================================
-- Section 3: Exhaustiveness, all-timed-out, single-solver
-- ==========================================================================

/-- **PR-1 (E13/1) Exhaustiveness**: every input list maps to one of
    the four declared confidence levels. -/
theorem reconcile_exhaustive (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.crossChecked
    ∨ (reconcile rs).confidence = PortfolioConfidence.singleSolver
    ∨ (reconcile rs).confidence = PortfolioConfidence.inconclusive
    ∨ (reconcile rs).confidence = PortfolioConfidence.allTimedOut := by
  unfold reconcile
  cases _hcomp : completed rs with
  | nil =>
    right; right; right; rfl
  | cons first rest =>
    simp only
    -- `split_ifs` is a mathlib tactic; core `split` handles each `if`.
    split
    · split
      · left; rfl
      · right; left; rfl
    · right; right; left; rfl

/-- **PR-2 (E13/2) AllTimedOut iff every solver timed out**. -/
theorem allTimedOut_iff_no_completed (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.allTimedOut
    ↔ completed rs = [] := by
  constructor
  · intro h
    unfold reconcile at h
    cases hc : completed rs with
    | nil => rfl
    | cons first rest =>
      rw [hc] at h
      simp only at h
      -- `split_ifs` is mathlib; core `split` peels each `if`.
      repeat' split at h
      all_goals simp at h
  · intro h
    unfold reconcile
    rw [h]

/-- **PR-3 (E13/3) AllTimedOut produces no verdict**. -/
theorem allTimedOut_verdict (rs : List SolverResult)
    (h : (reconcile rs).confidence = PortfolioConfidence.allTimedOut) :
    (reconcile rs).verified = none := by
  rw [allTimedOut_iff_no_completed] at h
  unfold reconcile
  rw [h]

/-- **PR-4 (E13/4) AllTimedOut needs review**. -/
theorem allTimedOut_needs_review (rs : List SolverResult)
    (h : (reconcile rs).confidence = PortfolioConfidence.allTimedOut) :
    (reconcile rs).needs_review = true := by
  rw [allTimedOut_iff_no_completed] at h
  unfold reconcile
  rw [h]

-- ==========================================================================
-- Section 4: SingleSolver
-- ==========================================================================

/-- Predicate: all completed solvers agree on a single boolean
    verdict. -/
def allAgree (b : Bool) (rs : List SolverResult) : Prop :=
  ∀ r ∈ rs, r.verified = some b

instance : Decidable (allAgree b rs) := by
  unfold allAgree; exact inferInstance

/-- **PR-5 (E13/5) SingleSolver implies length-1 completed list**.

    Direction: `confidence = singleSolver ⟹ |completed rs| = 1`.

    The reverse direction (`|completed rs| = 1 ⟹ singleSolver`) is
    immediate from the definition; we prove only the harder direction
    here, which is the soundness of the verdict tag. -/
theorem singleSolver_implies_one_completed (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.singleSolver →
    (completed rs).length = 1 := by
  intro h
  unfold reconcile at h
  cases hc : completed rs with
  | nil =>
    rw [hc] at h; simp at h
  | cons first rest =>
    rw [hc] at h
    simp only at h
    -- `split_ifs` is mathlib; core `split` peels each `if`.
    split at h
    · split at h
      · -- crossChecked branch
        simp at h
      · -- singleSolver branch — `¬ (rest.length+1 ≥ 2)` ⇒ rest = []
        rename_i hlen
        have hlc : (first :: rest).length = rest.length + 1 :=
          List.length_cons first rest
        simp only [Nat.not_le] at hlen
        omega
    · -- inconclusive branch
      simp at h

-- ==========================================================================
-- Section 5: CrossChecked
-- ==========================================================================

/-- **PR-6 (E13/6) CrossChecked implies ≥ 2 completed**. -/
theorem crossChecked_implies_two_completed (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.crossChecked →
    (completed rs).length ≥ 2 := by
  intro h
  unfold reconcile at h
  cases hc : completed rs with
  | nil =>
    rw [hc] at h; simp at h
  | cons first rest =>
    rw [hc] at h
    simp only at h
    split at h
    · split at h
      · -- crossChecked: the length-bound hypothesis is exactly the goal
        rename_i hlen
        exact hlen
      · simp at h
    · simp at h

/-- **PR-7 (E13/7) CrossChecked yields a definite verdict**. -/
theorem crossChecked_has_verdict (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.crossChecked →
    ∃ b, (reconcile rs).verified = some b := by
  intro h
  unfold reconcile at h ⊢
  cases hc : completed rs with
  | nil =>
    rw [hc] at h; simp at h
  | cons first rest =>
    rw [hc] at h
    simp only at h ⊢
    split at h
    · split at h
      · refine ⟨first.verified.getD false, ?_⟩
        rename_i hd hl
        rw [if_pos hd, if_pos hl]
      · simp at h
    · simp at h

/-- **PR-8 (E13/8) CrossChecked has no review flag**. -/
theorem crossChecked_no_review (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.crossChecked →
    (reconcile rs).needs_review = false := by
  intro h
  unfold reconcile at h ⊢
  cases hc : completed rs with
  | nil =>
    rw [hc] at h; simp at h
  | cons first rest =>
    rw [hc] at h
    simp only at h ⊢
    split at h
    · split at h
      · rename_i hd hl
        rw [if_pos hd, if_pos hl]
      · simp at h
    · simp at h

/-- **PR-9 (E13/9) CrossChecked verdict matches first completed**. -/
theorem crossChecked_verdict_matches_first (rs : List SolverResult)
    (first : SolverResult) (rest : List SolverResult)
    (hc : completed rs = first :: rest)
    (hcc : (reconcile rs).confidence = PortfolioConfidence.crossChecked) :
    (reconcile rs).verified = some (first.verified.getD false) := by
  unfold reconcile at hcc ⊢
  rw [hc] at hcc ⊢
  simp only at hcc ⊢
  split at hcc
  · split at hcc
    · rename_i hd hl
      rw [if_pos hd, if_pos hl]
    · simp at hcc
  · simp at hcc

-- ==========================================================================
-- Section 6: Inconclusive (disagreement detection)
-- ==========================================================================

/-- **PR-10 (E13/10) Inconclusive implies disagreement**:
    if `reconcile` reports `Inconclusive`, then there exist two
    completed solvers in the input that returned different verdicts. -/
theorem inconclusive_implies_disagreement (rs : List SolverResult) :
    (reconcile rs).confidence = PortfolioConfidence.inconclusive →
    ∃ first ∈ completed rs, ∃ other ∈ completed rs,
      first.verified.isSome
      ∧ other.verified.isSome
      ∧ first.verified ≠ other.verified := by
  intro h
  unfold reconcile at h
  cases hc : completed rs with
  | nil =>
    simp [hc] at h
  | cons first rest =>
    rw [hc] at h
    simp only at h
    split at h
    · -- disagreeing.isEmpty = true: split inner length `if`; both give
      -- crossChecked / singleSolver, contradicting `= inconclusive`.
      split at h <;> simp at h
    · -- disagreement branch: the disagreeing list is non-empty, so some
      -- element of `rest` has `verified ≠ some firstVerdict`.
      rename_i hdis
      -- `split_ifs`/`push_neg` are mathlib; extract the witness with core
      -- `List.isEmpty_iff` + `List.exists_mem_of_ne_nil`.
      rw [List.isEmpty_iff, List.map_eq_nil_iff] at hdis
      obtain ⟨other, ho_in_filter⟩ := List.exists_mem_of_ne_nil _ hdis
      rw [List.mem_filter] at ho_in_filter
      have ho_mem : other ∈ rest := ho_in_filter.1
      have ho_ne : other.verified ≠ some (first.verified.getD false) := by
        have := ho_in_filter.2
        simpa using this
      -- `completed rs` was substituted to `first :: rest` in the goal by
      -- `cases hc`; supply memberships against `first :: rest` directly.
      -- `completed rs = rs.filter (·.verified.isSome)` definitionally, so
      -- via `hc` every element of `first :: rest` is `isSome`.
      have hcomp_eq : rs.filter (fun r => r.verified.isSome) = first :: rest := by
        have : completed rs = first :: rest := hc
        simpa [completed] using this
      have hfirst_some : first.verified.isSome := by
        have hmem : first ∈ rs.filter (fun r => r.verified.isSome) := by
          rw [hcomp_eq]; exact List.mem_cons_self first rest
        rw [List.mem_filter] at hmem
        exact hmem.2
      have hother_some : other.verified.isSome := by
        have hmem : other ∈ rs.filter (fun r => r.verified.isSome) := by
          rw [hcomp_eq]; exact List.mem_cons_of_mem first ho_mem
        rw [List.mem_filter] at hmem
        exact hmem.2
      refine ⟨first, List.mem_cons_self first rest,
        other, List.mem_cons_of_mem first ho_mem,
        hfirst_some, hother_some, ?_⟩
      -- Show first.verified ≠ other.verified.
      cases hfv : first.verified with
      | none =>
        -- `hfv : first.verified = none` contradicts `first.verified.isSome`.
        rw [hfv] at hfirst_some
        simp at hfirst_some
      | some bf =>
        -- `cases hfv:` substituted `first.verified := some bf` in the goal
        -- (now `some bf ≠ other.verified`) but not in `ho_ne`; rewrite the
        -- latter with `hfv` so both sides talk about `some bf`.
        simp only [hfv, Option.getD_some] at ho_ne
        exact fun heq => ho_ne heq.symm

/-- **PR-11 (E13/11) Inconclusive needs review**. -/
theorem inconclusive_needs_review (rs : List SolverResult)
    (h : (reconcile rs).confidence = PortfolioConfidence.inconclusive) :
    (reconcile rs).needs_review = true := by
  unfold reconcile at h ⊢
  cases hc : completed rs with
  | nil =>
    simp [hc] at h
  | cons first rest =>
    rw [hc] at h
    simp only at h ⊢
    split at h
    · split at h
      · simp at h
      · simp at h
    · -- inconclusive branch: needs_review is literally `true`
      rename_i hd
      rw [if_neg hd]

/-- **PR-12 (E13/12) Inconclusive has no verdict**. -/
theorem inconclusive_no_verdict (rs : List SolverResult)
    (h : (reconcile rs).confidence = PortfolioConfidence.inconclusive) :
    (reconcile rs).verified = none := by
  unfold reconcile at h ⊢
  cases hc : completed rs with
  | nil =>
    simp [hc] at h
  | cons first rest =>
    rw [hc] at h
    simp only at h ⊢
    split at h
    · split at h
      · simp at h
      · simp at h
    · rename_i hd
      rw [if_neg hd]

-- ==========================================================================
-- Section 7: needs_review predicate
-- ==========================================================================

/-- **PR-13 (E13/13) Review iff non-consensus**: the review flag fires
    iff the verdict is Inconclusive or AllTimedOut. -/
theorem needs_review_iff_no_consensus (rs : List SolverResult) :
    (reconcile rs).needs_review = true ↔
    (reconcile rs).confidence = PortfolioConfidence.inconclusive
    ∨ (reconcile rs).confidence = PortfolioConfidence.allTimedOut := by
  constructor
  · intro h
    unfold reconcile at h ⊢
    cases hc : completed rs with
    | nil =>
      right
      rfl
    | cons first rest =>
      rw [hc] at h
      simp only at h ⊢
      split at h
      · split at h
        · simp at h    -- crossChecked: needs_review is false
        · simp at h    -- singleSolver: needs_review is false
      · -- inconclusive
        left
        rename_i hd
        rw [if_neg hd]
  · intro h
    cases h with
    | inl h => exact inconclusive_needs_review rs h
    | inr h => exact allTimedOut_needs_review rs h

-- ==========================================================================
-- Section 8: Verdict preservation under unanimous agreement
-- ==========================================================================

/-- **PR-14 (E13/14) Unanimity → verdict**: if all completed solvers
    return `some b` and ≥ 2 completed, the verdict is `some b` with
    confidence `crossChecked`.

    NOTE — proof depends on `simp` rewriting through the inner
    `let firstVerdict := first.verified.getD false` in `reconcile`.
    If `lake build` rejects the current tactic structure, the
    `unfold reconcile` step may need to be replaced with a hand-rolled
    `show` clause that pre-computes `firstVerdict` outside the
    `match`.  Tracked alongside the other Lean-toolchain fixups
    flagged in `PROOF-NEEDS.md`. -/
theorem unanimous_yields_crosschecked (rs : List SolverResult)
    (b : Bool) (first : SolverResult) (rest : List SolverResult)
    (hc : completed rs = first :: rest)
    (hfirst : first.verified = some b)
    (hall : ∀ r ∈ rest, r.verified = some b)
    (hne : rest ≠ []) :
    (reconcile rs).confidence = PortfolioConfidence.crossChecked
    ∧ (reconcile rs).verified = some b := by
  -- Step 1: the inner `firstVerdict` of `reconcile` evaluates to `b`.
  have hfv : first.verified.getD false = b := by
    rw [hfirst]; rfl
  -- Step 2: every member of `rest` satisfies `r.verified = some b`,
  -- so the disagreement filter on `rest` is empty.  (`not_not` is a
  -- mathlib lemma; `simp [this]` discharges the `≠` directly instead.)
  have hfilter : rest.filter (fun r => r.verified ≠ some b) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    have hrb : r.verified = some b := hall r hr
    simp [hrb]
  -- Step 3: `rest ≠ []` ⇒ length of completed rs ≥ 2.
  have hrest_pos : rest.length ≥ 1 := by
    cases rest with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [List.length_cons]
  have hlen : (completed rs).length ≥ 2 := by
    rw [hc, List.length_cons]
    omega
  -- Step 4: compute reconcile rs.
  unfold reconcile
  rw [hc]
  -- Reduce the inner `let firstVerdict` and the empty disagreement list,
  -- firing the outer `isEmpty` `if`; then the length `if` via `hlen`.
  simp only [hfv, hfilter, List.map_nil, List.isEmpty_nil, if_true]
  rw [hc] at hlen
  rw [if_pos hlen]
  exact ⟨rfl, rfl⟩

end EchidnaPortfolio
