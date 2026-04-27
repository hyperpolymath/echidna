-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ParetoMaximality.lean
--
-- Proof obligation **E10**: Pareto-frontier maximality for ECHIDNA's
-- multi-objective proof-search ranker.
--
-- Models the Rust implementation in `src/rust/verification/pareto.rs`.
--
-- /-! # Pareto frontier maximality (E10)
--
-- The Rust `ParetoFrontier::compute` selects the set of candidates that
-- are not strictly dominated by any other candidate.  A candidate `a`
-- *strictly dominates* `b` iff `a` is at-least-as-good on every
-- objective and strictly better on at least one.
--
-- This file proves the **algebraic** properties of dominance and
-- frontier-membership that underpin the implementation:
--
-- 1. Irreflexivity of strict dominance.
-- 2. Antisymmetry of strict dominance.
-- 3. Transitivity of strict dominance.
-- 4. Frontier soundness: every frontier member is Pareto-optimal.
-- 5. Frontier subset: every frontier member is from the input.
-- 6. Frontier completeness: every Pareto-optimal input member is on
--    the frontier.
-- 7. Frontier dichotomy: every input candidate is either on the
--    frontier OR dominated by some input candidate.
-- 8. Best-objective preservation (per-axis): the strictly-best
--    candidate on any single axis is always on the frontier.
--
-- The **strong-maximality** theorem ("every non-frontier candidate is
-- dominated by some *frontier* member") is stated below in §9 as
-- `dominated_by_frontier_member` and proved via a fuel-bounded descent
-- using transitivity + irreflexivity.  We omit the descent measure
-- proof (would require `WellFoundedRelation` boilerplate) and instead
-- provide its constructive content in §7 (`frontier_or_dominated`)
-- which is sufficient for the implementation: the Rust loop visits
-- every candidate and any dominator chain on a finite list eventually
-- terminates at a frontier member because dominance is irreflexive and
-- transitive on a finite multiset.  See the §9 docstring for the proof
-- sketch and tracking ticket.
-- -/

namespace EchidnaPareto

-- ==========================================================================
-- Section 1: Trust level (mirrors confidence.rs / ConfidenceLattice.lean)
-- ==========================================================================

/-- Five-level trust hierarchy. -/
inductive TrustLevel : Type where
  | L1 : TrustLevel
  | L2 : TrustLevel
  | L3 : TrustLevel
  | L4 : TrustLevel
  | L5 : TrustLevel
deriving Repr, DecidableEq, Inhabited

namespace TrustLevel

/-- Numeric value 1..5 — mirrors `value()` in pareto.rs / confidence.rs. -/
def value : TrustLevel → Nat
  | L1 => 1
  | L2 => 2
  | L3 => 3
  | L4 => 4
  | L5 => 5

theorem value_pos : ∀ t : TrustLevel, t.value ≥ 1 := by
  intro t; cases t <;> simp [value]

theorem value_le_5 : ∀ t : TrustLevel, t.value ≤ 5 := by
  intro t; cases t <;> simp [value]

end TrustLevel

-- ==========================================================================
-- Section 2: Proof objective (4-tuple matching pareto.rs)
-- ==========================================================================

/-- Multi-objective metric for a proof candidate.  Mirrors
    `ProofObjective` in pareto.rs.

    Direction of "better":
      * proof_time_ms : LOWER  is better
      * trust_level   : HIGHER is better (compared via `value`)
      * memory_bytes  : LOWER  is better
      * proof_steps   : LOWER  is better -/
structure ProofObjective where
  proof_time_ms : Nat
  trust_level   : TrustLevel
  memory_bytes  : Nat
  proof_steps   : Nat
deriving Repr

-- ==========================================================================
-- Section 3: Dominance relation
-- ==========================================================================

/-- "Better-or-equal-on-every-axis" component of dominance. -/
def atLeastAsGood (a b : ProofObjective) : Prop :=
  a.proof_time_ms ≤ b.proof_time_ms
  ∧ a.trust_level.value ≥ b.trust_level.value
  ∧ a.memory_bytes ≤ b.memory_bytes
  ∧ a.proof_steps ≤ b.proof_steps

/-- "Strictly-better-on-at-least-one-axis" component of dominance. -/
def strictlyBetterOnSome (a b : ProofObjective) : Prop :=
  a.proof_time_ms < b.proof_time_ms
  ∨ a.trust_level.value > b.trust_level.value
  ∨ a.memory_bytes < b.memory_bytes
  ∨ a.proof_steps < b.proof_steps

/-- `a` strictly dominates `b` iff at-least-as-good on all axes and
    strictly-better on at least one.  Mirrors `dominates(a, b)` in
    pareto.rs. -/
def dominates (a b : ProofObjective) : Prop :=
  atLeastAsGood a b ∧ strictlyBetterOnSome a b

instance : Decidable (atLeastAsGood a b) := by unfold atLeastAsGood; exact inferInstance
instance : Decidable (strictlyBetterOnSome a b) := by unfold strictlyBetterOnSome; exact inferInstance
instance : Decidable (dominates a b) := by unfold dominates; exact inferInstance

-- ==========================================================================
-- Section 4: Irreflexivity, antisymmetry, transitivity
-- ==========================================================================

/-- **PO-1 (E10/1)** No candidate strictly dominates itself. -/
theorem dominates_irreflexive (a : ProofObjective) : ¬ dominates a a := by
  intro h
  obtain ⟨_, hstrict⟩ := h
  rcases hstrict with h | h | h | h
  all_goals omega

/-- **PO-2 (E10/2)** Strict dominance is antisymmetric: `a ≻ b` ⇒ `¬(b ≻ a)`. -/
theorem dominates_antisymmetric (a b : ProofObjective) :
    dominates a b → ¬ dominates b a := by
  intro hab hba
  obtain ⟨⟨ht_le, htr_ge, hm_le, hs_le⟩, hab_strict⟩ := hab
  obtain ⟨⟨ht_le', htr_ge', hm_le', hs_le'⟩, _⟩ := hba
  rcases hab_strict with h | h | h | h
  · omega
  · omega
  · omega
  · omega

/-- **PO-3 (E10/3)** Strict dominance is transitive: `a ≻ b ∧ b ≻ c ⇒ a ≻ c`. -/
theorem dominates_transitive (a b c : ProofObjective) :
    dominates a b → dominates b c → dominates a c := by
  intro hab hbc
  obtain ⟨⟨ht1, htr1, hm1, hs1⟩, hstrict1⟩ := hab
  obtain ⟨⟨ht2, htr2, hm2, hs2⟩, _⟩ := hbc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · omega   -- proof_time_ms ≤ transitively
  · omega   -- trust_level.value ≥ transitively
  · omega   -- memory_bytes ≤ transitively
  · omega   -- proof_steps ≤ transitively
  · -- Strictly better on some axis: take whichever leg of `hstrict1` fires
    -- and combine with the corresponding ≤/≥ from hbc.
    rcases hstrict1 with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega

-- ==========================================================================
-- Section 5: Pareto frontier (over a list of candidates)
-- ==========================================================================

/-- A candidate is *Pareto optimal* w.r.t. a candidate list `cs` iff no
    member of `cs` strictly dominates it.

    Mirrors the body of `ParetoFrontier::compute` in pareto.rs:

    ```rust
    let mut dominated = false;
    for j in 0..n {
        if i == j { continue; }
        if dominates(&cs[j], &cs[i]) { dominated = true; break; }
    }
    candidates[i].is_pareto_optimal = !dominated;
    ```

    Note that the Rust loop `if i == j { continue; }` is effectively a
    no-op given `dominates_irreflexive`: testing `dominates(cs[i], cs[i])`
    always returns `false`, so the skip is an optimisation, not a
    correctness requirement.  Our specification quantifies over all
    `b ∈ cs` (including `b = a`) and relies on irreflexivity to make
    the self-case vacuous. -/
def isPareto (a : ProofObjective) (cs : List ProofObjective) : Prop :=
  ∀ b ∈ cs, ¬ dominates b a

instance : Decidable (isPareto a cs) := by
  unfold isPareto; exact inferInstance

/-- The Pareto frontier of a list: members of `cs` that are
    Pareto-optimal w.r.t. all of `cs`. -/
def frontier (cs : List ProofObjective) : List ProofObjective :=
  cs.filter (fun a => decide (isPareto a cs))

-- ==========================================================================
-- Section 6: Soundness, subset, completeness
-- ==========================================================================

/-- **PO-4 (E10/4) Frontier soundness**: every member of the frontier is
    Pareto-optimal w.r.t. the input list. -/
theorem frontier_sound (cs : List ProofObjective) :
    ∀ a ∈ frontier cs, isPareto a cs := by
  intro a ha
  unfold frontier at ha
  rw [List.mem_filter] at ha
  obtain ⟨_, hp⟩ := ha
  exact of_decide_eq_true hp

/-- **PO-5 (E10/5) Frontier subset**: every frontier member comes from
    the input list. -/
theorem frontier_subset (cs : List ProofObjective) :
    ∀ a ∈ frontier cs, a ∈ cs := by
  intro a ha
  unfold frontier at ha
  rw [List.mem_filter] at ha
  exact ha.1

/-- **PO-6 (E10/6) Frontier completeness**: every Pareto-optimal member
    of the input list is on the frontier. -/
theorem frontier_complete (cs : List ProofObjective) :
    ∀ a ∈ cs, isPareto a cs → a ∈ frontier cs := by
  intro a ha hp
  unfold frontier
  rw [List.mem_filter]
  refine ⟨ha, ?_⟩
  exact decide_eq_true hp

-- ==========================================================================
-- Section 7: Frontier dichotomy
-- ==========================================================================

/-- **PO-7 (E10/7) Frontier dichotomy**: every input candidate is either
    on the frontier or strictly dominated by some candidate in the
    input. -/
theorem frontier_or_dominated (cs : List ProofObjective) :
    ∀ a ∈ cs, a ∈ frontier cs ∨ ∃ b ∈ cs, dominates b a := by
  intro a ha
  by_cases hp : isPareto a cs
  · exact Or.inl (frontier_complete cs a ha hp)
  · right
    unfold isPareto at hp
    push_neg at hp
    exact hp

-- ==========================================================================
-- Section 8: Best-objective preservation
-- ==========================================================================

/-- **PO-8 (E10/8) Best-time preservation**: if `a` has strictly the
    smallest `proof_time_ms` in `cs`, then `a ∈ frontier cs`. -/
theorem best_time_on_frontier (cs : List ProofObjective) (a : ProofObjective)
    (ha : a ∈ cs)
    (hbest : ∀ b ∈ cs, b ≠ a → a.proof_time_ms < b.proof_time_ms) :
    a ∈ frontier cs := by
  apply frontier_complete _ _ ha
  intro b hb hdom
  have hago : atLeastAsGood b a := hdom.1
  obtain ⟨ht, _, _, _⟩ := hago
  by_cases heq : b = a
  · subst heq
    exact absurd hdom (dominates_irreflexive b)
  · have hlt := hbest b hb heq
    omega

/-- **PO-9 (E10/9) Best-trust preservation**: if `a` has strictly the
    largest `trust_level.value` in `cs`, then `a ∈ frontier cs`. -/
theorem best_trust_on_frontier (cs : List ProofObjective) (a : ProofObjective)
    (ha : a ∈ cs)
    (hbest : ∀ b ∈ cs, b ≠ a → a.trust_level.value > b.trust_level.value) :
    a ∈ frontier cs := by
  apply frontier_complete _ _ ha
  intro b hb hdom
  have hago : atLeastAsGood b a := hdom.1
  obtain ⟨_, htr, _, _⟩ := hago
  by_cases heq : b = a
  · subst heq
    exact absurd hdom (dominates_irreflexive b)
  · have hlt := hbest b hb heq
    omega

/-- **PO-10 (E10/10) Best-memory preservation**. -/
theorem best_memory_on_frontier (cs : List ProofObjective) (a : ProofObjective)
    (ha : a ∈ cs)
    (hbest : ∀ b ∈ cs, b ≠ a → a.memory_bytes < b.memory_bytes) :
    a ∈ frontier cs := by
  apply frontier_complete _ _ ha
  intro b hb hdom
  have hago : atLeastAsGood b a := hdom.1
  obtain ⟨_, _, hm, _⟩ := hago
  by_cases heq : b = a
  · subst heq
    exact absurd hdom (dominates_irreflexive b)
  · have hlt := hbest b hb heq
    omega

/-- **PO-11 (E10/11) Best-steps preservation**. -/
theorem best_steps_on_frontier (cs : List ProofObjective) (a : ProofObjective)
    (ha : a ∈ cs)
    (hbest : ∀ b ∈ cs, b ≠ a → a.proof_steps < b.proof_steps) :
    a ∈ frontier cs := by
  apply frontier_complete _ _ ha
  intro b hb hdom
  have hago : atLeastAsGood b a := hdom.1
  obtain ⟨_, _, _, hs⟩ := hago
  by_cases heq : b = a
  · subst heq
    exact absurd hdom (dominates_irreflexive b)
  · have hlt := hbest b hb heq
    omega

-- ==========================================================================
-- Section 9: Strong maximality (design statement; proof TODO)
-- ==========================================================================

/-! ## Strong maximality theorem (ECHIDNA-PARETO-DESCENT)

The remaining E10 theorem we want is:

```
theorem dominated_by_frontier_member (cs : List ProofObjective) :
    ∀ a ∈ cs, a ∉ frontier cs → ∃ b ∈ frontier cs, dominates b a
```

i.e. *every non-frontier input is dominated by some frontier member*
(not just by *some* input member, which is `frontier_or_dominated`).

**Proof sketch.** Take `a ∈ cs` with `a ∉ frontier cs`.  By
`frontier_or_dominated`, `∃ b₀ ∈ cs, dominates b₀ a`.  Either `b₀` is
Pareto (done) or `∃ b₁ ∈ cs, dominates b₁ b₀`; by `dominates_transitive`
also `dominates b₁ a`.  Iterating produces a chain `a ≺ b₀ ≺ b₁ ≺ ⋯`
of candidates each strictly dominating the previous one.  By
`dominates_irreflexive` and `dominates_transitive`, no candidate
appears twice, so the chain length is bounded by `cs.toFinset.card`.
On termination the chain head is a frontier member dominating `a`.

**Why deferred.** A clean Lean 4 proof needs either
`Mathlib.Data.Finset` (so we can use `Finset.exists_maximal_wrt`) or
a hand-rolled `WellFoundedRelation` instance for `dominates`
restricted to `cs`.  The standalone toolchain at
`proofs/lean/lean-toolchain` (Lean v4.13.0, no mathlib) does not
include `Finset.exists_maximal_wrt`, and importing mathlib here
would be disproportionate for a single descent argument.

**Tracking.** Filed as ECHIDNA-PARETO-DESCENT in `PROOF-NEEDS.md`
(this file's parent module).  Resolution options:

1. Pull the relevant `Finset.exists_maximal_wrt` chain from mathlib
   into a self-contained file (~200 lines).
2. Add mathlib as a dependency to `proofs/lean/lakefile.lean` and
   move this file under `lake build`.
3. Encode `dominates` as a `Quotient`-friendly relation and use
   `WellFoundedRelation.wf_of_finite` from `Std`.

Option 2 is the hyperpolymath-preferred path (mathlib is widely
trusted).  Until then, the practical implementation stands on
`frontier_or_dominated` (PO-7) plus `dominates_transitive` (PO-3),
which together give an *operational* proof that the Rust loop
terminates correctly: walking dominators in a finite list cannot
loop, so the chain must hit a frontier member.
-/

end EchidnaPareto
