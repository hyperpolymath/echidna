-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ConfidenceLattice.lean
--
-- Proves that Echidna's 5-level TrustLevel forms a bounded linear order
-- (and therefore a lattice), that the confidence scoring function is
-- monotone in the appropriate sense, and that Reject-level axioms
-- unconditionally collapse trust to Level1.
--
-- Models the Rust types from src/rust/verification/confidence.rs.

/-! # TrustLevel Lattice Properties

We model the 5-level trust hierarchy as an inductive type and prove:
1. TrustLevel is a decidable linear order (hence a lattice).
2. Reject → Level1 theorem: any TrustFactors with worst_axiom_danger = Reject
   yields trust level ≤ Level1 (i.e., exactly Level1, since Level1 is the minimum).
3. Trust level monotonicity: improving factors never decreases trust.
-/

-- ==========================================================================
-- Section 1: TrustLevel as a bounded linear order
-- ==========================================================================

/-- The five trust levels, mirroring confidence.rs -/
inductive TrustLevel : Type where
  | Level1 : TrustLevel  -- Minimal trust
  | Level2 : TrustLevel  -- Basic trust
  | Level3 : TrustLevel  -- Moderate trust
  | Level4 : TrustLevel  -- High trust
  | Level5 : TrustLevel  -- Maximum trust
deriving Repr, DecidableEq, Inhabited

namespace TrustLevel

/-- Numeric value (1-5), mirroring TrustLevel::value() in Rust -/
def value : TrustLevel → Nat
  | Level1 => 1
  | Level2 => 2
  | Level3 => 3
  | Level4 => 4
  | Level5 => 5

/-- Less-than-or-equal relation on TrustLevel -/
def le (a b : TrustLevel) : Prop := a.value ≤ b.value

/-- Less-than relation on TrustLevel -/
def lt (a b : TrustLevel) : Prop := a.value < b.value

instance : LE TrustLevel := ⟨TrustLevel.le⟩
instance : LT TrustLevel := ⟨TrustLevel.lt⟩

-- Decidability of ≤ and <
instance instDecidableLE (a b : TrustLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.value ≤ b.value))

instance instDecidableLT (a b : TrustLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.value < b.value))

/-- value is injective: distinct levels have distinct numeric values -/
theorem value_injective : ∀ a b : TrustLevel, a.value = b.value → a = b := by
  intro a b h
  cases a <;> cases b <;> simp [value] at h <;> rfl

-- Reflexivity
theorem le_refl : ∀ a : TrustLevel, a ≤ a := by
  intro a; cases a <;> decide

-- Antisymmetry
theorem le_antisymm : ∀ a b : TrustLevel, a ≤ b → b ≤ a → a = b := by
  intro a b; cases a <;> cases b <;> decide

-- Transitivity
theorem le_trans : ∀ a b c : TrustLevel, a ≤ b → b ≤ c → a ≤ c := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

-- Totality (linear order)
theorem le_total : ∀ a b : TrustLevel, a ≤ b ∨ b ≤ a := by
  intro a b; cases a <;> cases b <;> decide

-- ==========================================================================
-- Section 2: Lattice operations (meet / join)
-- ==========================================================================

/-- Minimum of two trust levels (meet / infimum) -/
def meet (a b : TrustLevel) : TrustLevel :=
  if a ≤ b then a else b

/-- Maximum of two trust levels (join / supremum) -/
def join (a b : TrustLevel) : TrustLevel :=
  if a ≤ b then b else a

instance : Min TrustLevel := ⟨meet⟩
instance : Max TrustLevel := ⟨join⟩

/-- meet is a lower bound (left) -/
theorem meet_le_left (a b : TrustLevel) : meet a b ≤ a := by
  cases a <;> cases b <;> decide

/-- meet is a lower bound (right) -/
theorem meet_le_right (a b : TrustLevel) : meet a b ≤ b := by
  cases a <;> cases b <;> decide

/-- join is an upper bound (left) -/
theorem le_join_left (a b : TrustLevel) : a ≤ join a b := by
  cases a <;> cases b <;> decide

/-- join is an upper bound (right) -/
theorem le_join_right (a b : TrustLevel) : b ≤ join a b := by
  cases a <;> cases b <;> decide

-- Bounded: Level1 is bottom, Level5 is top.

/-- Level1 is the minimum element -/
theorem level1_le_all : ∀ t : TrustLevel, Level1 ≤ t := by
  intro t; cases t <;> decide

/-- Level5 is the maximum element -/
theorem all_le_level5 : ∀ t : TrustLevel, t ≤ Level5 := by
  intro t; cases t <;> decide

-- ==========================================================================
-- Section 3: DangerLevel and TrustFactors model
-- ==========================================================================

/-- Axiom danger levels, mirroring axiom_tracker.rs DangerLevel -/
inductive DangerLevel : Type where
  | Safe   : DangerLevel
  | Noted  : DangerLevel
  | Warning : DangerLevel
  | Reject : DangerLevel
deriving DecidableEq, Repr

/-- Trust computation input factors (simplified model of TrustFactors) -/
structure TrustFactors where
  /-- Number of independent confirming provers -/
  confirming_provers : Nat
  /-- Whether a proof certificate was produced -/
  has_certificate : Bool
  /-- Whether the certificate was independently verified -/
  certificate_verified : Bool
  /-- Worst axiom danger level found -/
  worst_axiom_danger : DangerLevel
  /-- Whether the solver binary passed integrity check -/
  solver_integrity_ok : Bool
  /-- Whether the primary prover has a small trusted kernel -/
  is_small_kernel : Bool

/-- Compute trust level from factors.
    Mirrors compute_trust_level() in confidence.rs exactly. -/
def computeTrustLevel (f : TrustFactors) : TrustLevel :=
  -- Reject-level axioms always cap at Level1
  if f.worst_axiom_danger = DangerLevel.Reject then Level1
  -- Warning-level axioms cap at Level1
  else if f.worst_axiom_danger = DangerLevel.Warning then Level1
  -- Failed integrity check caps at Level1
  else if !f.solver_integrity_ok then Level1
  -- Level 5: Cross-checked by 2+ small-kernel with certs
  else if f.confirming_provers ≥ 2 && f.certificate_verified && f.is_small_kernel then Level5
  -- Level 4: Small-kernel with verified cert
  else if f.is_small_kernel && f.certificate_verified then Level4
  -- Level 3: Any prover with verified cert
  else if f.has_certificate && f.certificate_verified then Level3
  -- Level 3: Cross-checked without cert
  else if f.confirming_provers ≥ 2 then Level3
  -- Level 2: default
  else Level2

-- ==========================================================================
-- Section 4: Reject → Level1 theorem
-- ==========================================================================

/-- CORE THEOREM: Reject-level axioms unconditionally result in Level1.
    This mirrors the first guard in compute_trust_level(). -/
theorem reject_implies_level1 :
    ∀ f : TrustFactors, f.worst_axiom_danger = DangerLevel.Reject →
      computeTrustLevel f = Level1 := by
  intro f h
  simp [computeTrustLevel, h]

/-- Corollary: Reject always gives the minimum possible trust. -/
theorem reject_gives_minimum_trust :
    ∀ f : TrustFactors, f.worst_axiom_danger = DangerLevel.Reject →
      ∀ g : TrustFactors, computeTrustLevel f ≤ computeTrustLevel g := by
  intro f hf g
  rw [reject_implies_level1 f hf]
  exact level1_le_all (computeTrustLevel g)

/-- Warning-level axioms also result in Level1. -/
theorem warning_implies_level1 :
    ∀ f : TrustFactors, f.worst_axiom_danger = DangerLevel.Warning →
      computeTrustLevel f = Level1 := by
  intro f h
  simp [computeTrustLevel, h]

/-- Failed integrity check results in Level1 (assuming safe axioms). -/
theorem failed_integrity_implies_level1 :
    ∀ f : TrustFactors,
      f.worst_axiom_danger = DangerLevel.Safe →
      f.solver_integrity_ok = false →
      computeTrustLevel f = Level1 := by
  intro f hd hi
  simp [computeTrustLevel, hd, hi]

-- ==========================================================================
-- Section 5: Trust level monotonicity
-- ==========================================================================

/-- Adding a confirming prover never decreases trust.
    We show: if f' has one more confirming prover and otherwise identical
    factors, then computeTrustLevel f ≤ computeTrustLevel f'. -/
theorem adding_prover_monotone (f : TrustFactors) :
    let f' := { f with confirming_provers := f.confirming_provers + 1 }
    computeTrustLevel f ≤ computeTrustLevel f' := by
  intro _f'
  obtain ⟨cp, hcert, cv, wad, si, sk⟩ := f
  show computeTrustLevel _ ≤ computeTrustLevel _
  simp only [computeTrustLevel]
  -- The only confirming_provers-dependent guards are the `≥ 2` thresholds.
  -- For cp < 2 the threshold is ground (cp ∈ {0,1}); for cp ≥ 2 both
  -- `cp ≥ 2` (for f) and `cp+1 ≥ 2` (for f') hold, so all guards resolve.
  rcases Nat.lt_or_ge cp 2 with hlt | hge
  · obtain _ | _ | cp := cp
    · cases wad <;> cases hcert <;> cases cv <;> cases si <;> cases sk <;> decide
    · cases wad <;> cases hcert <;> cases cv <;> cases si <;> cases sk <;> decide
    · omega
  · have e1 : decide (cp ≥ 2) = true := by simp [hge]
    have e2 : decide (cp + 1 ≥ 2) = true := by simp; omega
    have p2 : cp + 1 ≥ 2 := by omega
    simp only [e1, e2, hge, p2, if_true]
    cases wad <;> cases hcert <;> cases cv <;> cases si <;> cases sk <;> decide

/-- Verifying a certificate never decreases trust. -/
theorem verifying_cert_monotone (f : TrustFactors)
    (h_has_cert : f.has_certificate = true) :
    let f' := { f with certificate_verified := true }
    computeTrustLevel f ≤ computeTrustLevel f' := by
  intro _f'
  obtain ⟨cp, hcert, cv, wad, si, sk⟩ := f
  subst h_has_cert
  show computeTrustLevel _ ≤ computeTrustLevel _
  simp only [computeTrustLevel]
  -- certificate_verified changes; confirming_provers is unchanged, so the
  -- `≥ 2` guard is identical on both sides — pin it, then all guards resolve.
  rcases Nat.lt_or_ge cp 2 with hlt | hge
  · have e1 : decide (cp ≥ 2) = false := by simp; omega
    have hn : ¬ cp ≥ 2 := by omega
    simp only [e1, hn, if_false]
    cases wad <;> cases cv <;> cases si <;> cases sk <;> decide
  · have e1 : decide (cp ≥ 2) = true := by simp [hge]
    simp only [e1, hge, if_true]
    cases wad <;> cases cv <;> cases si <;> cases sk <;> decide

/-- Having a small kernel never decreases trust. -/
theorem small_kernel_monotone (f : TrustFactors) :
    let f' := { f with is_small_kernel := true }
    computeTrustLevel f ≤ computeTrustLevel f' := by
  intro _f'
  obtain ⟨cp, hcert, cv, wad, si, sk⟩ := f
  show computeTrustLevel _ ≤ computeTrustLevel _
  simp only [computeTrustLevel]
  -- is_small_kernel changes; confirming_provers is unchanged, so the
  -- `≥ 2` guard is identical on both sides — pin it, then all guards resolve.
  rcases Nat.lt_or_ge cp 2 with hlt | hge
  · have e1 : decide (cp ≥ 2) = false := by simp; omega
    have hn : ¬ cp ≥ 2 := by omega
    simp only [e1, hn, if_false]
    cases wad <;> cases hcert <;> cases cv <;> cases si <;> cases sk <;> decide
  · have e1 : decide (cp ≥ 2) = true := by simp [hge]
    simp only [e1, hge, if_true]
    cases wad <;> cases hcert <;> cases cv <;> cases si <;> cases sk <;> decide

-- ==========================================================================
-- Section 6: Exhaustive level distinctness
-- ==========================================================================

theorem level1_ne_level2 : Level1 ≠ Level2 := by decide
theorem level1_ne_level3 : Level1 ≠ Level3 := by decide
theorem level1_ne_level4 : Level1 ≠ Level4 := by decide
theorem level1_ne_level5 : Level1 ≠ Level5 := by decide
theorem level2_ne_level3 : Level2 ≠ Level3 := by decide
theorem level2_ne_level4 : Level2 ≠ Level4 := by decide
theorem level2_ne_level5 : Level2 ≠ Level5 := by decide
theorem level3_ne_level4 : Level3 ≠ Level4 := by decide
theorem level3_ne_level5 : Level3 ≠ Level5 := by decide
theorem level4_ne_level5 : Level4 ≠ Level5 := by decide

-- ==========================================================================
-- Section 7: Strict ordering chain
-- ==========================================================================

theorem level1_lt_level2 : Level1 < Level2 := by decide

theorem level2_lt_level3 : Level2 < Level3 := by decide

theorem level3_lt_level4 : Level3 < Level4 := by decide

theorem level4_lt_level5 : Level4 < Level5 := by decide

end TrustLevel
