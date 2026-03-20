-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 ECHIDNA Project
-- Group Theory Examples for ML Training Corpus

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

-- Basic group theory examples

theorem mul_assoc {G : Type*} [Group G] (a b c : G) : (a * b) * c = a * (b * c) := by
  apply mul_assoc

theorem mul_left_inv {G : Type*} [Group G] (a : G) : a⁻¹ * a = 1 := by
  apply inv_mul_self

theorem mul_right_inv {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  apply mul_inv_self

theorem mul_one {G : Type*} [Group G] (a : G) : a * 1 = a := by
  apply mul_one

theorem one_mul {G : Type*} [Group G] (a : G) : 1 * a = a := by
  apply one_mul

-- Subgroup examples
theorem subgroup_closure {G : Type*} [Group G] (H : Subgroup G) (a b : H) : a * b ∈ H := by
  apply H.mul_mem
  assumption
  assumption

theorem subgroup_inv {G : Type*} [Group G] (H : Subgroup G) (a : H) : a⁻¹ ∈ H := by
  apply H.inv_mem
  assumption

theorem subgroup_one {G : Type*} [Group G] (H : Subgroup G) : (1 : G) ∈ H := by
  apply H.one_mem

-- Homomorphism examples
theorem hom_map_mul {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b) = f a * f b := by
  apply f.map_mul

theorem hom_map_one {G H : Type*} [Group G] [Group H] (f : G →* H) :
    f 1 = 1 := by
  apply f.map_one

-- Cyclic group examples
theorem pow_add {G : Type*} [Group G] (a : G) (m n : ℕ) :
    a^(m + n) = a^m * a^n := by
  apply pow_add

theorem pow_zero {G : Type*} [Group G] (a : G) : a^0 = 1 := by
  apply pow_zero

theorem pow_one {G : Type*} [Group G] (a : G) : a^1 = a := by
  apply pow_one

-- Commutator examples
theorem commutator_def {G : Type*} [Group G] (a b : G) :
    a ⋆ b = a⁻¹ * b⁻¹ * a * b := by
  rfl

-- Center examples
theorem center_closure {G : Type*} [Group G] (a b : G) (ha : a ∈ center G) (hb : b ∈ center G) :
    a * b ∈ center G := by
  rintro x
  apply mul_comm
  · apply ha
  · apply hb

-- Normal subgroup examples
theorem normal_conjugate {G : Type*} [Group G] (N : Subgroup G) [Normal N] (g : G) (n : N) :
    g * n * g⁻¹ ∈ N := by
  apply N.conj_mem
  assumption

-- Quotient group examples
theorem quotient_well_defined {G : Type*} [Group G] (N : Subgroup G) [Normal N] (a b : G) :
    (a * N = b * N) ↔ (a⁻¹ * b ∈ N) := by
  apply Subgroup.quotient_eq

-- Direct product examples
theorem prod_group_mul {G H : Type*} [Group G] [Group H] (g1 g2 : G) (h1 h2 : H) :
    (g1, h1) * (g2, h2) = (g1 * g2, h1 * h2) := by
  rfl

theorem prod_group_inv {G H : Type*} [Group G] [Group H] (g : G) (h : H) :
    (g, h)⁻¹ = (g⁻¹, h⁻¹) := by
  rfl

theorem prod_group_one {G H : Type*} [Group G] [Group H] :
    (1, 1) = 1 := by
  rfl
