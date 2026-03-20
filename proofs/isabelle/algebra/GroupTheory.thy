(** SPDX-License-Identifier: PMPL-1.0-or-later
    Copyright (c) 2026 ECHIDNA Project
    Group Theory Examples for ML Training Corpus *)

theory GroupTheory
  imports Main "~~/src/HOL/Algebra/Group"
begin

(** Basic group axioms *)

lemma mul_assoc:
  fixes G (structure)
  assumes "group G"
  shows "⋀a b c. (a ⊗ₘ b) ⊗ₘ c = a ⊗ₘ (b ⊗ₘ c)"
  using assms by (simp add: group.assoc)

lemma mul_left_inv:
  fixes G (structure)
  assumes "group G"
  shows "⋀a. invₘ a ⊗ₘ a = 𝟭ₘ"
  using assms by (simp add: group.left_inv)

lemma mul_right_inv:
  fixes G (structure)
  shows "⋀a. a ⊗ₘ invₘ a = 𝟭ₘ"
  using assms by (simp add: group.right_inv)

lemma mul_left_id:
  fixes G (structure)
  assumes "group G"
  shows "⋀a. 𝟭ₘ ⊗ₘ a = a"
  using assms by (simp add: group.left_id)

lemma mul_right_id:
  fixes G (structure)
  shows "⋀a. a ⊗ₘ 𝟭ₘ = a"
  using assms by (simp add: group.right_id)

(** Subgroup examples *)

lemma subgroup_closure:
  fixes G (structure)
  assumes "group G" and "subgroup H G"
  shows "⋀a b. a ∈ carrier H ∧ b ∈ carrier H ⇒ a ⊗ₘ b ∈ carrier H"
  using assms by (simp add: subgroup.m_closed)

lemma subgroup_inv:
  fixes G (structure)
  assumes "group G" and "subgroup H G"
  shows "⋀a. a ∈ carrier H ⇒ invₘ a ∈ carrier H"
  using assms by (simp add: subgroup.m_inv_closed)

lemma subgroup_id:
  fixes G (structure)
  assumes "group G" and "subgroup H G"
  shows "𝟭ₘ ∈ carrier H"
  using assms by (simp add: subgroup.one_closed)

(** Homomorphism examples *)

lemma hom_map_mul:
  fixes G H (structure)
  assumes "group G" and "group H" and "h ∈ hom G H"
  shows "⋀a b. h (a ⊗ₘ b) = h a ⊗ₘ h b"
  using assms by (simp add: hom.hom_mult)

lemma hom_map_id:
  fixes G H (structure)
  assumes "group G" and "group H" and "h ∈ hom G H"
  shows "h 𝟭ₘ = 𝟭ₘ"
  using assms by (simp add: hom.hom_one)

(** Power examples *)

lemma pow_add:
  fixes G (structure)
  assumes "group G"
  shows "⋀a m n. a (⊕ₘ) (m + n) = a (⊕ₘ) m ⊗ₘ a (⊕ₘ) n"
  using assms by (simp add: power_add)

lemma pow_zero:
  fixes G (structure)
  assumes "group G"
  shows "⋀a. a (⊕ₘ) 0 = 𝟭ₘ"
  using assms by (simp add: power_0)

lemma pow_one:
  fixes G (structure)
  assumes "group G"
  shows "⋀a. a (⊕ₘ) 1 = a"
  using assms by (simp add: power_1)

(** Commutator examples *)

definition commutator :: "'a ⇒ 'a ⇒ 'a" where
  "commutator a b ≡ invₘ a ⊗ₘ invₘ b ⊗ₘ a ⊗ₘ b"

lemma commutator_inverse:
  fixes G (structure)
  assumes "group G"
  shows "⋀a b. commutator a b ⊗ₘ commutator b a = 𝟭ₘ"
  using assms
  by (simp add: commutator_def group.assoc group.left_inv group.right_inv)

(** Center examples *)

definition center :: "'a set" where
  "center ≡ {x. ∀y. x ⊗ₘ y = y ⊗ₘ x}"

lemma center_closed:
  fixes G (structure)
  assumes "group G"
  shows "⋀a b. (∀x. a ⊗ₘ x = x ⊗ₘ a) ∧ (∀x. b ⊗ₘ x = x ⊗ₘ b) ⇒ ∀x. (a ⊗ₘ b) ⊗ₘ x = x ⊗ₘ (a ⊗ₘ b)"
  using assms
  by (metis group.assoc group.m_comm)

(** Normal subgroup examples *)

lemma normal_conjugate:
  fixes G (structure)
  assumes "group G" and "N ⊴ G"
  shows "⋀g n. n ∈ carrier N ⇒ g ⊗ₘ n ⊗ₘ invₘ g ∈ carrier N"
  using assms by (simp add: normal.conjugate)

(** Quotient group examples *)

lemma quotient_well_defined:
  fixes G (structure)
  assumes "group G" and "N ⊴ G"
  shows "⋀a b. (a *ₘ N = b *ₘ N) = (invₘ a ⊗ₘ b ∈ carrier N)"
  using assms by (simp add: r_coset_eq_normal)

(** Direct product examples *)

lemma prod_group_mul:
  fixes G H (structure)
  assumes "group G" and "group H"
  shows "⋀a b c d. (a, c) ⊗ₘ (b, d) = (a ⊗ₘ b, c ⊗ₘ d)"
  using assms by (simp add: Prod.mult_def)

lemma prod_group_inv:
  fixes G H (structure)
  assumes "group G" and "group H"
  shows "⋀a c. invₘ (a, c) = (invₘ a, invₘ c)"
  using assms by (simp add: Prod.inv_def)

lemma prod_group_id:
  fixes G H (structure)
  assumes "group G" and "group H"
  shows "𝟭ₘ = (𝟭ₘ, 𝟭ₘ)"
  using assms by (simp add: Prod.one_def)

end
