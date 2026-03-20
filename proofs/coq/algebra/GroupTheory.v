(** SPDX-License-Identifier: PMPL-1.0-or-later
    Copyright (c) 2026 ECHIDNA Project
    Group Theory Examples for ML Training Corpus *)

Require Import GroupTheory.Groups.
Require Import GroupTheory.GroupDef.

Section GroupTheoryExamples.
  Context {G : Type} (op : G → G → G) (e : G) (inv : G → G).
  Variable group : groupSet op e inv.

  (** Basic group axioms *)

  Lemma mul_assoc (a b c : G) :
    (op (op a b) c) = (op a (op b c)).
  Proof.
    apply (group_morph group); trivial.
    apply (group_set_like group); trivial.
    apply (group_axioms group); trivial.
    apply (assoc group); trivial.
    assumption.
  Qed.

  Lemma mul_left_inv (a : G) :
    op (inv a) a = e.
  Proof.
    apply (group_axioms group); trivial.
    apply (left_inverse group); trivial.
    assumption.
  Qed.

  Lemma mul_right_inv (a : G) :
    op a (inv a) = e.
  Proof.
    apply (group_axioms group); trivial.
    apply (right_inverse group); trivial.
    assumption.
  Qed.

  Lemma mul_left_id (a : G) :
    op e a = a.
  Proof.
    apply (group_axioms group); trivial.
    apply (left_id group); trivial.
    assumption.
  Qed.

  Lemma mul_right_id (a : G) :
    op a e = a.
  Proof.
    apply (group_axioms group); trivial.
    apply (right_id group); trivial.
    assumption.
  Qed.

  (** Subgroup examples *)

  Lemma subgroup_closure (H : subgroup G) (a b : G) :
    a ∈ H → b ∈ H → op a b ∈ H.
  Proof.
    intros Ha Hb.
    apply (subgroup_axioms H); trivial.
    apply (subgroup_mul_closed H); trivial.
    assumption.
  Qed.

  Lemma subgroup_inv (H : subgroup G) (a : G) :
    a ∈ H → inv a ∈ H.
  Proof.
    intros Ha.
    apply (subgroup_axioms H); trivial.
    apply (subgroup_inv_closed H); trivial.
    assumption.
  Qed.

  Lemma subgroup_id (H : subgroup G) :
    e ∈ H.
  Proof.
    apply (subgroup_axioms H); trivial.
    apply (subgroup_one_closed H); trivial.
  Qed.

  (** Homomorphism examples *)

  Lemma hom_map_mul {H : Type} (f : G → H) (opH : H → H → H) (eH : H) (invH : H → H) 
                    (hom : homomorphism f op opH e eH inv invH) 
                    (a b : G) :
    f (op a b) = opH (f a) (f b).
  Proof.
    apply (homomorphism_def hom); trivial.
    apply (homomorphism_morph hom); trivial.
    assumption.
  Qed.

  Lemma hom_map_id {H : Type} (f : G → H) (opH : H → H → H) (eH : H) (invH : H → H)
                   (hom : homomorphism f op opH e eH inv invH) :
    f e = eH.
  Proof.
    apply (homomorphism_def hom); trivial.
    apply (homomorphism_id hom); trivial.
  Qed.

  (** Power examples *)

  Lemma pow_add (a : G) (m n : nat) :
    op (pow op a (m + n)) e = op (pow op a m) (pow op a n).
  Proof.
    induction n; simpl.
    - apply pow_zero; trivial.
    - apply mul_assoc; trivial.
      apply pow_succ; trivial.
      assumption.
  Qed.

  Lemma pow_zero (a : G) :
    op (pow op a 0) e = e.
  Proof.
    apply pow_zero; trivial.
  Qed.

  Lemma pow_one (a : G) :
    op (pow op a 1) e = op a e.
  Proof.
    apply pow_one; trivial.
  Qed.

  (** Commutator examples *)

  Definition commutator (a b : G) : G := 
    op (inv a) (op (inv b) (op a (op b e))).

  Lemma commutator_inverse (a b : G) :
    op (commutator a b) (commutator b a) = e.
  Proof.
    unfold commutator.
    simpl.
    apply mul_assoc; trivial.
    apply mul_left_inv; trivial.
    apply mul_right_inv; trivial.
    apply mul_assoc; trivial.
    apply mul_left_inv; trivial.
    apply mul_right_inv; trivial.
  Qed.

  (** Center examples *)

  Definition center : set G := 
    { x : G | forall y : G, op x y = op y x }.

  Lemma center_closed (a b : G) :
    (forall x, op a x = op x a) →
    (forall x, op b x = op x b) →
    forall x, op (op a b) x = op x (op a b).
  Proof.
    intros Ha Hb x.
    apply mul_assoc; trivial.
    rewrite Ha; trivial.
    rewrite Hb; trivial.
    apply mul_assoc; trivial.
    rewrite Hb; trivial.
    rewrite Ha; trivial.
  Qed.

  (** Normal subgroup examples *)

  Lemma normal_conjugate (N : subgroup G) [normal : normal_subgroup N] 
                         (g : G) (n : G) :
    n ∈ N → op g (op n (inv g)) ∈ N.
  Proof.
    intros Hn.
    apply (normal_subgroup_def normal); trivial.
    apply (normal_conjugate normal); trivial.
    assumption.
  Qed.

  (** Quotient group examples *)

  Lemma quotient_well_defined (N : subgroup G) [normal : normal_subgroup N] 
                            (a b : G) :
    (coset N a = coset N b) ↔ (op (inv a) b ∈ N).
  Proof.
    apply coset_eq; trivial.
    apply normal_subgroup_quotient; trivial.
  Qed.

  (** Direct product examples *)

  Lemma prod_group_mul {H : Type} (opH : H → H → H) (eH : H) (invH : H → H)
                       (groupH : groupSet opH eH invH) 
                       (a b : G) (c d : H) :
    (op a b, opH c d) = (op (a, c) (b, d)).
  Proof.
    reflexivity.
  Qed.

  Lemma prod_group_inv {H : Type} (opH : H → H → H) (eH : H) (invH : H → H)
                      (groupH : groupSet opH eH invH) 
                      (a : G) (c : H) :
    (inv a, invH c) = inv (a, c).
  Proof.
    reflexivity.
  Qed.

  Lemma prod_group_id {H : Type} (opH : H → H → H) (eH : H) (invH : H → H)
                     (groupH : groupSet opH eH invH) :
    (e, eH) = (e, eH).
  Proof.
    reflexivity.
  Qed.

End GroupTheoryExamples.
