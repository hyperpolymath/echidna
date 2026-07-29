(* SPDX-License-Identifier: MPL-2.0
   Copyright (c) 2026 ECHIDNA Project
   Group Theory: self-contained abstract algebra for training corpus.

   This file defines abstract groups via a record, then proves the five
   standard group lemmas and several derived properties.
   No library dependency beyond Coq's kernel. *)

(** * Abstract Group Definition *)

(** A group consists of a carrier type, binary operation, identity, and
    inverse satisfying the standard axioms.
    [G] is implicit — inferred from [op]. *)
Record GroupAxioms {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G) : Prop := {
  gassoc    : forall a b c : G, op (op a b) c = op a (op b c);
  gleft_id  : forall a : G, op e a = a;
  gright_id : forall a : G, op a e = a;
  gleft_inv : forall a : G, op (inv a) a = e;
  gright_inv : forall a : G, op a (inv a) = e
}.

(** ** Derived properties *)

(** The identity element is unique. *)
Theorem identity_unique {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G)
    (gax : GroupAxioms op e inv) (e' : G) :
    (forall a, op e' a = a) -> e' = e.
Proof.
  intro H.
  rewrite <- (gright_id op e inv gax e').
  apply H.
Qed.

(** Left cancellation: op a b = op a c → b = c. *)
Theorem left_cancel {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G)
    (gax : GroupAxioms op e inv) (a b c : G) :
    op a b = op a c -> b = c.
Proof.
  intro H.
  rewrite <- (gleft_id op e inv gax b).
  rewrite <- (gleft_id op e inv gax c).
  rewrite <- (gleft_inv op e inv gax a).
  (* Goal: op (op (inv a) a) b = op (op (inv a) a) c *)
  rewrite (gassoc op e inv gax).   (* op (op (inv a) a) b → op (inv a) (op a b) *)
  rewrite (gassoc op e inv gax).   (* op (op (inv a) a) c → op (inv a) (op a c) *)
  rewrite H.
  reflexivity.
Qed.

(** Right cancellation: op b a = op c a → b = c. *)
Theorem right_cancel {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G)
    (gax : GroupAxioms op e inv) (a b c : G) :
    op b a = op c a -> b = c.
Proof.
  intro H.
  rewrite <- (gright_id op e inv gax b).
  rewrite <- (gright_id op e inv gax c).
  rewrite <- (gright_inv op e inv gax a).
  (* Goal: op b (op a (inv a)) = op c (op a (inv a)) *)
  rewrite <- (gassoc op e inv gax).  (* op b (op a (inv a)) → op (op b a) (inv a) *)
  rewrite <- (gassoc op e inv gax).  (* op c (op a (inv a)) → op (op c a) (inv a) *)
  rewrite H.
  reflexivity.
Qed.

(** The inverse of the inverse is the original element. *)
Theorem inv_inv {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G)
    (gax : GroupAxioms op e inv) (a : G) :
    inv (inv a) = a.
Proof.
  apply (left_cancel op e inv gax (inv a)).
  (* Goal: op (inv a) (inv (inv a)) = op (inv a) a *)
  rewrite (gleft_inv op e inv gax a).      (* op (inv a) a → e on RHS *)
  rewrite (gright_inv op e inv gax (inv a)). (* op (inv a) (inv (inv a)) → e on LHS *)
  reflexivity.
Qed.

(** The inverse of a product reverses order. *)
Theorem inv_mul {G : Type} (op : G -> G -> G) (e : G) (inv : G -> G)
    (gax : GroupAxioms op e inv) (a b : G) :
    inv (op a b) = op (inv b) (inv a).
Proof.
  apply (left_cancel op e inv gax (op a b)).
  (* Goal: op (op a b) (inv (op a b)) = op (op a b) (op (inv b) (inv a)) *)
  rewrite (gright_inv op e inv gax (op a b)).
  (* Goal: e = op (op a b) (op (inv b) (inv a)) *)
  rewrite <- (gassoc op e inv gax).
  (* Goal: e = op (op (op a b) (inv b)) (inv a) *)
  rewrite (gassoc op e inv gax a b (inv b)).
  (* Goal: e = op (op a (op b (inv b))) (inv a) *)
  rewrite (gright_inv op e inv gax b).
  (* Goal: e = op (op a e) (inv a) *)
  rewrite (gright_id op e inv gax a).
  (* Goal: e = op a (inv a) *)
  rewrite (gright_inv op e inv gax a).
  reflexivity.
Qed.

(** * Concrete Example: Integers mod 2 form a group under addition *)

Definition Z2 := bool.

Definition z2_op (a b : Z2) : Z2 := xorb a b.
Definition z2_e  : Z2 := false.
Definition z2_inv (a : Z2) : Z2 := a.

Lemma z2_group : GroupAxioms z2_op z2_e z2_inv.
Proof.
  constructor.
  - intros a b c. destruct a, b, c; reflexivity.
  - intros a. destruct a; reflexivity.
  - intros a. destruct a; reflexivity.
  - intros a. destruct a; reflexivity.
  - intros a. destruct a; reflexivity.
Qed.

(** Verify the derived lemmas hold for Z2. *)
Example z2_inv_inv : forall a : Z2, z2_inv (z2_inv a) = a.
Proof.
  intro a.
  exact (inv_inv z2_op z2_e z2_inv z2_group a).
Qed.
