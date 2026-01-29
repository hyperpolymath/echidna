(* SPDX-FileCopyrightText: 2025 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)

(* Binary tree operations in HOL4 *)
(* Demonstrates datatype definitions and structural induction *)

open HolKernel boolLib bossLib;

val _ = new_theory "binary_tree";

(* Binary tree datatype *)
Datatype:
  tree = Leaf
       | Node tree 'a tree
End

(* Tree size *)
Definition SIZE_DEF:
  (SIZE Leaf = 0) /\
  (SIZE (Node l x r) = 1 + SIZE l + SIZE r)
End

(* Tree height *)
Definition HEIGHT_DEF:
  (HEIGHT Leaf = 0) /\
  (HEIGHT (Node l x r) = 1 + MAX (HEIGHT l) (HEIGHT r))
End

(* Mirror a tree *)
Definition MIRROR_DEF:
  (MIRROR Leaf = Leaf) /\
  (MIRROR (Node l x r) = Node (MIRROR r) x (MIRROR l))
End

(* Mirror is involutive *)
Theorem MIRROR_MIRROR:
  !t. MIRROR (MIRROR t) = t
Proof
  Induct >> rw[MIRROR_DEF]
QED

(* Mirror preserves size *)
Theorem MIRROR_SIZE:
  !t. SIZE (MIRROR t) = SIZE t
Proof
  Induct >> rw[MIRROR_DEF, SIZE_DEF]
QED

(* Mirror preserves height *)
Theorem MIRROR_HEIGHT:
  !t. HEIGHT (MIRROR t) = HEIGHT t
Proof
  Induct >> rw[MIRROR_DEF, HEIGHT_DEF, MAX_COMM]
QED

(* In-order traversal *)
Definition INORDER_DEF:
  (INORDER Leaf = []) /\
  (INORDER (Node l x r) = INORDER l ++ [x] ++ INORDER r)
End

(* Relationship between size and inorder *)
Theorem SIZE_INORDER:
  !t. SIZE t = LENGTH (INORDER t)
Proof
  Induct >> rw[SIZE_DEF, INORDER_DEF]
QED

(* Perfect binary tree predicate *)
Definition PERFECT_DEF:
  (PERFECT Leaf <=> T) /\
  (PERFECT (Node l x r) <=> PERFECT l /\ PERFECT r /\ HEIGHT l = HEIGHT r)
End

(* Size of a perfect tree *)
Theorem PERFECT_SIZE:
  !t. PERFECT t ==> SIZE t = 2 ** HEIGHT t - 1
Proof
  Induct >> rw[PERFECT_DEF, SIZE_DEF, HEIGHT_DEF] >>
  '2 ** SUC (HEIGHT t) = 2 * 2 ** HEIGHT t' by rw[] >>
  DECIDE_TAC
QED

val _ = export_theory();
