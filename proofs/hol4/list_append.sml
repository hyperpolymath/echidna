(* SPDX-FileCopyrightText: 2025 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)

(* List append properties in HOL4 *)
(* Demonstrates inductive proofs over lists *)

open HolKernel boolLib bossLib listTheory;

val _ = new_theory "list_append";

(* Length of append theorem *)
Theorem LENGTH_APPEND_THM:
  !l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2
Proof
  Induct >> rw[]
QED

(* Append associativity *)
Theorem APPEND_ASSOC_THM:
  !l1 l2 l3. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
Proof
  Induct >> rw[]
QED

(* Append with empty list *)
Theorem APPEND_NIL_RIGHT:
  !l. l ++ [] = l
Proof
  Induct >> rw[]
QED

(* Reverse of append *)
Definition REVERSE_DEF:
  (REVERSE [] = []) /\
  (REVERSE (h::t) = REVERSE t ++ [h])
End

Theorem REVERSE_APPEND:
  !l1 l2. REVERSE (l1 ++ l2) = REVERSE l2 ++ REVERSE l1
Proof
  Induct >> rw[REVERSE_DEF] >>
  metis_tac[APPEND_ASSOC_THM]
QED

Theorem REVERSE_REVERSE:
  !l. REVERSE (REVERSE l) = l
Proof
  Induct >> rw[REVERSE_DEF, REVERSE_APPEND]
QED

val _ = export_theory();
