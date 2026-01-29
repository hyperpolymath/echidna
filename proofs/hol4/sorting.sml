(* SPDX-FileCopyrightText: 2025 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)

(* Sorting algorithm verification in HOL4 *)
(* Demonstrates algorithm correctness proofs *)

open HolKernel boolLib bossLib listTheory sortingTheory;

val _ = new_theory "sorting_correctness";

(* Sorted predicate *)
Definition SORTED_DEF:
  (SORTED [] <=> T) /\
  (SORTED [x] <=> T) /\
  (SORTED (x::y::rest) <=> x <= y /\ SORTED (y::rest))
End

(* Insert element into sorted list *)
Definition INSERT_DEF:
  (INSERT x [] = [x]) /\
  (INSERT x (h::t) = if x <= h then x::h::t else h::(INSERT x t))
End

(* Insertion sort *)
Definition ISORT_DEF:
  (ISORT [] = []) /\
  (ISORT (h::t) = INSERT h (ISORT t))
End

(* Insert preserves sortedness *)
Theorem INSERT_SORTED:
  !x l. SORTED l ==> SORTED (INSERT x l)
Proof
  Induct_on 'l' >> rw[INSERT_DEF, SORTED_DEF] >>
  Cases_on 'l' >> fs[INSERT_DEF, SORTED_DEF] >>
  rw[] >> DECIDE_TAC
QED

(* Insertion sort produces sorted output *)
Theorem ISORT_SORTED:
  !l. SORTED (ISORT l)
Proof
  Induct >> rw[ISORT_DEF, INSERT_SORTED, SORTED_DEF]
QED

(* Permutation - element count preservation *)
Definition COUNT_DEF:
  COUNT x l = LENGTH (FILTER ($= x) l)
End

Theorem INSERT_COUNT:
  !x y l. COUNT y (INSERT x l) = if x = y then SUC (COUNT y l) else COUNT y l
Proof
  Induct_on 'l' >> rw[INSERT_DEF, COUNT_DEF, FILTER] >>
  Cases_on 'x = h' >> rw[] >>
  Cases_on 'y = h' >> rw[]
QED

Theorem ISORT_COUNT:
  !x l. COUNT x (ISORT l) = COUNT x l
Proof
  Induct_on 'l' >> rw[ISORT_DEF, COUNT_DEF, INSERT_COUNT]
QED

(* Quick sort definition *)
Definition QSORT_DEF:
  (QSORT [] = []) /\
  (QSORT (pivot::rest) =
    let smaller = FILTER (\x. x <= pivot) rest in
    let larger = FILTER (\x. pivot < x) rest in
    QSORT smaller ++ [pivot] ++ QSORT larger)
Termination
  WF_REL_TAC 'measure LENGTH' >> rw[] >>
  'LENGTH (FILTER P rest) <= LENGTH rest' by simp[LENGTH_FILTER_LEQ] >>
  DECIDE_TAC
End

(* QuickSort produces sorted output *)
Theorem QSORT_SORTED:
  !l. SORTED (QSORT l)
Proof
  recInduct QSORT_DEF >> rw[QSORT_DEF, SORTED_DEF] >>
  rw[SORTED_DEF] >>
  irule SORTED_APPEND >> rw[] >>
  fs[EVERY_MEM, MEM_FILTER] >>
  DECIDE_TAC
QED

val _ = export_theory();
