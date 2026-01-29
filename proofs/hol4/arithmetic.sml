(* SPDX-FileCopyrightText: 2025 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)

(* Arithmetic properties in HOL4 *)
(* Demonstrates decision procedures and automation *)

open HolKernel boolLib bossLib arithmeticTheory;

val _ = new_theory "arithmetic_props";

(* Factorial definition *)
Definition FACT_DEF:
  (FACT 0 = 1) /\
  (FACT (SUC n) = SUC n * FACT n)
End

(* Factorial is always positive *)
Theorem FACT_POSITIVE:
  !n. 0 < FACT n
Proof
  Induct >> rw[FACT_DEF] >> DECIDE_TAC
QED

(* Factorial is monotonically increasing *)
Theorem FACT_MONO:
  !n. FACT n <= FACT (SUC n)
Proof
  Induct >> rw[FACT_DEF] >>
  'FACT n <= SUC n * FACT n' by DECIDE_TAC >>
  DECIDE_TAC
QED

(* Exponentiation definition *)
Definition EXP_DEF:
  (EXP x 0 = 1) /\
  (EXP x (SUC n) = x * EXP x n)
End

(* Exponentiation laws *)
Theorem EXP_ADD:
  !x m n. EXP x (m + n) = EXP x m * EXP x n
Proof
  Induct_on 'n' >> rw[EXP_DEF] >>
  DECIDE_TAC
QED

Theorem EXP_MULT:
  !x m n. EXP x (m * n) = EXP (EXP x m) n
Proof
  Induct_on 'n' >> rw[EXP_DEF, EXP_ADD] >>
  DECIDE_TAC
QED

(* Sum of first n natural numbers *)
Definition SUM_TO_DEF:
  (SUM_TO 0 = 0) /\
  (SUM_TO (SUC n) = SUC n + SUM_TO n)
End

Theorem SUM_TO_FORMULA:
  !n. 2 * SUM_TO n = n * (n + 1)
Proof
  Induct >> rw[SUM_TO_DEF] >> DECIDE_TAC
QED

val _ = export_theory();
