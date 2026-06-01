(* SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
   SPDX-License-Identifier: MPL-2.0
   Smoke fixture for the HOL4 corpus adapter. *)

open HolKernel boolLib bossLib;
open boolTheory arithmeticTheory listTheory;

val _ = new_theory "MINI";

Definition double_def:
  (double 0 = 0) /\
  (double (SUC n) = SUC (SUC (double n)))
End

val ADD_SYM = store_thm("ADD_SYM",
  `!m n. m + n = n + m`,
  METIS_TAC[ADD_COMM]);

Theorem DOUBLE_TWICE:
  !n. double n = 2 * n
Proof
  Induct >> ASM_REWRITE_TAC[double_def, MULT_CLAUSES, ADD_CLAUSES] >>
  DECIDE_TAC
QED

(* HAZARD: a deliberate cheat to exercise the corpus indexer. *)
val FAKE_THEOREM = store_thm("FAKE_THEOREM",
  `!x. F`,
  cheat);

val _ = export_theory();
