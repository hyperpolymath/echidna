(* SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
   SPDX-License-Identifier: MPL-2.0
   Smoke fixture for the HOL Light corpus adapter. *)

needs "lib.ml";;
needs "arith.ml";;

let DOUBLE = define
  `DOUBLE 0 = 0 /\
   DOUBLE (SUC n) = SUC (SUC (DOUBLE n))`;;

let ADD_SYM = prove
 (`!m n. m + n = n + m`,
  MESON_TAC[ADD_AC]);;

let DOUBLE_IS_TWICE = prove
 (`!n. DOUBLE n = 2 * n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[DOUBLE; MULT_CLAUSES; ADD_CLAUSES] THEN
  ARITH_TAC);;

(* HAZARD: a deliberate axiom to exercise the corpus indexer. *)
let EXCLUDED_MIDDLE = new_axiom `!p. p \/ ~p`;;
