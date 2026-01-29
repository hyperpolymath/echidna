(* SPDX-FileCopyrightText: 2025 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)

(* Set theory properties in HOL4 *)
(* Demonstrates higher-order reasoning *)

open HolKernel boolLib bossLib pred_setTheory;

val _ = new_theory "set_props";

(* Custom set operations (using HOL4's built-in set theory) *)

(* De Morgan's laws *)
Theorem DE_MORGAN_UNION:
  !s t. COMPL (s UNION t) = COMPL s INTER COMPL t
Proof
  rw[EXTENSION, IN_COMPL, IN_UNION, IN_INTER]
QED

Theorem DE_MORGAN_INTER:
  !s t. COMPL (s INTER t) = COMPL s UNION COMPL t
Proof
  rw[EXTENSION, IN_COMPL, IN_UNION, IN_INTER]
QED

(* Distributivity *)
Theorem UNION_OVER_INTER:
  !s t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)
Proof
  rw[EXTENSION, IN_UNION, IN_INTER]
QED

Theorem INTER_OVER_UNION:
  !s t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)
Proof
  rw[EXTENSION, IN_UNION, IN_INTER]
QED

(* Subset properties *)
Theorem SUBSET_REFLEXIVE:
  !s. s SUBSET s
Proof
  rw[SUBSET_DEF]
QED

Theorem SUBSET_ANTISYM:
  !s t. s SUBSET t /\ t SUBSET s ==> s = t
Proof
  rw[EXTENSION, SUBSET_DEF]
QED

Theorem SUBSET_TRANSITIVE:
  !s t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u
Proof
  rw[SUBSET_DEF]
QED

(* Power set *)
Definition POWERSET_DEF:
  POWERSET s = {t | t SUBSET s}
End

Theorem IN_POWERSET:
  !s t. t IN POWERSET s <=> t SUBSET s
Proof
  rw[POWERSET_DEF, SPECIFICATION]
QED

Theorem EMPTY_IN_POWERSET:
  !s. {} IN POWERSET s
Proof
  rw[IN_POWERSET, EMPTY_SUBSET]
QED

Theorem SELF_IN_POWERSET:
  !s. s IN POWERSET s
Proof
  rw[IN_POWERSET, SUBSET_REFLEXIVE]
QED

(* Cardinality properties *)
Theorem CARD_UNION_DISJOINT:
  !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
        CARD (s UNION t) = CARD s + CARD t
Proof
  metis_tac[CARD_UNION_EQN, CARD_INTER_EMPTY, DISJOINT_DEF]
QED

Theorem CARD_SUBSET:
  !s t. FINITE t /\ s SUBSET t ==> CARD s <= CARD t
Proof
  rw[CARD_SUBSET]
QED

val _ = export_theory();
