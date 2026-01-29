(* SPDX-License-Identifier: MIT OR Palimpsest-0.6 *)
(* Simple Coq proof demonstrating ECHIDNA capabilities *)

(** * Simple Arithmetic Proof

    This proof demonstrates basic tactics and shows how ECHIDNA
    can assist with interactive theorem proving.
*)

Require Import Arith.

(** Commutativity of addition *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  (* ECHIDNA suggestion: Use induction on n *)
  induction n as [| n' IHn'].
  - (* Base case: 0 + m = m + 0 *)
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - (* Inductive case: S n' + m = m + S n' *)
    simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

(** Associativity of addition *)
Theorem add_assoc : forall n m p : nat,
  (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(** Identity element *)
Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(** Distributivity *)
Theorem mult_dist : forall n m p : nat,
  n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    rewrite (plus_comm m (n' * m)).
    rewrite plus_assoc.
    rewrite plus_assoc.
    reflexivity.
Qed.

(** 
  Try this proof in ECHIDNA:
  
  1. Start ECHIDNA and select "Coq" as your prover
  2. Load this file
  3. Use the tactic suggester to get AI recommendations
  4. Try filtering suggestions by "algebraic" aspect tag
  5. Watch the proof tree grow as you apply tactics
*)
