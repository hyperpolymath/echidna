(* SPDX-FileCopyrightText: 2026 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MPL-2.0 *)

module Smoke

/// Docstring: a tiny F* fixture exercising the corpus adapter's main shapes.

open FStar.List
include FStar.Mul

val double : nat -> Tot nat
let double x = x + x

let rec sum_to (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0 else n + sum_to (n - 1)

type color =
  | Red
  | Green
  | Blue

inductive tree (a: Type) =
  | Leaf : tree a
  | Node : tree a -> a -> tree a -> tree a

// HAZARD: deliberate assume to exercise the postulate-detection path.
assume val oracle : x:nat -> Tot (y:nat{y >= x})
