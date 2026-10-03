(* SPDX-License-Identifier: MPL-2.0 *)
(* Trivial Coq goal: identity on True. Accepted by coqc. Used by *)
(* the Chapel speedup baseline (docs/bench/2026-05-30-chapel-mrr-baseline.adoc). *)
Definition trivial_true : True := I.
