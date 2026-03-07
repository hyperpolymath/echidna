(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* neurosymbolicTac.sml — Neurosymbolic tactics for ECHIDNA
 *
 * Provides HOL4 tactics that integrate with ECHIDNA's ML-guided
 * proof search. These tactics are additive overlays — they do NOT
 * modify any existing HOL4 tactics.
 *
 * Part of the HOL-o-extension overlay.
 *)

structure neurosymbolicTac :> sig
  (* Placeholder: tactic that queries ECHIDNA's ML layer for suggestions *)
  val NEURAL_SUGGEST_TAC : Abbrev.tactic

  (* Placeholder: tactic that tries multiple provers via ECHIDNA dispatch *)
  val PORTFOLIO_TAC : Abbrev.tactic
end = struct

open HolKernel boolLib;

(* NEURAL_SUGGEST_TAC: stub that will query ECHIDNA's Julia ML layer
 * for tactic suggestions based on the current goal.
 * For now, falls back to DECIDE_TAC. *)
fun NEURAL_SUGGEST_TAC (asl, goal) =
  let
    val _ = print "[neurosymbolic] NEURAL_SUGGEST_TAC: ML integration pending\n"
    val _ = print ("  Goal: " ^ term_to_string goal ^ "\n")
  in
    (* Fallback to basic decision procedure *)
    bossLib.DECIDE_TAC (asl, goal)
  end;

(* PORTFOLIO_TAC: stub that will dispatch to multiple ECHIDNA backends
 * and return the first successful proof.
 * For now, falls back to METIS_TAC []. *)
fun PORTFOLIO_TAC (asl, goal) =
  let
    val _ = print "[neurosymbolic] PORTFOLIO_TAC: multi-prover dispatch pending\n"
  in
    metisLib.METIS_TAC [] (asl, goal)
  end;

end;
