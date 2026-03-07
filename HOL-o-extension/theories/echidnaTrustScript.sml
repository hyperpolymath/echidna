(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* echidnaTrustScript.sml — Trust level theory for ECHIDNA
 *
 * Formalises ECHIDNA's 5-level trust hierarchy in HOL4:
 *   Untrusted < Sandboxed < Verified < CrossChecked < CertificateProven
 *
 * This theory is part of the HOL-o-extension overlay and does NOT
 * modify any upstream HOL4 code.
 *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "echidnaTrust";

(* Trust levels as a datatype *)
val _ = Datatype `trust_level =
    Untrusted
  | Sandboxed
  | Verified
  | CrossChecked
  | CertificateProven`;

(* Trust ordering: each level strictly dominates the previous *)
val trust_leq_def = Define `
  (trust_leq Untrusted _           = T) /\
  (trust_leq Sandboxed Untrusted   = F) /\
  (trust_leq Sandboxed _           = T) /\
  (trust_leq Verified Untrusted    = F) /\
  (trust_leq Verified Sandboxed    = F) /\
  (trust_leq Verified _            = T) /\
  (trust_leq CrossChecked CertificateProven = T) /\
  (trust_leq CrossChecked CrossChecked      = T) /\
  (trust_leq CrossChecked _                 = F) /\
  (trust_leq CertificateProven CertificateProven = T) /\
  (trust_leq CertificateProven _                 = F)`;

(* Reflexivity of trust ordering *)
val trust_leq_refl = store_thm("trust_leq_refl",
  ``!t. trust_leq t t = T``,
  Cases >> EVAL_TAC);

(* Axiom safety levels *)
val _ = Datatype `axiom_safety =
    Safe
  | Noted
  | Warning
  | Reject`;

val _ = export_theory();
