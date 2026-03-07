(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* default.sml — Base overlay configuration for HOL-o-extension
 *
 * This overlay is always applied when the o-extension is active.
 * It registers custom theories and tactics with HOL's load system.
 *)

(* Guard: only load if o-extension is active *)
val _ = case OS.Process.getEnv "HOL_OEXT_ACTIVE" of
    SOME "1" => ()
  | _ => raise Fail "HOL-o-extension not activated (source activate.sh first)";

val oextDir = case OS.Process.getEnv "HOL_OEXT_DIR" of
    SOME d => d
  | NONE => raise Fail "HOL_OEXT_DIR not set";

val _ = print ("[HOL-o-extension] Loading from " ^ oextDir ^ "\n");

(* Register theory search paths *)
(* val _ = loadPath := (oextDir ^ "/theories") :: (!loadPath); *)

(* Placeholder: theories and tactics will be registered here as they are created *)
val _ = print "[HOL-o-extension] Default overlay loaded (no theories registered yet)\n";
