(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* security.sml — Security-focused overlay for HOL-o-extension
 *
 * Adds theories and tactics for security protocol verification,
 * intended for use with ECHIDNA's trust pipeline.
 *
 * Load after default.sml:
 *   use "overlays/security.sml";
 *)

val _ = print "[HOL-o-extension] Security overlay loaded (stubs)\n";

(* Placeholder: security-specific theories will be registered here *)
(* Planned:
 *   - TrustLevel theory (formalising ECHIDNA's 5-level trust hierarchy)
 *   - ConfidenceScore theory (dependent on TrustLevel)
 *   - AxiomSafety theory (Safe, Noted, Warning, Reject classification)
 *)
