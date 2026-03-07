;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm — HOL-o-extension meta-level information

(meta
  ((metadata
     ((version . "0.1.0")
      (media-type . "application/meta+scheme")))

   (architecture-decisions
     ((adr-001
        ((title . "Use o-extension pattern instead of forking HOL")
         (status . "accepted")
         (date . "2026-03-07")
         (context . "ECHIDNA needs custom theories and tactics for HOL4 integration. Options: fork HOL, patch HOL, or overlay alongside HOL.")
         (decision . "Use the o-extension (optional-extension) pattern: a peer-level directory that overlays HOL via environment variables without modifying any upstream files.")
         (rationale . "Forking creates maintenance burden tracking upstream. Patching breaks on rebase. The o-extension pattern keeps HOL pristine, allows clean rebasing, and can be toggled on/off per-run.")
         (consequences . ("HOL upstream can be rebased freely"
                          "No merge conflicts with upstream"
                          "Slightly more complex activation (must source activate.sh)"
                          "Custom theories must be self-contained"))))

      (adr-002
        ((title . "Overlay Protocol as shared pattern with aggregate-library")
         (status . "accepted")
         (date . "2026-03-07")
         (context . "Both o-extension and aggregate-library share core invariants: never modify base, switchable, declared relationship.")
         (decision . "Formalize both as instances of the Overlay Protocol, differentiated by peer-type (o-extension vs aggregate-library) and activation-method (flag vs dependency).")
         (rationale . "Unifying under one protocol makes the patterns discoverable, composable, and consistently documented across the ecosystem.")
         (consequences . ("ECOSYSTEM.scm gains overlay-protocol section"
                          "Both patterns can reference each other as protocol-peers"
                          "Future overlay types can extend the protocol"))))))

   (development-practices
     ((sml-conventions
        ((description . "HOL4 uses Standard ML (SML). All theories and tactics in this o-extension are written in SML.")
         (style . "Follow HOL4 naming conventions for theories and tactics")))

      (testing
        ((description . "Test by loading theories with and without o-extension active")
         (approach . "Activation/deactivation cycle must be idempotent")))))))
