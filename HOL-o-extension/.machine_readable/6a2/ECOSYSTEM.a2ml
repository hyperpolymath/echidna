;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm — HOL-o-extension ecosystem position

(ecosystem
  ((metadata
     ((version . "0.1.0")
      (name . "HOL-o-extension")
      (type . "o-extension")
      (purpose . "Optional overlay extending HOL4 with custom theories and tactics for ECHIDNA integration")))

   (overlay-protocol
     ((base . "../HOL")
      (upstream . "https://github.com/HOL-Theorem-Prover/HOL")
      (peer-type . "o-extension")
      (activation . "source activate.sh")
      (deactivation . "unset HOL_OEXT_ACTIVE; unset HOL_OEXT_DIR")
      (switchable . #t)
      (modifies-base . #f)
      (description . "Optional-extension pattern: never touches base code, purely additive overlay that can be toggled on/off per-run. When active, extends HOL's load path with custom theories and tactics. When inactive, HOL behaves as virgin upstream.")))

   (position-in-ecosystem
     "HOL-o-extension is a peer-level sibling to the upstream HOL4 theorem prover within the ECHIDNA monorepo. It provides custom theories and tactics needed for ECHIDNA's neurosymbolic proof search without forking or modifying HOL itself. This follows the Overlay Protocol, where overlays declare their relationship to a base project and maintain strict non-modification invariants.")

   (related-projects
     ((base-project
        ((hol4
           ((relationship . "base")
            (description . "HOL4 higher-order logic theorem prover (upstream)")
            (path . "../HOL")
            (upstream . "https://github.com/HOL-Theorem-Prover/HOL")
            (interaction . "Load path extension, never modification")))))

      (parent-project
        ((echidna
           ((relationship . "parent-monorepo")
            (description . "ECHIDNA neurosymbolic theorem prover")
            (path . "..")
            (interaction . "HOL4 backend uses o-extension theories when activated")))))

      (overlay-protocol-peers
        ;; Other projects using the Overlay Protocol pattern
        ((proven-aggregate-lib
           ((relationship . "protocol-peer")
            (peer-type . "aggregate-library")
            (description . "Curated subset of proven bindings — same Overlay Protocol, different peer-type")
            (status . "active")
            (notes . "aggregate-library selects/re-exports; o-extension adds new capabilities. Both verified conformant.")))))))

   (what-this-is
     (("An optional overlay for HOL4 within ECHIDNA"
       "Custom theories for neurosymbolic proof search"
       "Additional tactics for ECHIDNA-specific proof strategies"
       "Switchable per-run — activate.sh to enable, unset to disable"
       "Part of the Overlay Protocol (peer-type: o-extension)")))

   (what-this-is-not
     (("Not a fork of HOL — upstream is rebased, never patched"
       "Not a dependency — HOL works fine without it"
       "Not an aggregate-library — it adds new things, not curates existing ones"
       "Not permanent — can be toggled off for vanilla HOL behaviour")))))
