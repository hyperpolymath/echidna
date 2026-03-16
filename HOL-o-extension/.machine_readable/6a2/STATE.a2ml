;; SPDX-License-Identifier: PMPL-1.0-or-later
;; STATE.scm — HOL-o-extension project state

(state
  ((metadata
     ((version . "0.1.0")
      (last-updated . "2026-03-07")
      (author . "Jonathan D.A. Jewell")))

   (project-context
     ((name . "HOL-o-extension")
      (type . "o-extension")
      (base . "HOL4 Theorem Prover")
      (parent . "ECHIDNA")))

   (current-position
     ((phase . "scaffolding")
      (completion . 5)
      (status . "Directory structure and overlay protocol declared. Theories and tactics not yet populated.")))

   (route-to-mvp
     ((milestone-1
        ((name . "Activation mechanism")
         (status . "complete")
         (description . "activate.sh sets environment for HOL load path extension")))
      (milestone-2
        ((name . "First custom theory")
         (status . "pending")
         (description . "Create an ECHIDNA-specific HOL4 theory (e.g., trust levels, confidence types)")))
      (milestone-3
        ((name . "First custom tactic")
         (status . "pending")
         (description . "Create an ECHIDNA-specific HOL4 tactic (e.g., neurosymbolic_suggest)")))
      (milestone-4
        ((name . "ECHIDNA HOL4 backend integration")
         (status . "pending")
         (description . "Wire o-extension into ECHIDNA's HOL4 prover backend")))))

   (blockers-and-issues
     ((none-currently . #t)))

   (critical-next-actions
     (("Define first custom HOL4 theory for ECHIDNA trust types"
       "Create neurosymbolic tactic stubs"
       "Test activate/deactivate cycle end-to-end")))))
