;; SPDX-License-Identifier: PMPL-1.0-or-later
;; STATE.scm - Current project state

(define state
  '((metadata
     (version "1.0")
     (schema-version "1.0")
     (created "2026-02-04")
     (updated "2026-02-04")
     (project "echidna")
     (repo "hyperpolymath/echidna"))

    (project-context
     (name "echidna")
     (tagline "TODO: Add project description")
     (tech-stack ()))

    (current-position
     (phase "development")
     (overall-completion 0)
     (components ())
     (working-features ()))

    (route-to-mvp
     (milestones
      ((milestone-id "m1")
       (name "Initial Setup")
       (items ("Add project description"
               "Define tech stack"
               "Set up initial features")))))

    (blockers-and-issues
     (critical ())
     (high ())
     (medium ())
     (low ()))

    (critical-next-actions
     (immediate ("Update STATE.scm with project details"))
     (this-week ())
     (this-month ()))))
