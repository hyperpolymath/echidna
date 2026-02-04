;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Meta-level project information

(define meta
  '((architecture-decisions
     ((adr-001
       (status "accepted")
       (date "2026-02-04")
       (context "Initial project setup")
       (decision "Use standard hyperpolymath structure")
       (consequences "Consistent with other hyperpolymath projects"))))

    (development-practices
     (code-style "Follow language-specific conventions")
     (security "SPDX headers, OpenSSF Scorecard compliance")
     (testing "Required for critical functionality")
     (versioning "Semantic versioning")
     (documentation "README.adoc, inline comments")
     (branching "main branch, feature branches, PRs required"))

    (design-rationale
     ())))
