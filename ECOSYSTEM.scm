;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ECOSYSTEM.scm — echidna

(ecosystem
  (version "1.0.0")
  (name "echidna")
  (type "project")
  (purpose "*E*xtensible *C*ognitive *H*ybrid *I*ntelligence for *D*eductive *N*eural *A*ssistance")

  (position-in-ecosystem
    "Part of hyperpolymath ecosystem. Follows RSR guidelines.")

  (related-projects
    (project (name "rhodium-standard-repositories")
             (url "https://github.com/hyperpolymath/rhodium-standard-repositories")
             (relationship "standard")))

  (what-this-is "*E*xtensible *C*ognitive *H*ybrid *I*ntelligence for *D*eductive *N*eural *A*ssistance")
  (what-this-is-not "- NOT exempt from RSR compliance"))
