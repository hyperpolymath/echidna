;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Project ecosystem position

(ecosystem
 (version "1.3")
 (name "echidna")
 (type "neurosymbolic-theorem-prover")
 (purpose "AI-assisted formal verification with soundness guarantees.
   Orchestrates 12 theorem provers with learned heuristics via a
   Rust core, Julia ML layer, and ReScript UI.")

 (position-in-ecosystem
  (category "formal-methods")
  (subcategory "ai-assisted-proving")
  (unique-value
    ("First production neurosymbolic prover with 12 backends"
     "ML suggests, provers verify — no unsound proofs possible"
     "Four-layer trust framework (benchmarks, property tests, formal validator, anomaly detection)"
     "HTTP/REST architecture for language-agnostic integration")))

 (related-projects
   (("absolute-zero" "sibling-research"
     "Formal verification of CNOs. ECHIDNA could verify CNO properties.
      Shared interest in Coq/Lean proof engineering.")
    ("echidnabot" "sibling-automation"
     "GitHub bot for ECHIDNA repo management. 75% complete,
      needs container isolation and retry logic.")
    ("valence-shell" "potential-integration"
     "Filesystem operations library. Could use ECHIDNA for
      proving filesystem operation properties.")
    ("proven" "validation-library"
     "Idris2 proven-correct algorithms. Used in ECHIDNA's
      formal proof validator.")
    ("rsr-template-repo" "infrastructure"
     "Repository standards. ECHIDNA follows RSR structure.")))

 (what-this-is
  ("Neurosymbolic theorem proving platform"
   "Multi-prover orchestrator (12 backends)"
   "Research + production tool for formal verification"
   "Educational resource for AI-assisted proving"))

 (what-this-is-not
  ("Not a replacement for human proof engineers"
   "Not a black-box oracle — transparency is core"
   "Not unsound — ML only suggests, provers verify"
   "Not limited to one proof assistant")))
