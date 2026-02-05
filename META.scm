;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Meta-level project information

(define meta
  '((architecture-decisions
     ((adr-001
       (status "accepted")
       (date "2026-01-10")
       (context "Soundness guarantee architecture")
       (decision "ML suggests tactics, provers verify. No unsound proofs possible.")
       (consequences "Users can trust results. ML failures caught by prover rejection."))

      (adr-002
       (status "accepted")
       (date "2026-01-12")
       (context "Multi-prover coverage")
       (decision "12 prover backends across 4 tiers for maximum technique coverage.")
       (consequences "Broad logic coverage. Maintenance burden mitigated by tiered priority."))

      (adr-003
       (status "accepted")
       (date "2026-01-15")
       (context "Language stack selection")
       (decision "Julia ML + Rust core + ReScript UI. HTTP boundaries between layers.")
       (consequences "Each language best-in-class for its role. Build complexity managed by clear separation."))

      (adr-004
       (status "accepted")
       (date "2026-01-25")
       (context "Trust framework design")
       (decision "Four layers: Criterion benchmarks, PropTest properties, Idris2 formal validator, anomaly detection.")
       (consequences "Multi-layer validation. Addresses 'LLM bullshit' concern with evidence."))

      (adr-005
       (status "accepted")
       (date "2026-01-28")
       (context "Chapel parallel proof search")
       (decision "Optional metalayer via feature flag. PoC validated with 9/12 provers.")
       (consequences "Massive speedup available. Not required for core functionality."))

      (adr-006
       (status "proposed")
       (date "2026-02-05")
       (context "Correctness certification pipeline")
       (decision "Add end-to-end certification: every proof output includes machine-checkable certificate, provenance chain, and multi-prover cross-validation.")
       (consequences "Users get cryptographic proof of correctness. Enables regulatory compliance."))

      (adr-007
       (status "proposed")
       (date "2026-02-05")
       (context "Chapel integration strategy")
       (decision "Chapel calls Rust via C FFI for prover execution. Julia provides neural guidance via HTTP. Chapel orchestrates parallel search with neural-guided beam search.")
       (consequences "Unifies all three compute layers. Chapel gets real provers instead of simulation."))))

    (development-practices
     (code-style "Language-specific conventions with linting")
     (security
       (principle "Defense in depth")
       (practices ("Input sanitization" "No shell injection" "CORS validation"
                   "No secrets in source" "cargo audit")))
     (testing "Unit + property + integration + formal + benchmarks")
     (versioning "SemVer")
     (documentation "AsciiDoc + Rustdoc + Julia docstrings")
     (branching "main stable, feature branches, PR required"))

    (design-rationale
     (("Soundness over performance — never sacrifice correctness"
       "Transparency over magic — users understand why tactics are suggested"
       "Evidence over claims — trust framework provides receipts"
       "Accessibility over elitism — UI makes proving approachable")))))
