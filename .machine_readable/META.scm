;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - ECHIDNA meta-level information and architectural decisions

(define echidna-meta
  `((metadata
      ((name . "ECHIDNA")
       (full-name . "Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance")
       (tagline . "Neurosymbolic Theorem Proving with Formal Guarantees")
       (version . "1.3.0")
       (status . "production-ready")
       (license . "MIT OR Palimpsest-0.6")
       (authors . ("Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"))
       (created . "2026-01-10")
       (updated . "2026-01-29")
       (repository . "https://github.com/hyperpolymath/echidna")))

    (architecture-decisions
      ((adr-001
         ((title . "Neurosymbolic Architecture: ML Suggests, Provers Verify")
          (status . "accepted")
          (date . "2026-01-10")
          (context . "Need to combine neural ML predictions with formal verification to ensure soundness while benefiting from learned heuristics")
          (decision . "Implement two-layer architecture where ML models suggest tactics but formal provers always verify. This guarantees no unsound proofs while leveraging ML for search guidance.")
          (consequences
            ((positive . ("Formal soundness guarantee - no false proofs possible"
                         "ML improves over time with more training data"
                         "Users can trust results completely"
                         "Best of both worlds: speed + correctness"))
             (negative . ("ML suggestions may be rejected by prover"
                         "Requires maintaining both ML and prover infrastructure"
                         "Training data collection effort"))
             (mitigation . ("Anomaly detection catches ML failures early"
                           "Multi-prover consensus validates suggestions"
                           "Automated training data extraction"))))))

       (adr-002
         ((title . "12 Prover Backends for Maximum Coverage")
          (status . "accepted")
          (date . "2026-01-12")
          (context . "Different theorem provers excel at different domains. Need broad coverage of proof techniques and logics.")
          (decision . "Support 12 major theorem provers across 3 tiers: Interactive (Coq, Lean, Isabelle, Agda), SMT (Z3, CVC5), Specialized (ACL2, PVS, HOL4, Mizar, HOL Light, Metamath)")
          (consequences
            ((positive . ("Maximum proof technique coverage"
                         "Users choose best tool for their domain"
                         "Cross-prover validation possible"
                         "Community support from multiple ecosystems"))
             (negative . ("Maintenance burden for 12 integrations"
                         "Installation complexity"
                         "Version compatibility challenges"))
             (mitigation . ("Tiered architecture with core 4 provers priority"
                           "Automated testing for all backends"
                           "Docker containers for easy deployment"))))))

       (adr-003
         ((title . "Julia for ML, Rust for Core, ReScript for UI")
          (status . "accepted")
          (date . "2026-01-15")
          (context . "Need performant, type-safe stack with good ML support")
          (decision . "Use Julia for ML (great scientific computing), Rust for core logic (safety + speed), ReScript for UI (type-safe JS)")
          (consequences
            ((positive . ("Julia: Excellent ML ecosystem, fast numerical computing"
                         "Rust: Memory safety, zero-cost abstractions, async"
                         "ReScript: Type safety for frontend, compiles to clean JS"
                         "Each language best-in-class for its role"))
             (negative . ("Three languages to maintain"
                         "Developers need polyglot skills"
                         "Build complexity"))
             (mitigation . ("Clear separation of concerns"
                           "HTTP API boundaries between components"
                           "Comprehensive documentation for each layer"))))))

       (adr-004
         ((title . "Trust Framework: Benchmarking + Property Testing + Formal Verification + Anomaly Detection")
          (status . "accepted")
          (date . "2026-01-25")
          (context . "Users need assurance that ECHIDNA is 'not LLM bullshit' but formally sound")
          (decision . "Implement four-layer trust framework: (1) Criterion.rs benchmarking for performance regression, (2) PropTest property-based testing for invariants, (3) Idris2 dependent-type validator for formal correctness, (4) Anomaly detection for ML failures")
          (consequences
            ((positive . ("Multi-layer validation catches different error types"
                         "Formal proof of soundness theorem"
                         "Performance tracking over time"
                         "Early detection of ML overconfidence"))
             (negative . ("Additional development complexity"
                         "Idris2 learning curve"
                         "Test suite maintenance"))
             (mitigation . ("Comprehensive documentation"
                           "Automated CI/CD integration"
                           "FAQ addressing 'LLM bullshit' concerns"))))))

       (adr-005
         ((title . "Chapel for Optional Parallel Proof Search")
          (status . "accepted")
          (date . "2026-01-28")
          (context . "Need high-performance parallel proof search across multiple provers simultaneously")
          (decision . "Use Chapel as optional metalayer for coforall-based parallelism. Make it 100% optional via feature flag and trait abstraction.")
          (consequences
            ((positive . ("Massive speedup with parallel search"
                         "Proof quality selection (choose best of N proofs)"
                         "Robustness via multi-prover consensus"
                         "Chapel's elegant parallelism model"))
             (negative . ("Additional dependency"
                         "Chapel installation complexity"
                         "Limited Chapel community"))
             (mitigation . ("Feature flag makes it optional"
                           "Podman container for easy Chapel usage"
                           "Fallback to sequential search"
                           "Zig FFI alternative documented"))))))

       (adr-006
         ((title . "HTTP/REST APIs for Inter-Component Communication")
          (status . "accepted")
          (date . "2026-01-29")
          (context . "Need language-agnostic communication between Julia ML, Rust core, and ReScript UI")
          (decision . "Use HTTP/REST APIs with JSON payloads. Julia HTTP.jl server on port 8090, Rust Axum server on port 8080, ReScript Fetch API.")
          (consequences
            ((positive . ("Language-agnostic boundaries"
                         "Easy to test components independently"
                         "Standard protocols, wide tool support"
                         "Can scale to distributed deployment"))
             (negative . ("Network overhead vs in-process calls"
                         "Serialization/deserialization cost"
                         "Need error handling for network failures"))
             (mitigation . ("All services on localhost for development"
                           "Graceful degradation if ML unavailable"
                           "Connection pooling for efficiency"))))))

       (adr-007
         ((title . "Training Data Extraction from Example Proofs")
          (status . "accepted")
          (date . "2026-01-20")
          (context . "Need large corpus of proofs for ML training but manual labeling is expensive")
          (decision . "Extract training data directly from proof assistant source files (Coq .v, Lean .lean, etc.). Parse proof scripts to get goal-tactic pairs.")
          (consequences
            ((positive . ("Automated data collection"
                         "Real-world proof patterns"
                         "Easy to expand corpus"
                         "No manual labeling needed"))
             (negative . ("Parser complexity for each prover format"
                         "Quality depends on example code quality"
                         "May capture bad practices from examples"))
             (mitigation . ("Curate example sources carefully"
                           "Balance across provers (avoid 69% Coq imbalance)"
                           "Manual validation of extracted data"))))))

       (adr-008
         ((title . "Logistic Regression for MVP ML Model")
          (status . "accepted")
          (date . "2026-01-22")
          (context . "Need simple, interpretable ML model for first version before moving to deep learning")
          (decision . "Use bag-of-words encoding + logistic regression for tactic prediction. Simple, fast, interpretable.")
          (consequences
            ((positive . ("Fast training and inference"
                         "Interpretable coefficients"
                         "Low compute requirements"
                         "Good baseline for comparison"))
             (negative . ("Limited expressiveness vs deep learning"
                         "Doesn't capture sequential dependencies"
                         "Simple bag-of-words loses structure"))
             (mitigation . ("Plan migration to Transformer models in v2.0"
                           "Current model sufficient for 65% top-1 accuracy"
                           "Focus on infrastructure first, model later"))))))))

    (development-practices
      ((code-style
         ((rust . "Follow Rust API guidelines, use clippy, rustfmt")
          (julia . "Follow Julia style guide, use JuliaFormatter.jl")
          (rescript . "Follow ReScript conventions, compile with warnings as errors")
          (documentation . "Every public API needs docstring with examples")))

       (security
         ((principle . "Defense in depth")
          (practices . ("All prover inputs sanitized"
                       "No shell injection vulnerabilities"
                       "CORS enabled but origin validation"
                       "Secrets never in source code"
                       "Dependency scanning via cargo audit"))))

       (testing
         ((unit-tests . "Every module has unit tests")
          (property-tests . "Core invariants tested with PropTest")
          (integration-tests . "End-to-end flow validated")
          (benchmarks . "Performance regressions caught by Criterion.rs")
          (formal-verification . "Proof validator in Idris2 for critical paths")))

       (versioning
         ((scheme . "Semantic versioning (major.minor.patch)")
          (policy . "Major: breaking changes, Minor: features, Patch: bugfixes")
          (compatibility . "Maintain API compatibility within major version")))

       (documentation
         ((principle . "Documentation as code")
          (formats . ("Markdown for guides"
                     "Rustdoc for Rust API"
                     "Julia docstrings for Julia code"
                     "ReScript docstrings for UI components"))
          (audiences . ("Academic: rigorous explanation with citations"
                       "Developer: API reference, architecture deep-dive"
                       "User: tutorials, how-to guides, examples"
                       "Layperson: high-level overview, no jargon"))))

       (branching
         ((main . "Production-ready code only")
          (develop . "Integration branch for features")
          (feature . "feature/name for new work")
          (hotfix . "hotfix/issue-number for urgent fixes")
          (policy . "All merges via pull request with review")))))

    (design-rationale
      ((why-neurosymbolic
         "Neural networks alone can hallucinate false proofs. Symbolic provers alone require expert knowledge. Neurosymbolic combines ML's learning ability with formal verification's soundness guarantee.")

       (why-twelve-provers
         "Different provers excel at different logics and domains. Coq for dependent types, Z3 for SMT, ACL2 for industrial verification. Supporting 12 provers means users can choose the best tool for their specific problem.")

       (why-julia-ml
         "Julia has the best scientific computing ecosystem outside Python, with superior performance. It's designed for numerical work, has great ML libraries, and compiles to efficient native code. Better than Python for production ML serving.")

       (why-rust-core
         "Rust provides memory safety without garbage collection overhead. Zero-cost abstractions mean high-level code compiles to fast machine code. Async/await for concurrent prover execution. Strong type system catches bugs at compile time.")

       (why-rescript-ui
         "ReScript compiles to clean, readable JavaScript while providing OCaml-level type safety. Catches UI bugs at compile time that would be runtime errors in TypeScript. Better than raw JS, more pragmatic than Elm.")

       (why-http-apis
         "HTTP boundaries between components allow independent development, testing, and deployment. Language-agnostic interfaces. Can scale from single-machine to distributed. Standard protocols with excellent tooling.")

       (why-trust-framework
         "Users must trust that ECHIDNA proofs are sound. Multi-layer validation (benchmarking, property tests, formal verification, anomaly detection) provides evidence. Addresses 'LLM bullshit' concern directly with formal guarantees.")

       (why-chapel-optional
         "Not everyone needs parallel proof search, and Chapel installation is complex. Making it optional (via feature flag and trait abstraction) means core users aren't burdened, but power users can enable massive speedups.")

       (why-training-from-examples
         "Manual proof labeling doesn't scale. Extracting from existing proof files gives us real-world patterns automatically. We can expand corpus easily by adding more example files.")

       (why-logistic-regression-mvp
         "Start simple, validate infrastructure, then add complexity. Logistic regression is fast, interpretable, and good enough for 65% accuracy. Focus on getting the pipeline right before investing in deep learning.")))

    (philosophical-commitments
      ((soundness-over-performance
         "ECHIDNA will NEVER sacrifice correctness for speed. If ML suggests a tactic the prover rejects, we trust the prover. Formal verification is non-negotiable.")

       (transparency-over-magic
         "Users should understand why ECHIDNA suggests a tactic. Confidence scores, premise explanations, aspect tags all provide interpretability. No black-box magic.")

       (community-over-vendor-lock
         "ECHIDNA uses open standards (HTTP/REST), open-source provers, permissive licenses (MIT/Palimpsest). No proprietary lock-in. Users own their proofs.")

       (accessibility-over-elitism
         "Theorem proving should be accessible to newcomers, not just PhD mathematicians. UI makes it approachable. Documentation explains concepts. Examples show the way.")

       (evidence-over-claims
         "Trust framework provides evidence of correctness (benchmarks, tests, formal proofs). We don't ask users to 'just trust us' - we show receipts.")))

    (future-vision
      ((v2.0-goals
         (("Deep learning models (Transformers) for better prediction accuracy"
           "Premise selection with neural retrieval"
           "Proof step generation, not just tactic suggestion"
           "OpenCyc integration for domain knowledge"
           "Multi-prover consensus voting"
           "Proof explanation in natural language")))

       (v3.0-goals
         (("Automated theorem discovery (conjecture generation)"
           "Cross-domain knowledge transfer"
           "Interactive proof refinement with human-in-the-loop"
           "Proof repair for failing proofs"
           "Integration with mathematical libraries (Mathlib, Coq stdlib)"
           "Cloud deployment with GPU acceleration")))

       (long-term-dream
         "ECHIDNA as the 'GitHub Copilot for theorem proving' - an AI pair programmer that helps mathematicians and verification engineers prove theorems faster and more reliably. Not replacing human insight, but amplifying it.")))))
