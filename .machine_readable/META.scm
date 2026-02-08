;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - ECHIDNA meta-level information and architectural decisions

(define echidna-meta
  `((metadata
      ((name . "ECHIDNA")
       (full-name . "Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance")
       (tagline . "Trust-Hardened Neurosymbolic Theorem Proving")
       (version . "1.5.0")
       (status . "production-ready")
       (license . "PMPL-1.0-or-later")
       (authors . ("Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"))
       (created . "2026-01-10")
       (updated . "2026-02-08")
       (repository . "https://github.com/hyperpolymath/echidna")))

    (architecture-decisions
      ((adr-001
         ((title . "Neurosymbolic Architecture: ML Suggests, Provers Verify")
          (status . "accepted")
          (date . "2026-01-10")
          (context . "Need to combine neural ML predictions with formal verification to ensure soundness while benefiting from learned heuristics")
          (decision . "Implement two-layer architecture where ML models suggest tactics but formal provers always verify. This guarantees no unsound proofs while leveraging ML for search guidance.")
          (consequences
            ((positive . ("Formal soundness guarantee -- no false proofs possible"
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
         ((title . "30 Prover Backends for Maximum Coverage")
          (status . "accepted")
          (date . "2026-02-08")
          (supersedes . "adr-002-original-12-provers")
          (context . "Different theorem provers, SMT solvers, ATPs, and constraint solvers excel at different domains. The trust hardening work revealed benefits of cross-checking across solver families.")
          (decision . "Support 30 backends across 8 tiers: interactive proof assistants (Agda, Coq, Lean, Isabelle, Idris2, F*), SMT solvers (Z3, CVC5, Alt-Ergo), auto-active verifiers (Dafny, Why3), specialised (Metamath, HOL Light, Mizar, HOL4, PVS, ACL2, TLAPS, Twelf, Nuprl, Minlog, Imandra), first-order ATPs (Vampire, E Prover, SPASS), and constraint solvers (GLPK, SCIP, MiniZinc, Chuffed, OR-Tools).")
          (consequences
            ((positive . ("Maximum technique coverage across all formal methods"
                         "Cross-checking between solver families (SMT, ATP, ITP)"
                         "Constraint solvers enable optimisation problems"
                         "Portfolio solving leverages solver diversity"))
             (negative . ("30 integrations to maintain"
                         "Installation complexity for full stack"
                         "Not all provers available on all platforms"))
             (mitigation . ("Tiered architecture -- core provers prioritised"
                           "Auto-detection of available provers"
                           "Podman containers for easy deployment"
                           "Graceful fallback when provers missing"))))))

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
         ((title . "Trust Framework: Multi-Layer Verification Pipeline")
          (status . "accepted")
          (date . "2026-02-08")
          (supersedes . "adr-004-original-trust-framework")
          (context . "Users need assurance that ECHIDNA proofs are sound. The v1.5 trust hardening expanded the original 4-layer framework to a comprehensive pipeline.")
          (decision . "Implement trust-hardening pipeline with 8 stages: (1) Solver binary integrity verification (SHAKE3-512 + BLAKE3), (2) Portfolio solving / cross-checking, (3) Proof certificate verification (Alethe, DRAT/LRAT, TSTP), (4) Axiom usage tracking (4 danger levels), (5) Solver sandboxing (Podman, bubblewrap), (6) 5-level confidence scoring, (7) Mutation testing for specifications, (8) Pareto optimisation for proof search")
          (consequences
            ((positive . ("8-stage pipeline catches different error types"
                         "5-level trust hierarchy gives users clear confidence signals"
                         "Dangerous axioms rejected automatically"
                         "Cross-checking detects solver bugs"
                         "Sandboxing prevents untrusted code execution"
                         "Mutation testing validates specification strength"))
             (negative . ("Pipeline adds latency to proof verification"
                         "Sandboxing requires Podman or bubblewrap"
                         "Certificate checking requires external tools"))
             (mitigation . ("Pipeline stages are configurable and optional"
                           "Fast path for trusted provers"
                           "Auto-detection of available sandboxing"
                           "Graceful fallback when tools missing"))))))

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
                           "Balance across provers"
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
                           "Focus on infrastructure first, model later"))))))

       (adr-009
         ((title . "SHAKE3-512 + BLAKE3 for Solver Integrity Verification")
          (status . "accepted")
          (date . "2026-02-08")
          (context . "Solver binaries could be tampered with, leading to silently unsound results. Need to verify integrity at startup and during runtime.")
          (decision . "Use SHAKE3-512 (FIPS 202 XOF) for provenance hashing in the TOML manifest, and BLAKE3 for fast runtime re-verification. Two-hash approach balances security (SHAKE3-512) with speed (BLAKE3 for periodic checks).")
          (consequences
            ((positive . ("Detects tampered solver binaries before use"
                         "SHAKE3-512 provides FIPS-standard provenance"
                         "BLAKE3 enables fast periodic re-checks"
                         "Manifest-based approach supports version pinning"))
             (negative . ("First-run requires computing initial hashes"
                         "Solver updates require manifest updates"
                         "Small startup overhead for integrity checking"))
             (mitigation . ("Placeholder hashes for first run"
                           "Manifest generation tooling planned"
                           "BLAKE3 is extremely fast (>10 GB/s)"))))))

       (adr-010
         ((title . "4-Level Axiom Danger Classification")
          (status . "accepted")
          (date . "2026-02-08")
          (context . "Proofs can use axioms and constructs that compromise soundness. Need to detect and report these automatically.")
          (decision . "Classify axiom usage into 4 levels: Safe (standard library), Noted (classical in constructive), Warning (incomplete markers like sorry/Admitted), Reject (known unsound like --type-in-type, mk_thm, believe_me). Rejected axioms cap trust at Level 1 regardless of other factors.")
          (consequences
            ((positive . ("Automatic detection of unsound constructs"
                         "Graduated response (warn vs reject)"
                         "Comment-aware scanning avoids false positives"
                         "Policy enforcement is configurable"))
             (negative . ("Pattern-based scanning may miss obfuscated usage"
                         "New provers need new pattern definitions"
                         "May flag intentional use of axioms"))
             (mitigation . ("Axiom report includes explanations"
                           "Users can review and override at policy level"
                           "Pattern database is extensible"))))))

       (adr-011
         ((title . "Podman-First Solver Sandboxing")
          (status . "accepted")
          (date . "2026-02-08")
          (context . "Solvers are external binaries that could execute arbitrary code. Need isolation to prevent filesystem/network access.")
          (decision . "Run solvers in sandboxed environments. Prefer Podman (--network=none, --read-only, memory/CPU/disk limits). Fall back to bubblewrap (--unshare-all). Unsandboxed mode requires explicit opt-in and logs a warning.")
          (consequences
            ((positive . ("Prevents solver escape to host system"
                         "Network isolation prevents data exfiltration"
                         "Resource limits prevent DoS"
                         "Auto-detection selects strongest available"))
             (negative . ("Podman adds latency"
                         "Container image management"
                         "Not all solvers containerise easily"))
             (mitigation . ("Unsandboxed mode for development"
                           "Bubblewrap fallback is lightweight"
                           "Auto-detection makes it transparent"))))))

       (adr-012
         ((title . "Cross-Prover Proof Exchange via OpenTheory and Dedukti")
          (status . "accepted")
          (date . "2026-02-08")
          (context . "Cross-checking proofs across prover families requires translating between proof formats. Need universal interchange formats.")
          (decision . "Support two exchange formats: OpenTheory for HOL family interop (HOL4, HOL Light, Isabelle/HOL), and Dedukti/Lambdapi as a universal proof format based on the lambda-Pi calculus modulo rewriting.")
          (consequences
            ((positive . ("HOL family cross-checking via OpenTheory"
                         "Universal format via Dedukti for any prover"
                         "Enables independent re-verification of proofs"
                         "Standards-based approach"))
             (negative . ("Not all provers have Dedukti translations"
                         "Translation may lose prover-specific information"
                         "OpenTheory limited to HOL family"))
             (mitigation . ("Focus on most commonly used provers first"
                           "Preserve original proof alongside translation"
                           "Future: add SMTCoq bridge for SMT proofs in Coq"))))))))

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
                       "Dependency scanning via cargo audit"
                       "Solver binary integrity verification (SHAKE3-512 + BLAKE3)"
                       "Solver sandboxing (Podman, bubblewrap)"
                       "Axiom usage tracking and enforcement"))))

       (testing
         ((unit-tests . "232 unit tests for all modules")
          (property-tests . "21 PropTest tests for trust invariants")
          (integration-tests . "38 end-to-end flow tests")
          (mutation-tests . "Specification mutation testing (95% threshold)")
          (formal-verification . "Proof validator in Idris2 for critical paths")))

       (versioning
         ((scheme . "Semantic versioning (major.minor.patch)")
          (policy . "Major: breaking changes, Minor: features, Patch: bugfixes")
          (compatibility . "Maintain API compatibility within major version")))

       (documentation
         ((principle . "Documentation as code")
          (formats . ("AsciiDoc for guides (README, ROADMAP, CHANGELOG)"
                     "Rustdoc for Rust API"
                     "Julia docstrings for Julia code"
                     "ReScript docstrings for UI components"))
          (audiences . ("Academic: rigorous explanation with citations"
                       "Developer: API reference, architecture deep-dive"
                       "User: tutorials, how-to guides, examples"))))

       (branching
         ((main . "Production-ready code only")
          (develop . "Integration branch for features")
          (feature . "feature/name for new work")
          (hotfix . "hotfix/issue-number for urgent fixes")
          (policy . "All merges via pull request with review")))))

    (design-rationale
      ((why-neurosymbolic
         "Neural networks alone can hallucinate false proofs. Symbolic provers alone require expert knowledge. Neurosymbolic combines ML's learning ability with formal verification's soundness guarantee.")

       (why-thirty-provers
         "Different provers excel at different logics and domains. Supporting 30 backends means users can choose the best tool for their problem, and portfolio solving can cross-check results across independent implementations.")

       (why-trust-pipeline
         "Users must trust that ECHIDNA proofs are sound. The 8-stage trust pipeline (integrity, portfolio, certificates, axioms, sandboxing, confidence, mutation, Pareto) provides evidence at every step. This directly addresses the 'LLM bullshit' concern with formal guarantees.")

       (why-five-level-hierarchy
         "Not all proofs deserve the same confidence. A sorry-laden proof from a large-TCB system is fundamentally different from a cross-checked result with certificates from small-kernel provers. The 5-level hierarchy makes this explicit.")

       (why-solver-sandboxing
         "Solver binaries are external code from diverse sources. Running them without isolation risks filesystem access, network exfiltration, and resource abuse. Sandboxing is defense-in-depth for the verification pipeline.")

       (why-julia-ml
         "Julia has the best scientific computing ecosystem outside Python, with superior performance. It's designed for numerical work, has great ML libraries, and compiles to efficient native code.")

       (why-rust-core
         "Rust provides memory safety without garbage collection overhead. Zero-cost abstractions mean high-level code compiles to fast machine code. Async/await for concurrent prover execution. Strong type system catches bugs at compile time.")

       (why-rescript-ui
         "ReScript compiles to clean, readable JavaScript while providing OCaml-level type safety. Catches UI bugs at compile time that would be runtime errors in TypeScript.")

       (why-pareto-optimisation
         "Proof search involves multiple competing objectives: speed, confidence, resource usage, proof size. Users have different priorities. Pareto frontier analysis lets ECHIDNA present the trade-offs rather than making arbitrary choices.")))

    (philosophical-commitments
      ((soundness-over-performance
         "ECHIDNA will NEVER sacrifice correctness for speed. If ML suggests a tactic the prover rejects, we trust the prover. Formal verification is non-negotiable.")

       (transparency-over-magic
         "Users should understand why ECHIDNA assigns a trust level. Confidence scores, axiom reports, certificate verification, and Pareto analysis all provide interpretability.")

       (community-over-vendor-lock
         "ECHIDNA uses open standards (HTTP/REST, OpenTheory, Dedukti), open-source provers, and a permissive license (PMPL-1.0-or-later). No proprietary lock-in.")

       (evidence-over-claims
         "The trust pipeline provides evidence of correctness (integrity checks, certificates, cross-checking, mutation scores). We don't ask users to 'just trust us' -- we show receipts.")))

    (future-vision
      ((v2.0-goals
         (("FFI/IPC bridge for API-to-prover integration"
           "Deep learning models (Transformers via Flux.jl)"
           "Premise selection with neural retrieval"
           "Tamarin/ProVerif bridge for protocol verification"
           "Production deployment configuration")))

       (v3.0-goals
         (("Automated theorem discovery (conjecture generation)"
           "Cross-domain knowledge transfer"
           "Proof repair for failing proofs"
           "Integration with mathematical libraries (Mathlib, AFP)"
           "Cloud deployment with GPU acceleration")))

       (long-term-dream
         "ECHIDNA as the trust-hardened AI pair programmer for theorem proving -- amplifying human insight with 30 provers, ML-guided search, and formal soundness guarantees that users can verify independently.")))))
