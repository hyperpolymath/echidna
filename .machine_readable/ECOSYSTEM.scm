;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - ECHIDNA's position in the theorem proving ecosystem

(ecosystem
  ((metadata
     ((version . "1.3.0")
      (name . "ECHIDNA")
      (type . "neurosymbolic-theorem-prover")
      (purpose . "AI-assisted formal verification with soundness guarantees")))

   (position-in-ecosystem
     "ECHIDNA sits at the intersection of machine learning and formal verification, acting as a meta-tool that orchestrates multiple existing theorem provers while providing learned heuristics for proof search. It complements rather than replaces existing provers.")

   (related-projects
     ((theorem-provers
        ((coq
           ((relationship . "backend-integration")
            (description . "Coq proof assistant - ECHIDNA uses Coq as one of 12 backend provers")
            (interaction . "ECHIDNA sends Coq proof scripts via stdin/stdout, parses responses")
            (url . "https://coq.inria.fr")))

         (lean
           ((relationship . "backend-integration")
            (description . "Lean 4 theorem prover - ECHIDNA's primary prover for dependent type theory")
            (interaction . "Lean LSP integration for interactive proving, tactic parsing")
            (url . "https://lean-lang.org")))

         (isabelle
           ((relationship . "backend-integration")
            (description . "Isabelle/HOL proof assistant")
            (interaction . "Isabelle server protocol for proof checking")
            (url . "https://isabelle.in.tum.de")))

         (agda
           ((relationship . "backend-integration")
            (description . "Agda dependently typed programming language and proof assistant")
            (interaction . "Agda type checking for proof validation")
            (url . "https://wiki.portal.chalmers.se/agda")))

         (z3
           ((relationship . "backend-integration")
            (description . "Z3 SMT solver from Microsoft Research")
            (interaction . "SMT-LIB2 format for automated theorem proving")
            (url . "https://github.com/Z3Prover/z3")))

         (cvc5
           ((relationship . "backend-integration")
            (description . "CVC5 SMT solver (successor to CVC4)")
            (interaction . "SMT-LIB2 input for satisfiability checking")
            (url . "https://cvc5.github.io")))

         (acl2
           ((relationship . "backend-integration")
            (description . "ACL2 theorem prover for industrial verification")
            (interaction . "ACL2 S-expression syntax for proof scripts")
            (url . "https://www.cs.utexas.edu/users/moore/acl2")))

         (pvs
           ((relationship . "backend-integration")
            (description . "PVS (Prototype Verification System)")
            (interaction . "PVS proof commands and sequent manipulation")
            (url . "https://pvs.csl.sri.com")))

         (hol4
           ((relationship . "backend-integration")
            (description . "HOL4 higher-order logic theorem prover")
            (interaction . "Standard ML integration for HOL proofs")
            (url . "https://hol-theorem-prover.org")))

         (mizar
           ((relationship . "backend-integration")
            (description . "Mizar proof checker with natural language syntax")
            (interaction . "Mizar article format parsing")
            (url . "http://mizar.org")))

         (metamath
           ((relationship . "backend-integration")
            (description . "Metamath minimal proof checker")
            (interaction . "Metamath database format for proofs")
            (url . "http://us.metamath.org")))

         (hol-light
           ((relationship . "backend-integration")
            (description . "HOL Light proof assistant in OCaml")
            (interaction . "OCaml toplevel interaction for proofs")
            (url . "https://www.cl.cam.ac.uk/~jrh13/hol-light")))))

      (ml-frameworks
        ((julia-ecosystem
           ((relationship . "runtime-dependency")
            (description . "Julia scientific computing for ML inference")
            (packages . ("HTTP.jl" "JSON3.jl" "LinearAlgebra"))
            (usage . "Model serving, numerical computation, API server")
            (url . "https://julialang.org")))

         (flux-jl
           ((relationship . "potential-future")
            (description . "Julia ML framework for deep learning")
            (usage . "Future v2.0 Transformer models")
            (url . "https://fluxml.ai")))

         (scikit-learn
           ((relationship . "inspiration")
            (description . "Python ML library - our logistic regression mirrors sklearn API")
            (usage . "Training methodology inspiration")
            (url . "https://scikit-learn.org")))))

      (formal-verification-tools
        ((idris2
           ((relationship . "formal-validator")
            (description . "Idris2 dependent types for proof validator")
            (interaction . "Standalone validator with totality checking")
            (usage . "Formal soundness guarantees for proof terms")
            (url . "https://idris-lang.org")))

         (proven-library
           ((relationship . "validation-library")
            (description . "Idris2 library for proven-correct algorithms")
            (interaction . "Import proven modules for verified components")
            (usage . "Integrate proven-correct data structures and algorithms")
            (url . "https://github.com/hyperpolymath/proven")))

         (proptest
           ((relationship . "testing-dependency")
            (description . "Rust property-based testing framework")
            (usage . "Generate test cases for invariant validation")
            (url . "https://github.com/proptest-rs/proptest")))

         (criterion-rs
           ((relationship . "benchmarking-dependency")
            (description . "Rust statistical benchmarking")
            (usage . "Performance regression detection")
            (url . "https://github.com/bheisler/criterion.rs")))))

      (web-frameworks
        ((axum
           ((relationship . "runtime-dependency")
            (description . "Rust async web framework")
            (usage . "REST API server (port 8080)")
            (url . "https://github.com/tokio-rs/axum")))

         (rescript-react
           ((relationship . "ui-framework")
            (description . "ReScript bindings for React")
            (usage . "Type-safe UI components")
            (url . "https://rescript-lang.org")))

         (rescript-webapi
           ((relationship . "ui-dependency")
            (description . "ReScript bindings for Web APIs")
            (usage . "Fetch API for HTTP requests")
            (url . "https://github.com/rescript-lang/rescript-webapi")))))

      (parallel-computing
        ((chapel
           ((relationship . "optional-metalayer")
            (description . "Chapel high-performance parallel programming")
            (usage . "Optional parallel proof search (feature-flagged)")
            (url . "https://chapel-lang.org")))

         (zig
           ((relationship . "alternative-ffi")
            (description . "Zig systems programming language")
            (usage . "Alternative to C for FFI/ABI (safer than C)")
            (url . "https://ziglang.org")))))

      (standards
        ((rhodium-standard-repositories
           ((relationship . "sibling-standard")
            (description . "RSR compliance for repository structure")
            (compliance . "ECHIDNA follows RSR for repository layout")
            (url . "https://github.com/hyperpolymath/rhodium-standard-repositories")))

         (pmpl-license
           ((relationship . "licensing-framework")
            (description . "Palimpsest Meta-Project License")
            (usage . "Dual MIT/PMPL-1.0-or-later licensing")
            (url . "https://github.com/hyperpolymath/pmpl")))

         (cccp-protocol
           ((relationship . "development-protocol")
            (description . "Commit Convention and Contribution Protocol")
            (compliance . "ECHIDNA uses CCCP for commit messages")
            (url . "https://github.com/hyperpolymath/cccp")))))

      (community-tools
        ((echidnabot
           ((relationship . "sibling-automation")
            (description . "Automated bot for ECHIDNA repository management")
            (usage . "CI/CD automation, issue triage, release management")
            (url . "https://github.com/hyperpolymath/echidnabot")))

         (gitvisor
           ((relationship . "sibling-tool")
            (description . "Git repository supervisor and health monitor")
            (usage . "Repository metrics, code quality tracking")
            (url . "https://github.com/hyperpolymath/gitvisor")))

         (robot-repo-cleaner
           ((relationship . "maintenance-automation")
            (description . "Automated repository cleanup and standardization")
            (usage . "Workflow cleanup, dead code removal")
            (url . "https://github.com/hyperpolymath/robot-repo-cleaner")))))

      (academic-foundations
        ((machine-learning-for-theorem-proving
           ((papers . ("Kaliszyk et al. 'Deep Learning for Automated Theorem Proving'"
                      "Polu & Sutskever 'Generative Language Modeling for Automated Theorem Proving'"
                      "First et al. 'TacticZero: Learning to Prove Theorems from Scratch with Deep Reinforcement Learning'"))
            (relationship . "theoretical-foundation")
            (contribution . "ECHIDNA applies these techniques with added soundness guarantees")))

         (neurosymbolic-ai
           ((papers . ("Garcez et al. 'Neurosymbolic AI: The 3rd Wave'"
                      "Lamb et al. 'Graph Neural Networks for Theorem Proving'"
                      "d'Avila Garcez & Lamb 'Neurosymbolic AI: The State of the Art'"))
            (relationship . "paradigm-alignment")
            (contribution . "ECHIDNA exemplifies neurosymbolic approach: neural learning + symbolic verification")))

         (dependent-type-theory
           ((references . ("Martin-Löf 'Intuitionistic Type Theory'"
                          "Coquand & Huet 'The Calculus of Constructions'"
                          "Univalent Foundations Program 'Homotopy Type Theory'"))
            (relationship . "theoretical-basis")
            (contribution . "ECHIDNA supports dependent type provers (Coq, Lean, Agda, Idris2)")))))

      (potential-integrations
        ((mathlib
           ((description . "Lean's mathematical library")
            (potential . "Future integration for mathematical theorem search")
            (priority . "high")
            (timeline . "v2.0")))

         (opencyc
           ((description . "Open source version of Cyc knowledge base")
            (potential . "Domain knowledge for premise selection")
            (priority . "medium")
            (timeline . "v2.0")))

         (isabelle-afp
           ((description . "Archive of Formal Proofs for Isabelle")
            (potential . "Training data source for Isabelle proofs")
            (priority . "medium")
            (timeline . "v1.4")))

         (coq-platform
           ((description . "Curated Coq package distribution")
            (potential . "Integration with standard Coq libraries")
            (priority . "medium")
            (timeline . "v1.4")))))))

   (what-this-is
     (("A neurosymbolic theorem proving system that combines machine learning with formal verification"
       "An orchestrator for 12 different theorem provers with learned heuristics"
       "A research platform for ML-guided proof search with soundness guarantees"
       "A production tool for formal verification with AI assistance"
       "An educational resource for learning theorem proving with AI guidance")))

   (what-this-is-not
     (("Not a replacement for human mathematicians or proof engineers"
       "Not a 'black box' that magically proves theorems - transparency is key"
       "Not unsound - ML suggests, provers verify, no false proofs possible"
       "Not limited to one prover - supports 12 backends for maximum coverage"
       "Not closed-source - fully open MIT/PMPL licensed"
       "Not research-only - production-ready v1.3 available now")))

   (ecosystem-contributions
     (("First production neurosymbolic theorem prover with 12 backends"
       "Open-source reference implementation of ML + formal verification"
       "Comprehensive trust framework (benchmarking, property tests, formal validation, anomaly detection)"
       "Training data extraction methodology from proof files"
       "HTTP/REST architecture for language-agnostic prover integration"
       "Documentation spanning academic, developer, user, and layperson audiences")))

   (community-engagement
     ((target-audiences
        (("Researchers: Novel neurosymbolic architecture for study"
          "Educators: Teaching tool for theorem proving concepts"
          "Practitioners: Production verification for software/hardware"
          "Students: Learn formal methods with AI assistance"
          "Open-source community: Contribute to cutting-edge AI+verification")))

      (contribution-opportunities
        (("Add support for new theorem provers"
          "Improve ML models (Transformers, premise selection)"
          "Expand training data corpus"
          "Build domain-specific tactic libraries"
          "Create tutorials and educational content"
          "Integrate with existing proof libraries (Mathlib, AFP, etc.)"
          "Develop better UI/UX for proof exploration")))))))
