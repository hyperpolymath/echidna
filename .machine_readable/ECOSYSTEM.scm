;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - ECHIDNA's position in the theorem proving ecosystem

(ecosystem
  ((metadata
     ((version . "1.5.0")
      (name . "ECHIDNA")
      (type . "neurosymbolic-theorem-prover")
      (purpose . "AI-assisted formal verification with trust-hardened soundness guarantees")))

   (position-in-ecosystem
     "ECHIDNA sits at the intersection of machine learning and formal verification, acting as a meta-tool that orchestrates 30 theorem provers, SMT solvers, ATPs, and constraint solvers. It provides a trust-hardened verification pipeline (integrity checking, portfolio solving, certificate verification, axiom tracking, sandboxing, and confidence scoring) while using learned heuristics for proof search. It complements rather than replaces existing provers.")

   (related-projects
     ((theorem-provers
        ;; Tier 1: Interactive Proof Assistants (small kernel)
        ((coq
           ((relationship . "backend-integration")
            (description . "Coq/Rocq proof assistant with small trusted kernel")
            (interaction . "Proof scripts via stdin/stdout, coqchk certificate checking")
            (url . "https://coq.inria.fr")))

         (lean
           ((relationship . "backend-integration")
            (description . "Lean 4 theorem prover with dependent types")
            (interaction . "LSP integration, lean4checker certificate checking")
            (url . "https://lean-lang.org")))

         (isabelle
           ((relationship . "backend-integration")
            (description . "Isabelle/HOL proof assistant")
            (interaction . "Server protocol for proof checking")
            (url . "https://isabelle.in.tum.de")))

         (agda
           ((relationship . "backend-integration")
            (description . "Agda dependently typed programming language")
            (interaction . "Type checking for proof validation")
            (url . "https://wiki.portal.chalmers.se/agda")))

         (idris2
           ((relationship . "backend-integration")
            (description . "Idris2 with dependent types, also used as ABI definition language")
            (interaction . "Type checking with totality verification")
            (url . "https://idris-lang.org")))

         (fstar
           ((relationship . "backend-integration")
            (description . "F* verification-oriented programming language")
            (interaction . "Dependent types with effects, small kernel")
            (url . "https://fstar-lang.org")))

         ;; Tier 2: SMT Solvers
         (z3
           ((relationship . "backend-integration")
            (description . "Z3 SMT solver from Microsoft Research")
            (interaction . "SMT-LIB2 format, portfolio cross-checking with CVC5")
            (url . "https://github.com/Z3Prover/z3")))

         (cvc5
           ((relationship . "backend-integration")
            (description . "CVC5 SMT solver with Alethe proof certificates")
            (interaction . "SMT-LIB2, Alethe certificate generation and checking")
            (url . "https://cvc5.github.io")))

         (altergo
           ((relationship . "backend-integration")
            (description . "Alt-Ergo SMT solver for software verification")
            (interaction . "Native and SMT-LIB2 format")
            (url . "https://alt-ergo.ocamlpro.com")))

         ;; Auto-active verifiers
         (dafny
           ((relationship . "backend-integration")
            (description . "Dafny auto-active verification language")
            (interaction . "Dafny source verification via Boogie/Z3 pipeline")
            (url . "https://dafny.org")))

         (why3
           ((relationship . "backend-integration")
            (description . "Why3 multi-prover verification platform")
            (interaction . "WhyML format, orchestrates multiple backend provers")
            (url . "https://why3.lri.fr")))

         ;; Specialised
         (metamath
           ((relationship . "backend-integration")
            (description . "Metamath minimal proof checker (tiny kernel)")
            (interaction . "Metamath database format")
            (url . "https://us.metamath.org")))

         (hol-light
           ((relationship . "backend-integration")
            (description . "HOL Light proof assistant (small kernel)")
            (interaction . "OCaml toplevel, OpenTheory interop")
            (url . "https://www.cl.cam.ac.uk/~jrh13/hol-light")))

         (mizar
           ((relationship . "backend-integration")
            (description . "Mizar mathematical vernacular proof checker")
            (interaction . "Mizar article format")
            (url . "https://mizar.org")))

         (hol4
           ((relationship . "backend-integration")
            (description . "HOL4 higher-order logic theorem prover")
            (interaction . "SML integration, OpenTheory interop")
            (url . "https://hol-theorem-prover.org")))

         (pvs
           ((relationship . "backend-integration")
            (description . "PVS Prototype Verification System")
            (interaction . "PVS proof commands")
            (url . "https://pvs.csl.sri.com")))

         (acl2
           ((relationship . "backend-integration")
            (description . "ACL2 theorem prover for industrial verification")
            (interaction . "S-expression syntax")
            (url . "https://www.cs.utexas.edu/users/moore/acl2")))

         (tlaps
           ((relationship . "backend-integration")
            (description . "TLA+ Proof System for distributed systems")
            (interaction . "TLA+ proof language")
            (url . "https://tla.msr-inria.inria.fr/tlaps")))

         (twelf
           ((relationship . "backend-integration")
            (description . "Twelf logical framework (LF type theory)")
            (interaction . "Elf format")
            (url . "https://twelf.org")))

         (nuprl
           ((relationship . "backend-integration")
            (description . "Nuprl constructive type theory prover")
            (interaction . "Nuprl proof format")
            (url . "https://www.nuprl.org")))

         (minlog
           ((relationship . "backend-integration")
            (description . "Minlog minimal logic proof system")
            (interaction . "Minlog format")
            (url . "https://minlog-system.de")))

         (imandra
           ((relationship . "backend-integration")
            (description . "Imandra ML-based automated reasoning")
            (interaction . "IML format")
            (url . "https://imandra.ai")))

         ;; First-Order ATPs
         (vampire
           ((relationship . "backend-integration")
            (description . "Vampire first-order ATP (TPTP format)")
            (interaction . "TPTP input, TSTP proof certificates")
            (url . "https://vprover.github.io")))

         (eprover
           ((relationship . "backend-integration")
            (description . "E Prover equational first-order ATP")
            (interaction . "TPTP input, TSTP proof certificates")
            (url . "https://eprover.org")))

         (spass
           ((relationship . "backend-integration")
            (description . "SPASS first-order ATP (DFG format)")
            (interaction . "DFG and TPTP formats")
            (url . "https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench")))

         ;; Constraint / Optimisation Solvers
         (glpk
           ((relationship . "backend-integration")
            (description . "GNU Linear Programming Kit")
            (interaction . "LP/MPS format")
            (url . "https://www.gnu.org/software/glpk")))

         (scip
           ((relationship . "backend-integration")
            (description . "SCIP mixed-integer nonlinear programming solver")
            (interaction . "PIP/ZIMPL format")
            (url . "https://scipopt.org")))

         (minizinc
           ((relationship . "backend-integration")
            (description . "MiniZinc constraint modelling language")
            (interaction . "MZN/DZN format")
            (url . "https://www.minizinc.org")))

         (chuffed
           ((relationship . "backend-integration")
            (description . "Chuffed lazy clause generation CP solver")
            (interaction . "FlatZinc format")
            (url . "https://github.com/chuffed/chuffed")))

         (ortools
           ((relationship . "backend-integration")
            (description . "Google OR-Tools constraint/optimisation solver")
            (interaction . "Constraint programming API")
            (url . "https://developers.google.com/optimization")))))

      (proof-exchange-formats
        ((opentheory
           ((relationship . "interoperability")
            (description . "OpenTheory universal format for HOL family")
            (usage . "Cross-checking between HOL4, HOL Light, Isabelle/HOL")
            (url . "https://www.gilith.com/opentheory")))

         (dedukti
           ((relationship . "interoperability")
            (description . "Dedukti/Lambdapi universal proof format")
            (usage . "Universal proof kernel (lambda-Pi calculus modulo rewriting)")
            (url . "https://deducteam.github.io")))

         (alethe
           ((relationship . "certificate-format")
            (description . "Alethe proof format for SMT solvers")
            (usage . "Certificate verification for CVC5 proofs")
            (url . "https://verit.loria.fr/documentation/alethe-spec.pdf")))

         (drat-lrat
           ((relationship . "certificate-format")
            (description . "DRAT/LRAT proof formats for SAT solvers")
            (usage . "Independent certificate checking via drat-trim")
            (url . "https://www.cs.utexas.edu/~marijn/drat-trim")))

         (tstp
           ((relationship . "certificate-format")
            (description . "TSTP proof format for first-order ATPs")
            (usage . "Proof output from Vampire and E Prover")
            (url . "https://www.tptp.org/TSTP.html")))))

      (ml-frameworks
        ((julia-ecosystem
           ((relationship . "runtime-dependency")
            (description . "Julia scientific computing for ML inference")
            (packages . ("HTTP.jl" "JSON3.jl" "LinearAlgebra"))
            (usage . "Logistic regression tactic prediction (port 8090)")
            (url . "https://julialang.org")))

         (flux-jl
           ((relationship . "potential-future")
            (description . "Julia ML framework for deep learning")
            (usage . "v2.0 Transformer models for premise selection")
            (url . "https://fluxml.ai")))))

      (trust-infrastructure
        ((blake3
           ((relationship . "cryptographic-dependency")
            (description . "BLAKE3 hash function for fast integrity checks")
            (usage . "Runtime solver re-verification, certificate hashing")
            (url . "https://blake3.io")))

         (shake3-512
           ((relationship . "cryptographic-dependency")
            (description . "SHAKE (SHA-3 XOF) for provenance hashing")
            (usage . "Solver binary integrity manifests (via tiny-keccak)")
            (url . "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf")))

         (proptest
           ((relationship . "testing-dependency")
            (description . "Rust property-based testing framework")
            (usage . "21 property-based tests for trust invariants")
            (url . "https://github.com/proptest-rs/proptest")))

         (podman
           ((relationship . "sandbox-runtime")
            (description . "Podman container runtime for solver isolation")
            (usage . "Network-disabled, read-only, resource-limited solver execution")
            (url . "https://podman.io")))

         (bubblewrap
           ((relationship . "sandbox-fallback")
            (description . "Bubblewrap namespace isolation")
            (usage . "Lightweight solver sandboxing when Podman unavailable")
            (url . "https://github.com/containers/bubblewrap")))))

      (web-frameworks
        ((axum
           ((relationship . "runtime-dependency")
            (description . "Rust async web framework")
            (usage . "REST API server (port 8000), core HTTP server")
            (url . "https://github.com/tokio-rs/axum")))

         (async-graphql
           ((relationship . "runtime-dependency")
            (description . "Rust async GraphQL framework")
            (usage . "GraphQL API server (port 8080)")
            (url . "https://github.com/async-graphql/async-graphql")))

         (tonic
           ((relationship . "runtime-dependency")
            (description . "Rust gRPC framework")
            (usage . "gRPC server with bidirectional streaming (port 50051)")
            (url . "https://github.com/hyperium/tonic")))

         (rescript-react
           ((relationship . "ui-framework")
            (description . "ReScript bindings for React")
            (usage . "Type-safe UI components (28 files)")
            (url . "https://rescript-lang.org")))))

      (parallel-computing
        ((chapel
           ((relationship . "optional-metalayer")
            (description . "Chapel high-performance parallel programming")
            (usage . "Optional parallel proof dispatch across 30 provers")
            (url . "https://chapel-lang.org")))))

      (standards
        ((rhodium-standard-repositories
           ((relationship . "sibling-standard")
            (description . "RSR compliance for repository structure")
            (compliance . "ECHIDNA follows RSR for repository layout, 17 CI workflows")
            (url . "https://github.com/hyperpolymath/rhodium-standard-repositories")))

         (pmpl-license
           ((relationship . "licensing-framework")
            (description . "Palimpsest Meta-Project License")
            (usage . "PMPL-1.0-or-later (sole license)")
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

         (panic-attacker
           ((relationship . "security-scanner")
            (description . "Security weakness scanner for repositories")
            (usage . "VeriSimDB integration for weakness tracking")
            (url . "https://github.com/hyperpolymath/panic-attacker")))

         (verisimdb
           ((relationship . "security-database")
            (description . "Verisimilitude Database for weakness tracking")
            (usage . "Aggregates scan results across repos")
            (url . "https://github.com/hyperpolymath/verisimdb")))

         (hypatia
           ((relationship . "sibling-intelligence")
            (description . "Neurosymbolic CI/CD intelligence platform")
            (usage . "VeriSimDB connector, pattern detection, fleet dispatch")
            (url . "https://github.com/hyperpolymath/hypatia")))

         (opsm
           ((relationship . "sibling-tool")
            (description . "Federated multi-language package manager with cryptographic security")
            (usage . "Formal verification of package distribution pipelines, dependency integrity proofs")
            (url . "https://github.com/hyperpolymath/odds-and-sods-package-manager")))))

      (potential-integrations
        ((mathlib
           ((description . "Lean's mathematical library")
            (potential . "Training data and theorem search")
            (priority . "high")
            (timeline . "v2.0")))

         (tamarin-proverif
           ((description . "Security protocol verification tools")
            (potential . "Cipherbot integration for protocol proofs")
            (priority . "medium")
            (timeline . "v2.0")))

         (isabelle-afp
           ((description . "Archive of Formal Proofs for Isabelle")
            (potential . "Training data source")
            (priority . "medium")
            (timeline . "v2.0")))))))

   (what-this-is
     (("A neurosymbolic theorem proving system with 30 prover backends"
       "A trust-hardened verification pipeline with 5-level confidence scoring"
       "An orchestrator for theorem provers, SMT solvers, ATPs, and constraint solvers"
       "A platform for ML-guided proof search with formal soundness guarantees"
       "A multi-objective proof optimiser using Pareto frontier analysis")))

   (what-this-is-not
     (("Not a replacement for human mathematicians or proof engineers"
       "Not a black box -- transparency via trust levels, axiom reports, certificates"
       "Not unsound -- ML suggests, provers verify, dangerous axioms are tracked and rejected"
       "Not limited to one prover -- 30 backends across 8 tiers"
       "Not closed-source -- fully open PMPL-1.0-or-later licensed")))

   (ecosystem-contributions
     (("First trust-hardened neurosymbolic theorem prover with 30 backends"
       "Open-source reference for solver integrity verification (SHAKE3-512 + BLAKE3)"
       "Comprehensive trust framework: integrity, portfolio, certificates, axioms, sandboxing, confidence"
       "Cross-prover proof exchange via OpenTheory and Dedukti/Lambdapi"
       "Pareto optimisation for multi-objective proof search"
       "Statistical confidence tracking with Bayesian timeout estimation")))))
