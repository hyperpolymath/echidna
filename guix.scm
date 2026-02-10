;; SPDX-License-Identifier: PMPL-1.0-or-later
;; echidna - Guix Package Definition
;; Development: guix shell -D -f guix.scm
;; Build: guix build -f guix.scm

(use-modules (guix packages)
             (guix gexp)
             (guix git-download)
             (guix build-system cargo)
             ((guix licenses) #:prefix license:)
             (gnu packages base)
             (gnu packages crates-io)
             (gnu packages rust)
             (gnu packages rust-apps)
             (gnu packages tls)
             (gnu packages pkg-config)
             (gnu packages idris)
             (gnu packages maths))

(define-public echidna
  (package
    (name "echidna")
    (version "1.5.0")
    (source (local-file "." "echidna-checkout"
                        #:recursive? #t
                        #:select? (git-predicate ".")))
    (build-system cargo-build-system)
    (arguments
     `(#:cargo-inputs
       (;; Core async runtime
        ("rust-tokio" ,rust-tokio-1)
        ("rust-async-trait" ,rust-async-trait-0.1)
        ("rust-futures" ,rust-futures-0.3)
        ;; Serialization
        ("rust-serde" ,rust-serde-1)
        ("rust-serde-json" ,rust-serde-json-1)
        ("rust-toml" ,rust-toml-0.8)
        ;; Error handling
        ("rust-anyhow" ,rust-anyhow-1)
        ("rust-thiserror" ,rust-thiserror-2)
        ;; CLI
        ("rust-clap" ,rust-clap-4)
        ("rust-colored" ,rust-colored-3)
        ("rust-indicatif" ,rust-indicatif-0.17)
        ;; Logging
        ("rust-tracing" ,rust-tracing-0.1)
        ("rust-tracing-subscriber" ,rust-tracing-subscriber-0.3)
        ;; Web/HTTP
        ("rust-axum" ,rust-axum-0.7)
        ("rust-tower" ,rust-tower-0.5)
        ("rust-tower-http" ,rust-tower-http-0.6)
        ("rust-reqwest" ,rust-reqwest-0.12)
        ;; Actor framework
        ("rust-actix" ,rust-actix-0.13)
        ;; Parsing
        ("rust-nom" ,rust-nom-7)
        ;; REPL
        ("rust-rustyline" ,rust-rustyline-15)
        ;; Hashing
        ("rust-blake3" ,rust-blake3-1)
        ("rust-tiny-keccak" ,rust-tiny-keccak-2)
        ;; Utilities
        ("rust-uuid" ,rust-uuid-1)
        ("rust-lazy-static" ,rust-lazy-static-1)
        ("rust-chrono" ,rust-chrono-0.4))
       #:cargo-development-inputs
       (("rust-proptest" ,rust-proptest-1)
        ("rust-tempfile" ,rust-tempfile-3)
        ("rust-tokio-test" ,rust-tokio-test-0.4)
        ("rust-pretty-assertions" ,rust-pretty-assertions-1))))
    (native-inputs
     (list pkg-config
           rust
           rust-cargo))
    (inputs
     (list openssl))
    (propagated-inputs
     (list z3 idris))
    (synopsis "Neurosymbolic theorem proving platform with 30 prover backends")
    (description
     "ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural
Assistance) is a trust-hardened neurosymbolic theorem proving platform.  It
supports 30 prover backends including Agda, Coq, Lean 4, Isabelle, Z3, CVC5,
and more, with a comprehensive verification pipeline featuring solver integrity
checking, proof certificate validation, axiom tracking, and confidence scoring.")
    (home-page "https://github.com/hyperpolymath/echidna")
    (license (license:non-copyleft "https://github.com/hyperpolymath/palimpsest-license"
                                   #:comment "PMPL-1.0-or-later"))))

;; For development shell
echidna
