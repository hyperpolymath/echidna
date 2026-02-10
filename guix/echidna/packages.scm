;; SPDX-License-Identifier: PMPL-1.0-or-later
;; Guix channel module exporting the echidna package
(define-module (echidna packages)
  #:use-module (guix packages)
  #:use-module (guix gexp)
  #:use-module (guix git-download)
  #:use-module (guix build-system cargo)
  #:use-module ((guix licenses) #:prefix license:)
  #:use-module (gnu packages base)
  #:use-module (gnu packages crates-io)
  #:use-module (gnu packages rust)
  #:use-module (gnu packages rust-apps)
  #:use-module (gnu packages tls)
  #:use-module (gnu packages pkg-config)
  #:use-module (gnu packages idris)
  #:use-module (gnu packages maths))

(define-public echidna
  (package
    (name "echidna")
    (version "1.5.0")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://github.com/hyperpolymath/echidna")
                    (commit (string-append "v" version))))
              (file-name (git-file-name name version))
              (sha256
               (base32
                "0000000000000000000000000000000000000000000000000000"))))
    (build-system cargo-build-system)
    (arguments
     `(#:cargo-inputs
       (("rust-tokio" ,rust-tokio-1)
        ("rust-async-trait" ,rust-async-trait-0.1)
        ("rust-futures" ,rust-futures-0.3)
        ("rust-serde" ,rust-serde-1)
        ("rust-serde-json" ,rust-serde-json-1)
        ("rust-toml" ,rust-toml-0.8)
        ("rust-anyhow" ,rust-anyhow-1)
        ("rust-thiserror" ,rust-thiserror-2)
        ("rust-clap" ,rust-clap-4)
        ("rust-tracing" ,rust-tracing-0.1)
        ("rust-tracing-subscriber" ,rust-tracing-subscriber-0.3)
        ("rust-axum" ,rust-axum-0.7)
        ("rust-blake3" ,rust-blake3-1)
        ("rust-tiny-keccak" ,rust-tiny-keccak-2)
        ("rust-uuid" ,rust-uuid-1)
        ("rust-chrono" ,rust-chrono-0.4))))
    (native-inputs
     (list pkg-config rust rust-cargo))
    (inputs
     (list openssl))
    (propagated-inputs
     (list z3 idris))
    (synopsis "Neurosymbolic theorem proving platform with 30 prover backends")
    (description
     "ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural
Assistance) is a trust-hardened neurosymbolic theorem proving platform supporting
30 prover backends with solver integrity checking and confidence scoring.")
    (home-page "https://github.com/hyperpolymath/echidna")
    (license (license:non-copyleft "https://github.com/hyperpolymath/palimpsest-license"
                                   #:comment "PMPL-1.0-or-later"))))
