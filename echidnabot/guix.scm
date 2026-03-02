;; echidnabot - Guix Package Definition
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
             (gnu packages sqlite)
             (gnu packages tls)
             (gnu packages pkg-config))

(define-public echidnabot
  (package
    (name "echidnabot")
    (version "0.1.0")
    (source (local-file "." "echidnabot-checkout"
                        #:recursive? #t
                        #:select? (git-predicate ".")))
    (build-system cargo-build-system)
    (arguments
     `(#:cargo-inputs
       (;; Core async runtime
        ("rust-tokio" ,rust-tokio-1)
        ;; HTTP framework
        ("rust-axum" ,rust-axum-0.7)
        ("rust-tower" ,rust-tower-0.4)
        ("rust-tower-http" ,rust-tower-http-0.5)
        ;; Serialization
        ("rust-serde" ,rust-serde-1)
        ("rust-serde-json" ,rust-serde-json-1)
        ("rust-toml" ,rust-toml-0.8)
        ;; Database
        ("rust-sqlx" ,rust-sqlx-0.8)
        ;; HTTP client
        ("rust-reqwest" ,rust-reqwest-0.11)
        ;; Utilities
        ("rust-uuid" ,rust-uuid-1)
        ("rust-chrono" ,rust-chrono-0.4)
        ("rust-thiserror" ,rust-thiserror-1)
        ("rust-anyhow" ,rust-anyhow-1)
        ("rust-tracing" ,rust-tracing-0.1)
        ("rust-tracing-subscriber" ,rust-tracing-subscriber-0.3)
        ;; Crypto
        ("rust-hmac" ,rust-hmac-0.12)
        ("rust-sha2" ,rust-sha2-0.10)
        ("rust-hex" ,rust-hex-0.4)
        ;; CLI
        ("rust-clap" ,rust-clap-4)
        ("rust-config" ,rust-config-0.14))
       #:cargo-development-inputs
       (("rust-tokio-test" ,rust-tokio-test-0.4)
        ("rust-tempfile" ,rust-tempfile-3))))
    (native-inputs
     (list pkg-config
           rust
           rust-cargo))
    (inputs
     (list sqlite
           openssl))
    (synopsis "Proof-aware CI bot for theorem prover repositories")
    (description
     "echidnabot monitors code repositories containing formal proofs and
delegates verification to ECHIDNA Core.  It integrates with GitHub, GitLab,
and Bitbucket to provide automated proof checking via webhooks.")
    (home-page "https://github.com/hyperpolymath/echidnabot")
    (license (license:non-copyleft "https://github.com/hyperpolymath/palimpsest-license"
                                   #:comment "PMPL-1.0-or-later"))))

;; For development shell
echidnabot
