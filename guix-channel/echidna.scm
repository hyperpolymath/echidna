;;; SPDX-License-Identifier: PMPL-1.0-or-later
;;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;;
;;; GNU Guix channel for ECHIDNA packages.
;;;
;;; Add to your channels.scm:
;;;   (channel
;;;     (name 'echidna)
;;;     (url "https://github.com/hyperpolymath/echidna")
;;;     (branch "main")
;;;     (introduction
;;;       (make-channel-introduction
;;;         (version "0")
;;;         (commit "<initial-commit-hash>"))))

(define-module (echidna)
  #:use-module (guix packages)
  #:use-module (guix build-system cargo)
  #:use-module (guix download)
  #:use-module (guix git-download)
  #:use-module (guix utils)
  #:use-module ((guix licenses) #:prefix license:))

;;; --- echidna: Core CLI and library ---

(define-public echidna
  (package
    (name "echidna")
    (version "1.5.0")
    (source
      (origin
        (method git-fetch)
        (uri (git-reference
               (url "https://github.com/hyperpolymath/echidna")
               (commit (string-append "v" version))))
        (file-name (git-file-name name version))
        (sha256
          (base32 "0000000000000000000000000000000000000000000000000000"))))
    (build-system cargo-build-system)
    (arguments
      `(#:cargo-inputs
        (("rust-axum" ,rust-axum-0.7)
         ("rust-tokio" ,rust-tokio-1)
         ("rust-serde" ,rust-serde-1)
         ("rust-serde-json" ,rust-serde-json-1)
         ("rust-clap" ,rust-clap-4))
        #:phases
        (modify-phases %standard-phases
          (add-after 'install 'install-bin
            (lambda* (#:key outputs #:allow-other-keys)
              (let ((bin (string-append (assoc-ref outputs "out") "/bin")))
                (install-file "target/release/echidna" bin)))))))
    (synopsis "Neurosymbolic theorem proving platform")
    (description
      "ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural
Assistance) is a trust-hardened neurosymbolic theorem proving platform supporting
30 prover backends with a comprehensive verification pipeline.")
    (home-page "https://github.com/hyperpolymath/echidna")
    (license (list license:pmpl1.0+))))

;;; --- echidna-rest: REST API interface ---

(define-public echidna-rest
  (package
    (inherit echidna)
    (name "echidna-rest")
    (arguments
      `(#:cargo-inputs
        (("rust-axum" ,rust-axum-0.7)
         ("rust-tokio" ,rust-tokio-1)
         ("rust-utoipa" ,rust-utoipa-5))
        #:phases
        (modify-phases %standard-phases
          (replace 'build
            (lambda _
              (invoke "cargo" "build" "--release" "-p" "echidna-rest"))))))
    (synopsis "ECHIDNA REST API interface (OpenAPI)")
    (description "REST API server for ECHIDNA with OpenAPI documentation.")))

;;; --- echidna-graphql: GraphQL API interface ---

(define-public echidna-graphql
  (package
    (inherit echidna)
    (name "echidna-graphql")
    (arguments
      `(#:cargo-inputs
        (("rust-async-graphql" ,rust-async-graphql-7)
         ("rust-tokio" ,rust-tokio-1))
        #:phases
        (modify-phases %standard-phases
          (replace 'build
            (lambda _
              (invoke "cargo" "build" "--release" "-p" "echidna-graphql"))))))
    (synopsis "ECHIDNA GraphQL API interface")
    (description "GraphQL server for ECHIDNA with playground support.")))

;;; --- echidna-grpc: gRPC API interface ---

(define-public echidna-grpc
  (package
    (inherit echidna)
    (name "echidna-grpc")
    (arguments
      `(#:cargo-inputs
        (("rust-tonic" ,rust-tonic-0.12)
         ("rust-prost" ,rust-prost-0.13)
         ("rust-tokio" ,rust-tokio-1))
        #:phases
        (modify-phases %standard-phases
          (replace 'build
            (lambda _
              (invoke "cargo" "build" "--release" "-p" "echidna-grpc"))))))
    (synopsis "ECHIDNA gRPC API interface")
    (description "gRPC server for ECHIDNA with streaming proof updates.")))
