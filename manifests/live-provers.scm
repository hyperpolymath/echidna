;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
;;
;; ECHIDNA — Live-Prover CI Manifest (Guix, PRIMARY)
;;
;; Purpose: resolve the subset packaged by GNU Guix 1.4.0 (the CI baseline).
;; This manifest is NOT a declaration that every live prover is packaged or
;; tested. Resolution does not prove that a prover ran or that a proof passed.
;; It has no CI consumer: the T1 Guix manifest check in live-provers.yml was
;; retired 2026-11-09 under the CI-4 ruling (#416), and the Containerfile is
;; the reproducibility path (container-ci.yml rebuilds the image on an
;; independent runner and requires the same image ID). Local developers can
;; still resolve it via:
;;
;;     guix package -m manifests/live-provers.scm --dry-run --no-substitutes
;;
;; The release's Rust package is not the repository's pinned Rust toolchain.
;; Building the live test harness also requires rust-toolchain.toml and its
;; native dependencies; manifest resolution alone does not establish that.
;;
;; Tiering (matches ~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md):
;;   T1 — trivial (apt/Guix single-package)       — run on every PR
;;   T2 — build-from-source                       — run nightly
;;   T3 — container / special env                 — run weekly
;;   T4 — niche / best-effort                     — no CI job (quarterly
;;        allow-fail jobs retired 2026-11-09, CI-4 #416; mock-only)
;;
;; Policy (estate ruling 2026-05-18 + estate-wide nix-deprecation 2026-06-01):
;;   Guix is the PRIMARY (and only) package-management path declared here.
;;   There is NO Nix mirror anywhere — flake.nix was DEPRECATED on 2026-05-18,
;;   removed from this repo, and on 2026-06-01 nix was deprecated estate-wide.
;;   The single universal escape hatch for the not-in-Guix / non-free tail is a
;;   SEALED CONTAINER (.containerization/Containerfile.wave3), not a Nix twin.
;;
;; Availability note:
;;   Package names below were checked against the GNU Guix 1.4.0 release.
;;   The comment beside each line records its upstream module. Anything marked
;;   NIX_ONLY or CONTAINER_ONLY is *not* in Guix upstream and is provisioned via
;;   the Wave-3 sealed container (Containerfile.wave3 --target <prover>). The
;;   "NIX_ONLY" label is retained below only as a historical availability fact
;;   (the package is absent from Guix) — it does NOT imply a Nix provisioning
;;   path is permitted; the intended provisioning path is the container.
;;
;; Explicit boundary (Guix coverage UNKNOWN, not passed by this manifest):
;;   T1 cvc5, alt-ergo, vampire, eprover, spass and chuffed are provisioned by
;;   the separate live-prover matrix. cvc4 is not an equivalent cvc5 check.
;;   T2 Idris2 and Isabelle are also absent from this baseline. Their separate
;;   jobs must provide execution evidence; this resolution job cannot.
;;   Chuffed appears in Guix 1.5.0; the other names remain absent from that
;;   release inventory. CI currently checks the explicit 1.4.0 baseline.

(specifications->manifest
 '(;; ----------------------------------------------------------------------
   ;; Tier 1 — packaged subset; live execution is checked by separate jobs
   ;; ----------------------------------------------------------------------
   "z3"              ; (gnu packages maths) — SMT, deep wiring
   "glpk"            ; (gnu packages maths) — LP/MIP constraint solver (glpsol)
   "minizinc"        ; (gnu packages maths) — constraint modelling
   ;; --- Harness prerequisites
   "coreutils"       ; timeout(1) and other GNU core utilities
   "util-linux"      ; Linux system utilities used by the harness
   "gcc-toolchain"   ; linker for compiled provers that invoke backends

   ;; ----------------------------------------------------------------------
   ;; Tier 2 — build-from-source: Guix packages exist; nightly cadence
   ;; ----------------------------------------------------------------------
   "coq"             ; (gnu packages coq) — Coq/Rocq
   "agda"            ; (gnu packages agda) — dependent-type proof assistant
   "why3"            ; (gnu packages maths) — auto-active verifier
   ;; Lean 4 — NIX_ONLY: not in Guix; install via the Wave-3 sealed container
   ;; (the upstream installer ships pre-built binaries; the historical "flake.nix"
   ;; path was closed 2026-06-01 per estate-wide nix-deprecation).
   ;; Dafny — NIX_ONLY: dotnet toolchain dependency makes Guix packaging tricky.
   ;; F* — BUILD_FROM_SOURCE (no Guix package): manual Wave-2 Containerfile path.
   ;; HOL Light — CONTAINER_ONLY: obscure build requirements.
   ;; TLAPS — CONTAINER_ONLY: TLA+ toolkit distribution model.

   ;; ----------------------------------------------------------------------
   ;; Tier 3 — container / special env (declared here for visibility;
   ;; provisioned via Containerfile in Wave-3, not Guix)
   ;; ----------------------------------------------------------------------
   ;; Tamarin      — CONTAINER_ONLY (Haskell Stack build)
   ;; ProVerif     — CONTAINER_ONLY (OCaml build)
   ;; Imandra      — CONTAINER_ONLY (proprietary binary)
   ;; SCIP         — CONTAINER_ONLY (license-restricted until recently)
   ;; OR-Tools     — CONTAINER_ONLY (large C++ build)
   ;; HOL4         — CONTAINER_ONLY
   ;; ACL2         — CONTAINER_ONLY (Lisp)
   ;; Twelf        — CONTAINER_ONLY
   ;; Metamath     — NIX_ONLY (pure-Rust verifier in Echidna; external metamath binary optional)

   ;; ----------------------------------------------------------------------
   ;; Tier 4 — niche / best-effort (NOT managed by Guix; retained as mocks
   ;; unless a maintainer volunteers a per-backend Containerfile)
   ;; ----------------------------------------------------------------------
   ;; Mizar, Nuprl, PVS, Minlog, Dedukti, Arend, KeY, Prism, UPPAAL, ViPER,
   ;; NuSMV, Spin, TLC, CBMC, Seahorn, dReal, Boogie, Kissat, Alloy

   ;; ----------------------------------------------------------------------
   ;; Packaged build tools (not the repository's pinned Rust toolchain)
   ;; ----------------------------------------------------------------------
   "rust"
   "rust:cargo"      ; cargo output of rust, not the rust-cargo library crate
   "pkg-config"
   "openssl"))
