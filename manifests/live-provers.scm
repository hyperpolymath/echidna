;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
;;
;; ECHIDNA — Live-Prover CI Manifest (Guix, PRIMARY)
;;
;; Purpose: declare every prover binary that live-prover CI exercises.
;; Used by `.github/workflows/live-provers.yml` and local developers via:
;;
;;     guix shell -m manifests/live-provers.scm -- cargo test --test live_prover_suite --features live-provers
;;
;; Tiering (matches ~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md):
;;   T1 — trivial (apt/Guix single-package)       — run on every PR
;;   T2 — build-from-source                       — run nightly
;;   T3 — container / special env                 — run weekly
;;   T4 — niche / best-effort                     — run quarterly, allow-fail
;;
;; Policy (estate ruling 2026-05-18 + estate-wide nix-deprecation 2026-06-01):
;;   Guix is the PRIMARY (and only) package-management path declared here.
;;   There is NO Nix mirror anywhere — flake.nix was DEPRECATED on 2026-05-18,
;;   removed from this repo, and on 2026-06-01 nix was deprecated estate-wide.
;;   The single universal escape hatch for the not-in-Guix / non-free tail is a
;;   SEALED CONTAINER (.containerization/Containerfile.wave3), not a Nix twin.
;;
;; Availability note:
;;   Guix package availability drifts. The comment beside each line records the
;;   Guix module the package lives in at audit time. Anything previously marked
;;   NIX_ONLY or CONTAINER_ONLY is *not* in Guix upstream and is provisioned via
;;   the Wave-3 sealed container (Containerfile.wave3 --target <prover>). The
;;   "NIX_ONLY" label is retained below only as a historical availability fact
;;   (the package is absent from Guix) — it does NOT imply a Nix provisioning
;;   path is permitted; the provisioning path is the container.

(specifications->manifest
 '(;; ----------------------------------------------------------------------
   ;; Tier 1 — trivial: ships directly in Guix, every PR runs these live
   ;; ----------------------------------------------------------------------
   "z3"              ; (gnu packages maths) — SMT, deep wiring
   "cvc4"            ; (gnu packages maths) — SMT, cvc5 not yet upstream; cvc4 is a usable stand-in
   "alt-ergo"        ; (gnu packages ocaml) — SMT
   "vampire"         ; (gnu packages maths) — first-order ATP
   "eprover"         ; (gnu packages maths) — first-order ATP
   "spass"           ; (gnu packages maths) — first-order ATP
   "glpk"            ; (gnu packages maths) — LP/MIP constraint solver (glpsol)
   "minizinc"        ; (gnu packages maths) — constraint modelling
   ;; --- Harness prerequisites
   "coreutils"       ; which/timeout/etc. used by the harness
   "util-linux"      ; timeout(1) on GNU systems
   "gcc-toolchain"   ; linker for compiled provers that invoke backends

   ;; ----------------------------------------------------------------------
   ;; Tier 2 — build-from-source: Guix packages exist; nightly cadence
   ;; ----------------------------------------------------------------------
   "coq"             ; (gnu packages coq) — Coq/Rocq
   "agda"            ; (gnu packages agda) — dependent-type proof assistant
   "idris2"          ; (gnu packages idris) — dependent-type proof assistant
   "isabelle"        ; (gnu packages isabelle) — HOL proof assistant
   "why3"            ; (gnu packages ocaml) — auto-active verifier
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
   ;; Build toolchain (so Rust test harness compiles inside `guix shell`)
   ;; ----------------------------------------------------------------------
   "rust"
   "rust-cargo"
   "pkg-config"
   "openssl"))
