;; SPDX-License-Identifier: PMPL-1.0-or-later
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
;; Policy (per project CLAUDE.md):
;;   Guix is the PRIMARY package-management path.
;;   flake.nix mirrors this set as a fallback for contributors without Guix.
;;
;; Availability note:
;;   Guix package availability drifts. The comment beside each line records the
;;   Guix module the package lives in at audit time. Anything marked NIX_ONLY or
;;   CONTAINER_ONLY is *not* in Guix upstream and must be provisioned via the
;;   flake.nix fallback path or a Containerfile in Wave-3.

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
   ;; Lean 4 — NIX_ONLY: not in Guix; install via flake.nix or upstream installer.
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
