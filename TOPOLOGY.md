<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-03-08 -->

# ECHIDNA — Project Topology

## System Architecture

```
                        ┌─────────────────────────────────────────┐
                        │              USERS / CLIENTS            │
                        │      (GraphQL, gRPC, REST, REPL, UI)    │
                        └───────────────────┬─────────────────────┘
                                            │
                        ┌───────────────────┼─────────────────────┐
                        │    V-LANG REST ADAPTERS (5 adapters)    │
                        │  Core:8100-8102  Overlay:8103           │
                        │  BoJ:7700  TypeLL:7800  Tentacles:8300  │
                        └───────────────────┬─────────────────────┘
                                            │ links .so
                        ┌───────────────────┼─────────────────────┐
                        │    ZIG FFI LAYER (5 shared libraries)   │
                        │  libechidna_ffi  libechidna_overlay     │
                        │  libechidna_boj  libechidna_typell      │
                        │  libechidna_tentacles                   │
                        │  (C-ABI exports, bidirectional callbacks)│
                        └───────────────────┬─────────────────────┘
                                            │
                        ┌───────────────────┼─────────────────────┐
                        │    IDRIS2 ABI LAYER (8 modules)         │
                        │  Types.idr  Layout.idr  Foreign.idr     │
                        │  Overlay.idr  Boj.Foreign  TypeLL.Foreign│
                        │  TentaclesForeign.idr                   │
                        │  (Dependent type proofs, zero believe_me)│
                        └───────────────────┬─────────────────────┘
                                            │
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │           ECHIDNA CORE (RUST)           │
                        │    (Dispatch Pipeline, Actor Agents)    │
                        └──────────┬───────────────────┬──────────┘
                                   │                   │
                                   ▼                   ▼
                        ┌───────────────────────┐  ┌────────────────────────────────┐
                        │ TRUST PIPELINE        │  │ NEURAL LAYER (JULIA)           │
                        │ - Axiom Tracking      │  │ - Premise Selection            │
                        │ - Portfolio Solving   │  │ - Tactic Prediction            │
                        │ - Binary Integrity    │  │ - Anomaly Detection            │
                        └──────────┬────────────┘  └──────────┬─────────────────────┘
                                   │                          │
                                   └────────────┬─────────────┘
                                                ▼
                        ┌─────────────────────────────────────────┐
                        │           PROVER BACKENDS (30)          │
                        │  ┌───────────┐  ┌───────────┐  ┌───────┐│
                        │  │ Tier 1    │  │ Tier 2    │  │ Tier 3││
                        │  │ (Agda/Coq)│  │ (Z3/CVC5) │  │ (Dafny)││
                        │  └───────────┘  └───────────┘  └───────┘│
                        └───────────────────┬─────────────────────┘
                                            │
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │          EXECUTOR (SANDBOXED)           │
                        │      (Podman, Bubblewrap, No Net)       │
                        └─────────────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │    GENERATED C HEADERS (5 headers)      │
                        │  echidna_ffi.h  echidna_overlay.h       │
                        │  echidna_boj.h  echidna_typell.h        │
                        │  echidna_tentacles.h                    │
                        └─────────────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │          REPO INFRASTRUCTURE            │
                        │  Justfile / Cargo   .machine_readable/  │
                        │  Guix Channel       RSR Tier 1          │
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
PROVER BACKENDS
  30/30 Provers Operational         ██████████ 100%    All backends verified
  ProverBackend Trait               ██████████ 100%    Universal interface stable
  File Extension Detection          ██████████ 100%    30+ formats supported

TRUST PIPELINE
  Axiom Usage Tracking              ██████████ 100%    4 danger levels active
  SMT Portfolio Solving             ██████████ 100%    Cross-check logic stable
  Solver Binary Integrity           ██████████ 100%    SHAKE3-512 provenance
  5-Level Trust Hierarchy           ██████████ 100%    Confidence scoring active

LAYERS & INTERFACES
  Neural Layer (Julia)              ██████████ 100%    Logistic regression stable
  3 API Interfaces                  ██████████ 100%    GraphQL, gRPC, REST active
  ReScript UI (33 components)       ██████████ 100%    Proof exploration stable

FFI / ABI LAYER
  Idris2 ABI (8 modules)           ██████████ 100%    Type-checked, zero believe_me
  Zig FFI (5 shared libs)          ██████████ 100%    Core, overlay, boj, typell, tentacles
  Generated C Headers (5)          ██████████ 100%    echidna_ffi/overlay/boj/typell/tentacles.h
  Bidirectional Callbacks           ██████████ 100%    Init/prover/error/verify events
  Native Zig Tests                  ██████████ 100%    30+ tests, core + overlay
  V-lang REST Adapters (5)         ████████░░  80%    Polling works; SSE/WS pending
  Memory Layout Proofs              ██████████ 100%    DivisibleBy, VerifiedLayout

TENTACLES FFI/ABI
  TentaclesForeign.idr              ██████████ 100%    7-Tentacles agent ABI definitions
  tentacles.zig                     ██████████ 100%    Agent mgmt, OODA loop, events FFI
  echidna_tentacles.h               ██████████ 100%    Generated C header for tentacles
  tentacles.v                       ██████████ 100%    V-lang REST adapter (port 8300)
  libechidna_tentacles.so           ██████████ 100%    Shared library for tentacles FFI

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/lint/test
  .machine_readable/                ██████████ 100%    STATE.a2ml tracking
  Test Suite (306+ Passing)         ██████████ 100%    High unit/integration coverage

─────────────────────────────────────────────────────────────────────────────
OVERALL:                            █████████░  95%    v1.6 FFI/ABI ~95% (SSE/WS pending)
```

## Key Dependencies

```
Idris2 ABI ──► C Headers ──► Zig FFI (.so) ──► V-lang Adapters (REST)
     │              │              │                    │
     ▼              ▼              ▼                    ▼
Type Proofs    echidna_*.h    Callbacks ◄──►    SSE/WebSocket (planned)

Julia Neural ───► Rust Dispatch ───► Trust Filter ───► Podman Sandbox
     │                 │                 │                  │
     ▼                 ▼                 ▼                  ▼
Premise Selection ──► Prover ───────► Proof Cert ─────► Confidence 5
```

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
