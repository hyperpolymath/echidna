<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-02-19 -->

# ECHIDNA — Project Topology

## System Architecture

```
                        ┌─────────────────────────────────────────┐
                        │              USERS / CLIENTS            │
                        │      (GraphQL, gRPC, REST, REPL, UI)    │
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
  ReScript UI (28 components)       ██████████ 100%    Proof exploration stable

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/lint/test
  .machine_readable/                ██████████ 100%    STATE.a2ml tracking
  Test Suite (306+ Passing)         ██████████ 100%    High unit/integration coverage

─────────────────────────────────────────────────────────────────────────────
OVERALL:                            ██████████ 100%    v1.5.0 Trust Hardening Complete
```

## Key Dependencies

```
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
