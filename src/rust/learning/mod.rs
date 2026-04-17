// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Continuous self-learning loop for ECHIDNA.
//!
//! The four-piece architecture that turns a trained prover into a
//! self-improving one (AlphaProof / HyperTree / DeepSeek-Prover style):
//!
//! ```text
//!   ┌──────────────┐   generate   ┌──────────────┐
//!   │  Curriculum  │─────────────▶│  Self-Play   │
//!   │  scheduler   │              │  generator   │
//!   └──────────────┘              └──────┬───────┘
//!           ▲                            │ candidate lemma
//!           │                            ▼
//!           │                     ┌──────────────┐
//!           │                     │     MCTS     │   (tactic search
//!           │                     │  tactic      │    under UCB1,
//!           │                     │  search      │    neural priors)
//!           │                     └──────┬───────┘
//!           │                            │ proof attempt
//!           │                            ▼
//!           │                     ┌──────────────┐
//!           │                     │  Verifier    │   (48 prover
//!           │                     │  (prover     │    backends —
//!           │                     │   dispatch)  │    already built)
//!           │                     └──────┬───────┘
//!           │                            │ success/fail
//!           │                            ▼
//!           │                     ┌──────────────┐
//!           └─────────────────────│  VeriSimDB   │   (attempt log =
//!             difficulty signal   │  attempts    │    new training set)
//!                                 └──────┬───────┘
//!                                        │
//!                                        ▼
//!                                 ┌──────────────┐
//!                                 │  Expert      │   (retrain policy
//!                                 │  iteration   │    on solved → repeat)
//!                                 └──────────────┘
//! ```
//!
//! See `docs/LEARNING-ARCHITECTURE.adoc` for the full design rationale.

#![allow(dead_code)]

pub mod curriculum;
pub mod daemon;
pub mod mcts;
pub mod self_play;
