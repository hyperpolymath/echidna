// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

#![forbid(unsafe_code)]

//! Graph Neural Network integration for proof search guidance
//!
//! This module provides GNN-based proof search guidance by:
//!
//! 1. **Proof Graph Construction**: Converting proof states (goals, hypotheses,
//!    available theorems) into graph representations where nodes are terms and
//!    edges encode structural and semantic relationships.
//!
//! 2. **Term Embeddings**: Computing local feature vectors for terms without
//!    external dependencies, enabling graph construction before neural inference.
//!
//! 3. **GNN Inference Client**: Communicating with the Julia ML server
//!    (EchidnaML) for neural premise selection via Graph Neural Networks
//!    (GCN + GAT layers) and Transformer cross-attention.
//!
//! 4. **Guided Proof Search**: Using GNN-scored premise rankings to guide
//!    tactic selection in the agentic proof search loop.
//!
//! # Architecture
//!
//! ```text
//! ProofState ──> ProofGraph ──> GnnClient ──> Julia ML Server
//!                  │                             │
//!                  │ (local features)             │ (GNN inference)
//!                  v                             v
//!              Embeddings              PremiseRanking
//!                  │                             │
//!                  └─────────> GuidedSearch <────┘
//!                                   │
//!                                   v
//!                            Ranked Tactics
//! ```
//!
//! # Integration Points
//!
//! - **Agent module** (`src/rust/agent/`): Uses `GuidedSearch` for tactic selection
//! - **Dispatch pipeline** (`src/rust/dispatch.rs`): GNN scores feed confidence
//! - **Neural module** (`src/rust/neural.rs`): Complementary — text-based vs graph-based
//! - **Julia ML** (`src/julia/models/neural_solver.jl`): Server-side GNN encoder

pub mod client;
pub mod embeddings;
pub mod fallback_monitor;
pub mod graph;
pub mod guided_search;

pub use client::{GnnClient, GnnConfig, GnnInferenceResult};
pub use embeddings::{TermEmbedding, TermFeatureExtractor};
pub use fallback_monitor::{FallbackMetrics, FallbackMonitor, FallbackSlaConfig};
pub use graph::{EdgeKind, NodeKind, ProofGraph, ProofGraphBuilder};
pub use guided_search::{GnnGuidedSearch, GuidedSearchConfig, ScoredPremise};
