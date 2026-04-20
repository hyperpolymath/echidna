// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

#![forbid(unsafe_code)]

//! Term feature extraction and local embedding computation
//!
//! Computes feature vectors for proof graph nodes *without* calling the
//! Julia ML server. These local features serve as initial node embeddings
//! for the GNN — the GNN then refines them through message passing.
//!
//! Features encode structural and syntactic properties of terms:
//! - Term kind (one-hot encoding of Term variant)
//! - Depth in the proof graph
//! - Arity (number of arguments for App, branches for Match)
//! - Symbol frequency (how often the same constant appears)
//! - Structural complexity (total subterm count)
//! - Node kind (one-hot encoding of graph role)
//!
//! The feature dimension is fixed at [`FEATURE_DIM`] to match the Julia
//! GNN encoder's expected input dimension.

use std::collections::HashMap;

use crate::core::Term;
use crate::gnn::graph::{NodeKind, ProofGraph};

/// Fixed feature dimension for term embeddings.
///
/// Must match `feature_dim` in the Julia GNN encoder config
/// (see `src/julia/EchidnaML.jl` `EchidnaConfig.embedding_dim`).
pub const FEATURE_DIM: usize = 32;

/// Number of distinct Term variants for one-hot encoding.
const NUM_TERM_KINDS: usize = 14;

/// Number of distinct NodeKind variants for one-hot encoding.
const NUM_NODE_KINDS: usize = 7;

/// Extracts local feature vectors for proof graph nodes.
///
/// Operates on a completed [`ProofGraph`] by parsing node labels
/// and computing structural features. After extraction, each node's
/// `features` field is populated with a vector of length [`FEATURE_DIM`].
pub struct TermFeatureExtractor {
    /// Global symbol frequency counts (populated from all nodes)
    symbol_frequencies: HashMap<String, usize>,
    /// Maximum symbol frequency (for normalisation)
    max_frequency: usize,
}

impl TermFeatureExtractor {
    /// Create a new feature extractor.
    pub fn new() -> Self {
        Self {
            symbol_frequencies: HashMap::new(),
            max_frequency: 1,
        }
    }

    /// Extract features for all nodes in the proof graph.
    ///
    /// This is a two-pass process:
    /// 1. First pass: count symbol frequencies across all node labels
    /// 2. Second pass: compute per-node feature vectors
    pub fn extract_features(&mut self, graph: &mut ProofGraph) {
        // Pass 1: symbol frequency counting
        self.symbol_frequencies.clear();
        for node in &graph.nodes {
            let symbols = extract_symbols(&node.label);
            for sym in symbols {
                *self.symbol_frequencies.entry(sym).or_insert(0) += 1;
            }
        }
        self.max_frequency = self.symbol_frequencies.values().copied().max().unwrap_or(1);

        // Pass 2: compute feature vectors
        let num_nodes = graph.nodes.len();
        let num_edges = graph.edges.len();

        for node in &mut graph.nodes {
            let features = self.compute_node_features(node, num_nodes, num_edges);
            node.features = features;
        }
    }

    /// Compute the feature vector for a single node.
    fn compute_node_features(
        &self,
        node: &crate::gnn::graph::GraphNode,
        num_nodes: usize,
        num_edges: usize,
    ) -> Vec<f32> {
        let mut features = vec![0.0_f32; FEATURE_DIM];
        let mut offset = 0;

        // Features [0..7]: Node kind one-hot (7 dimensions)
        let node_kind_idx = node_kind_index(node.kind);
        if offset + node_kind_idx < FEATURE_DIM {
            features[offset + node_kind_idx] = 1.0;
        }
        offset += NUM_NODE_KINDS;

        // Features [7..21]: Term kind one-hot (14 dimensions)
        // Inferred from the node label prefix
        let term_kind_idx = infer_term_kind_from_label(&node.label);
        if offset + term_kind_idx < FEATURE_DIM {
            features[offset + term_kind_idx] = 1.0;
        }
        offset += NUM_TERM_KINDS;

        // Feature [21]: Normalised depth
        if offset < FEATURE_DIM {
            features[offset] = (node.term_depth as f32) / 10.0;
        }
        offset += 1;

        // Feature [22]: Symbol frequency (normalised)
        if offset < FEATURE_DIM {
            let symbols = extract_symbols(&node.label);
            let avg_freq = if symbols.is_empty() {
                0.0
            } else {
                let total: usize = symbols
                    .iter()
                    .map(|s| self.symbol_frequencies.get(s).copied().unwrap_or(0))
                    .sum();
                (total as f32) / (symbols.len() as f32 * self.max_frequency as f32)
            };
            features[offset] = avg_freq;
        }
        offset += 1;

        // Feature [23]: Label length (proxy for complexity, normalised)
        if offset < FEATURE_DIM {
            features[offset] = (node.label.len() as f32).min(200.0) / 200.0;
        }
        offset += 1;

        // Feature [24]: Number of symbols in label (arity proxy)
        if offset < FEATURE_DIM {
            let sym_count = extract_symbols(&node.label).len();
            features[offset] = (sym_count as f32).min(20.0) / 20.0;
        }
        offset += 1;

        // Feature [25]: Is a binder (lambda, pi, let, fix)?
        if offset < FEATURE_DIM {
            features[offset] = if node.kind == NodeKind::Binder {
                1.0
            } else {
                0.0
            };
        }
        offset += 1;

        // Feature [26]: Is a top-level node (goal or premise)?
        if offset < FEATURE_DIM {
            features[offset] = if node.kind == NodeKind::Goal || node.kind == NodeKind::Premise {
                1.0
            } else {
                0.0
            };
        }
        offset += 1;

        // Feature [27]: Graph density (global feature, same for all nodes)
        if offset < FEATURE_DIM {
            let max_edges = num_nodes.saturating_mul(num_nodes.saturating_sub(1));
            features[offset] = if max_edges > 0 {
                (num_edges as f32) / (max_edges as f32)
            } else {
                0.0
            };
        }
        offset += 1;

        // Feature [28]: Has type annotation (presence of ":" in label)
        if offset < FEATURE_DIM {
            features[offset] = if node.label.contains(':') { 1.0 } else { 0.0 };
        }
        offset += 1;

        // Feature [29]: Contains quantifier (forall, exists, pi)
        if offset < FEATURE_DIM {
            features[offset] = if node.label.contains("pi_")
                || node.label.contains("forall")
                || node.label.contains("exists")
                || node.label.contains("Pi")
            {
                1.0
            } else {
                0.0
            };
        }
        offset += 1;

        // Features [30..32]: Reserved for future use (zero-padded)
        let _ = offset; // suppress unused warning

        features
    }
}

impl Default for TermFeatureExtractor {
    fn default() -> Self {
        Self::new()
    }
}

/// Embedding result for a single term (independent of graph context).
///
/// Used when embedding a standalone term (e.g., for similarity search)
/// without building a full proof graph first.
#[derive(Debug, Clone)]
pub struct TermEmbedding {
    /// The feature vector
    pub features: Vec<f32>,
    /// The term that was embedded
    pub term_label: String,
}

impl TermEmbedding {
    /// Compute an embedding for a standalone term.
    pub fn from_term(term: &Term) -> Self {
        let label = format!("{}", term);
        let mut features = vec![0.0_f32; FEATURE_DIM];

        // Encode term kind
        let kind_idx = term_kind_index(term);
        if kind_idx < FEATURE_DIM {
            features[kind_idx] = 1.0;
        }

        // Encode structural depth
        let depth = term_depth(term);
        if NUM_TERM_KINDS < FEATURE_DIM {
            features[NUM_TERM_KINDS] = (depth as f32) / 10.0;
        }

        // Encode arity
        let arity = term_arity(term);
        if NUM_TERM_KINDS + 1 < FEATURE_DIM {
            features[NUM_TERM_KINDS + 1] = (arity as f32).min(10.0) / 10.0;
        }

        Self {
            features,
            term_label: label,
        }
    }

    /// Cosine similarity between two term embeddings.
    pub fn cosine_similarity(&self, other: &TermEmbedding) -> f32 {
        let dot: f32 = self
            .features
            .iter()
            .zip(other.features.iter())
            .map(|(a, b)| a * b)
            .sum();
        let norm_a: f32 = self.features.iter().map(|x| x * x).sum::<f32>().sqrt();
        let norm_b: f32 = other.features.iter().map(|x| x * x).sum::<f32>().sqrt();
        let denom = norm_a * norm_b;
        if denom < 1e-10 {
            0.0
        } else {
            dot / denom
        }
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Extract alphanumeric symbols from a label string.
fn extract_symbols(label: &str) -> Vec<String> {
    label
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .filter(|s| !s.is_empty() && s.len() > 1)
        .map(|s| s.to_string())
        .collect()
}

/// Map NodeKind to one-hot index.
fn node_kind_index(kind: NodeKind) -> usize {
    match kind {
        NodeKind::Goal => 0,
        NodeKind::Hypothesis => 1,
        NodeKind::Premise => 2,
        NodeKind::Subterm => 3,
        NodeKind::TypeExpr => 4,
        NodeKind::Binder => 5,
        NodeKind::Constant => 6,
    }
}

/// Infer the Term variant from a graph node label.
///
/// This is a heuristic based on label prefixes and patterns.
/// Returns an index into the one-hot encoding.
fn infer_term_kind_from_label(label: &str) -> usize {
    if label.starts_with("lambda_") {
        3 // Lambda
    } else if label.starts_with("pi_") {
        4 // Pi
    } else if label.starts_with("let_") {
        7 // Let
    } else if label.starts_with("fix_") {
        9 // Fix
    } else if label.starts_with("app@") {
        2 // App
    } else if label.starts_with("match@") {
        8 // Match
    } else if label.starts_with("?meta_") {
        11 // Meta
    } else if label.starts_with('?') {
        10 // Hole
    } else if label.starts_with("Type") || label.starts_with("Sort") {
        5 // Type/Sort/Universe
    } else if label.starts_with("goal_") {
        0 // Var-like (goal label)
    } else if label.contains(':') {
        1 // Const-like (named with type)
    } else {
        0 // Default to Var
    }
}

/// Map a Term to its kind index for one-hot encoding.
fn term_kind_index(term: &Term) -> usize {
    match term {
        Term::Var(_) => 0,
        Term::Const(_) => 1,
        Term::App { .. } => 2,
        Term::Lambda { .. } => 3,
        Term::Pi { .. } => 4,
        Term::Type(_) => 5,
        Term::Sort(_) => 6,
        Term::Universe(_) => 5, // Same slot as Type
        Term::Let { .. } => 7,
        Term::Match { .. } => 8,
        Term::Fix { .. } => 9,
        Term::Hole(_) => 10,
        Term::Meta(_) => 11,
        Term::ProverSpecific { .. } => 12,
    }
}

/// Compute the maximum depth of a term tree.
fn term_depth(term: &Term) -> usize {
    match term {
        Term::Var(_)
        | Term::Const(_)
        | Term::Type(_)
        | Term::Sort(_)
        | Term::Universe(_)
        | Term::Hole(_)
        | Term::Meta(_) => 0,
        Term::App { func, args } => {
            let func_depth = term_depth(func);
            let max_arg = args.iter().map(term_depth).max().unwrap_or(0);
            1 + func_depth.max(max_arg)
        },
        Term::Lambda {
            param_type, body, ..
        } => {
            let pt = param_type.as_ref().map(|t| term_depth(t)).unwrap_or(0);
            1 + pt.max(term_depth(body))
        },
        Term::Pi {
            param_type, body, ..
        } => 1 + term_depth(param_type).max(term_depth(body)),
        Term::Let {
            ty, value, body, ..
        } => {
            let t = ty.as_ref().map(|t| term_depth(t)).unwrap_or(0);
            1 + t.max(term_depth(value)).max(term_depth(body))
        },
        Term::Match {
            scrutinee,
            branches,
            ..
        } => {
            let s = term_depth(scrutinee);
            let b = branches
                .iter()
                .map(|(_, t)| term_depth(t))
                .max()
                .unwrap_or(0);
            1 + s.max(b)
        },
        Term::Fix { ty, body, .. } => {
            let t = ty.as_ref().map(|t| term_depth(t)).unwrap_or(0);
            1 + t.max(term_depth(body))
        },
        Term::ProverSpecific { .. } => 0,
    }
}

/// Compute the arity of a term (number of direct subterms).
fn term_arity(term: &Term) -> usize {
    match term {
        Term::Var(_)
        | Term::Const(_)
        | Term::Type(_)
        | Term::Sort(_)
        | Term::Universe(_)
        | Term::Hole(_)
        | Term::Meta(_)
        | Term::ProverSpecific { .. } => 0,
        Term::App { args, .. } => 1 + args.len(), // func + args
        Term::Lambda { param_type, .. } => {
            if param_type.is_some() {
                2
            } else {
                1
            }
        },
        Term::Pi { .. } => 2, // param_type + body
        Term::Let { ty, .. } => {
            if ty.is_some() {
                3
            } else {
                2
            }
        },
        Term::Match { branches, .. } => 1 + branches.len(),
        Term::Fix { ty, .. } => {
            if ty.is_some() {
                2
            } else {
                1
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gnn::graph::ProofGraphBuilder;

    #[test]
    fn test_feature_dim_is_32() {
        assert_eq!(FEATURE_DIM, 32);
    }

    #[test]
    fn test_term_embedding_from_var() {
        let term = Term::Var("x".to_string());
        let emb = TermEmbedding::from_term(&term);
        assert_eq!(emb.features.len(), FEATURE_DIM);
        assert_eq!(emb.features[0], 1.0); // Var is kind 0
    }

    #[test]
    fn test_term_embedding_from_pi() {
        let term = Term::Pi {
            param: "n".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::Var("n".to_string())),
        };
        let emb = TermEmbedding::from_term(&term);
        assert_eq!(emb.features.len(), FEATURE_DIM);
        assert_eq!(emb.features[4], 1.0); // Pi is kind 4
    }

    #[test]
    fn test_cosine_similarity_identical() {
        let term = Term::Const("Nat".to_string());
        let emb = TermEmbedding::from_term(&term);
        let sim = emb.cosine_similarity(&emb);
        assert!(
            (sim - 1.0).abs() < 1e-6,
            "Identical embeddings should have similarity 1.0, got {}",
            sim
        );
    }

    #[test]
    fn test_cosine_similarity_different() {
        let emb1 = TermEmbedding::from_term(&Term::Var("x".to_string()));
        let emb2 = TermEmbedding::from_term(&Term::Pi {
            param: "n".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::Var("n".to_string())),
        });
        let sim = emb1.cosine_similarity(&emb2);
        assert!(
            sim < 1.0,
            "Different terms should have similarity < 1.0, got {}",
            sim
        );
    }

    #[test]
    fn test_feature_extraction_populates_all_nodes() {
        let state = crate::core::ProofState::new(Term::App {
            func: Box::new(Term::Const("f".to_string())),
            args: vec![Term::Var("x".to_string()), Term::Var("y".to_string())],
        });

        let mut builder = ProofGraphBuilder::new(3);
        let mut graph = builder.build_from_proof_state(&state);

        let mut extractor = TermFeatureExtractor::new();
        extractor.extract_features(&mut graph);

        for node in &graph.nodes {
            assert_eq!(
                node.features.len(),
                FEATURE_DIM,
                "Node '{}' has wrong feature dim: {} (expected {})",
                node.label,
                node.features.len(),
                FEATURE_DIM
            );
        }
    }

    #[test]
    fn test_term_depth_computation() {
        assert_eq!(term_depth(&Term::Var("x".to_string())), 0);
        assert_eq!(
            term_depth(&Term::App {
                func: Box::new(Term::Const("f".to_string())),
                args: vec![Term::Var("x".to_string())],
            }),
            1
        );
        assert_eq!(
            term_depth(&Term::Lambda {
                param: "x".to_string(),
                param_type: None,
                body: Box::new(Term::App {
                    func: Box::new(Term::Const("f".to_string())),
                    args: vec![Term::Var("x".to_string())],
                }),
            }),
            2
        );
    }

    #[test]
    fn test_term_arity_computation() {
        assert_eq!(term_arity(&Term::Var("x".to_string())), 0);
        assert_eq!(
            term_arity(&Term::App {
                func: Box::new(Term::Const("f".to_string())),
                args: vec![Term::Var("x".to_string()), Term::Var("y".to_string())],
            }),
            3 // func + 2 args
        );
    }

    #[test]
    fn test_extract_symbols() {
        let symbols = extract_symbols("even_add_self: (Pi n: Nat. is_even (add n n))");
        assert!(symbols.contains(&"even_add_self".to_string()));
        assert!(symbols.contains(&"Nat".to_string()));
        assert!(symbols.contains(&"is_even".to_string()));
    }
}
