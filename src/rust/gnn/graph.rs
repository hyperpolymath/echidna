// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

#![forbid(unsafe_code)]

//! Proof graph construction from ECHIDNA proof states
//!
//! Converts proof states (goals, hypotheses, available theorems, context)
//! into directed graph representations suitable for GNN processing.
//! Nodes represent terms (goals, hypotheses, premises, subterms) and
//! edges encode structural relationships (contains, references, implies,
//! type-of, etc.).
//!
//! The graph structure mirrors what the Julia GNN encoder expects
//! (see `src/julia/models/neural_solver.jl` `TheoremGraph`).

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::core::{Context, Definition, Goal, Hypothesis, ProofState, Term, Theorem};

/// Kind of node in the proof graph.
///
/// Each node represents a distinct semantic role. The GNN encoder uses
/// node kinds to apply type-specific message passing and aggregation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NodeKind {
    /// Top-level proof goal to be proved
    Goal,
    /// A hypothesis available in the current context
    Hypothesis,
    /// A named theorem/lemma available as a premise
    Premise,
    /// A subterm extracted from a goal, hypothesis, or premise
    Subterm,
    /// A type expression (parameter type, return type, etc.)
    TypeExpr,
    /// A variable binding site (lambda, pi, let)
    Binder,
    /// A constant or axiom reference
    Constant,
}

/// Kind of edge in the proof graph.
///
/// Edges are directed. The GNN encoder uses edge kinds for
/// relation-aware message passing (different weight matrices per edge type).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EdgeKind {
    /// Parent term contains child as subterm (structural)
    Contains,
    /// Source references target by name (e.g., Apply references a theorem)
    References,
    /// Source implies target (logical implication in the proof context)
    Implies,
    /// Source has the target as its type (typing relation)
    HasType,
    /// Source is the body of a binder whose parameter is target
    BindsOver,
    /// Source and target share common subterms (computed similarity)
    SharedStructure,
    /// Goal depends on this hypothesis/premise (dependency)
    DependsOn,
    /// Reverse of DependsOn (premise is useful for goal)
    UsefulFor,
    /// Source has the target as its QTT multiplicity annotation
    HasMultiplicity,
    /// Source has the target as its algebraic effect annotation
    HasEffect,
    /// Source has the target as its modal decoration
    HasModality,
}

/// A single node in the proof graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraphNode {
    /// Unique node identifier within the graph
    pub id: usize,
    /// Semantic role of this node
    pub kind: NodeKind,
    /// Human-readable label (term pretty-print or name)
    pub label: String,
    /// Original term (if this node was derived from a Term)
    pub term_depth: u32,
    /// Feature vector computed locally (before GNN inference)
    pub features: Vec<f32>,
}

/// A single directed edge in the proof graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraphEdge {
    /// Source node id
    pub source: usize,
    /// Target node id
    pub target: usize,
    /// Semantic role of the edge
    pub kind: EdgeKind,
    /// Edge weight (1.0 for structural edges, computed for similarity)
    pub weight: f32,
}

/// A complete proof graph ready for GNN processing.
///
/// Encodes the proof state as a heterogeneous directed graph with
/// typed nodes and edges. This structure is serialised to JSON and
/// sent to the Julia ML server for GNN inference.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofGraph {
    /// All nodes in the graph
    pub nodes: Vec<GraphNode>,
    /// All directed edges
    pub edges: Vec<GraphEdge>,
    /// Mapping from node id to index in `nodes` (for fast lookup)
    pub id_to_index: HashMap<usize, usize>,
    /// The node id of the primary goal (first goal)
    pub goal_node_id: Option<usize>,
    /// Node ids of premise nodes (for ranking)
    pub premise_node_ids: Vec<usize>,
    /// Graph-level metadata
    pub metadata: ProofGraphMetadata,
}

/// Metadata about the proof graph for diagnostics and logging.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofGraphMetadata {
    /// Number of goals in the source proof state
    pub num_goals: usize,
    /// Number of hypotheses
    pub num_hypotheses: usize,
    /// Number of available premises/theorems
    pub num_premises: usize,
    /// Maximum term depth encountered
    pub max_depth: u32,
    /// Total number of subterms expanded
    pub num_subterms: usize,
}

/// Builder for constructing proof graphs from proof states.
///
/// Incrementally adds nodes and edges, handling deduplication and
/// id assignment. The builder traverses terms recursively to extract
/// subterm structure up to a configurable depth limit.
pub struct ProofGraphBuilder {
    /// Nodes accumulated so far
    nodes: Vec<GraphNode>,
    /// Edges accumulated so far
    edges: Vec<GraphEdge>,
    /// Next available node id
    next_id: usize,
    /// Maximum depth for subterm expansion (prevents blow-up on large terms)
    max_depth: u32,
    /// Label-to-id cache for deduplication of constants and named terms
    label_cache: HashMap<String, usize>,
}

impl ProofGraphBuilder {
    /// Create a new builder with the given maximum subterm expansion depth.
    ///
    /// # Arguments
    /// * `max_depth` - Maximum recursion depth for term decomposition.
    ///   Typical values: 3 (fast) to 6 (detailed). Default: 4.
    pub fn new(max_depth: u32) -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            next_id: 0,
            max_depth,
            label_cache: HashMap::new(),
        }
    }

    /// Build a proof graph from a complete proof state.
    ///
    /// This is the primary entry point. It processes:
    /// 1. All goals (as Goal nodes with subterm expansion)
    /// 2. All hypotheses (as Hypothesis nodes)
    /// 3. All available theorems/premises (as Premise nodes)
    /// 4. Cross-references between goals, hypotheses, and premises
    pub fn build_from_proof_state(&mut self, state: &ProofState) -> ProofGraph {
        let mut goal_node_id = None;
        let mut premise_node_ids = Vec::new();

        // Phase 1: Add goal nodes
        for (idx, goal) in state.goals.iter().enumerate() {
            let gid = self.add_goal(goal, idx);
            if idx == 0 {
                goal_node_id = Some(gid);
            }
        }

        // Phase 2: Add hypothesis nodes from context
        let hyp_ids = self.add_hypotheses_from_context(&state.context);

        // Phase 2b: Add definition nodes from context
        let def_ids = self.add_definitions_from_context(&state.context);

        // Phase 3: Add premise/theorem nodes from context
        for theorem in &state.context.theorems {
            let pid = self.add_premise(theorem);
            premise_node_ids.push(pid);
        }

        // Phase 4: Add dependency edges from goals to hypotheses/definitions/premises
        if let Some(gid) = goal_node_id {
            for &hid in &hyp_ids {
                self.add_edge(gid, hid, EdgeKind::DependsOn, 1.0);
                self.add_edge(hid, gid, EdgeKind::UsefulFor, 1.0);
            }
            for &did in &def_ids {
                self.add_edge(gid, did, EdgeKind::DependsOn, 0.9);
                self.add_edge(did, gid, EdgeKind::UsefulFor, 0.9);
            }
            for &pid in &premise_node_ids {
                self.add_edge(gid, pid, EdgeKind::DependsOn, 0.8);
                self.add_edge(pid, gid, EdgeKind::UsefulFor, 0.8);
            }
        }

        // Phase 5: Add shared-structure edges between premises
        self.add_shared_structure_edges(&premise_node_ids);

        // Build id-to-index mapping
        let id_to_index: HashMap<usize, usize> = self
            .nodes
            .iter()
            .enumerate()
            .map(|(idx, node)| (node.id, idx))
            .collect();

        let max_depth = self.nodes.iter().map(|n| n.term_depth).max().unwrap_or(0);
        let num_subterms = self
            .nodes
            .iter()
            .filter(|n| n.kind == NodeKind::Subterm)
            .count();

        let metadata = ProofGraphMetadata {
            num_goals: state.goals.len(),
            num_hypotheses: state
                .goals
                .iter()
                .map(|g| g.hypotheses.len())
                .sum::<usize>()
                + state.context.variables.len(),
            num_premises: state.context.theorems.len(),
            max_depth,
            num_subterms,
        };

        ProofGraph {
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            id_to_index,
            goal_node_id,
            premise_node_ids,
            metadata,
        }
    }

    /// Add a goal node and recursively expand its target term.
    fn add_goal(&mut self, goal: &Goal, index: usize) -> usize {
        let label = format!("goal_{}: {}", index, goal.target);
        let gid = self.add_node(NodeKind::Goal, &label, 0);

        // Expand the goal target term into subterm nodes
        self.expand_term(&goal.target, gid, 1);

        // Add hypothesis nodes local to this goal
        for hyp in &goal.hypotheses {
            let hid = self.add_hypothesis(hyp);
            self.add_edge(gid, hid, EdgeKind::DependsOn, 1.0);
            self.add_edge(hid, gid, EdgeKind::UsefulFor, 1.0);
        }

        gid
    }

    /// Add a hypothesis node.
    fn add_hypothesis(&mut self, hyp: &Hypothesis) -> usize {
        let label = format!("{}: {}", hyp.name, hyp.ty);
        let hid = self.add_node(NodeKind::Hypothesis, &label, 0);

        // Expand the hypothesis type
        let type_id = self.expand_term(&hyp.ty, hid, 1);
        if let Some(tid) = type_id {
            self.add_edge(hid, tid, EdgeKind::HasType, 1.0);
        }

        // If the hypothesis has a body (definition), expand it too
        if let Some(ref body) = hyp.body {
            self.expand_term(body, hid, 1);
        }

        // Wire type_info annotations as edges
        if let Some(ref info) = hyp.type_info {
            self.add_type_info_edges(hid, info);
        }

        hid
    }

    /// Add hypotheses from the global context (variables).
    fn add_hypotheses_from_context(&mut self, ctx: &Context) -> Vec<usize> {
        let mut ids = Vec::new();
        for var in &ctx.variables {
            let label = format!("{}: {}", var.name, var.ty);
            let vid = self.add_node(NodeKind::Hypothesis, &label, 0);
            self.expand_term(&var.ty, vid, 1);

            // Wire type_info annotations as edges
            if let Some(ref info) = var.type_info {
                self.add_type_info_edges(vid, info);
            }

            ids.push(vid);
        }
        ids
    }

    /// Add definition nodes from the global context.
    fn add_definitions_from_context(&mut self, ctx: &Context) -> Vec<usize> {
        let mut ids = Vec::new();
        for def in &ctx.definitions {
            let did = self.add_definition(def);
            ids.push(did);
        }
        ids
    }

    /// Add a definition node.
    fn add_definition(&mut self, def: &Definition) -> usize {
        let label = format!("{}: {}", def.name, def.ty);
        let did = self.add_node(NodeKind::Hypothesis, &label, 0);

        // Expand the definition type
        let type_id = self.expand_term(&def.ty, did, 1);
        if let Some(tid) = type_id {
            self.add_edge(did, tid, EdgeKind::HasType, 1.0);
        }

        // Expand the definition body
        self.expand_term(&def.body, did, 1);

        // Wire type_info annotations as edges
        if let Some(ref info) = def.type_info {
            self.add_type_info_edges(did, info);
        }

        did
    }

    /// Add a premise (theorem/lemma) node.
    fn add_premise(&mut self, theorem: &Theorem) -> usize {
        let label = format!("{}: {}", theorem.name, theorem.statement);
        let pid = self.add_node(NodeKind::Premise, &label, 0);

        // Expand the statement term
        self.expand_term(&theorem.statement, pid, 1);

        pid
    }

    /// Recursively expand a term into subterm nodes up to max_depth.
    ///
    /// Returns the node id of the root subterm node (if created),
    /// or None if the term was too deep or already cached.
    fn expand_term(&mut self, term: &Term, parent_id: usize, depth: u32) -> Option<usize> {
        if depth > self.max_depth {
            return None;
        }

        match term {
            Term::Var(name) => {
                let nid = self.add_or_get_node(NodeKind::Subterm, name, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                Some(nid)
            },
            Term::Const(name) => {
                let nid = self.add_or_get_node(NodeKind::Constant, name, depth);
                self.add_edge(parent_id, nid, EdgeKind::References, 1.0);
                Some(nid)
            },
            Term::App { func, args } => {
                let label = format!("app@{}", depth);
                let nid = self.add_node(NodeKind::Subterm, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                // Expand function and arguments
                self.expand_term(func, nid, depth + 1);
                for arg in args {
                    self.expand_term(arg, nid, depth + 1);
                }
                Some(nid)
            },
            Term::Lambda {
                param,
                param_type,
                body,
            } => {
                let label = format!("lambda_{}", param);
                let nid = self.add_node(NodeKind::Binder, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                if let Some(pt) = param_type {
                    if let Some(tid) = self.expand_term(pt, nid, depth + 1) {
                        self.add_edge(nid, tid, EdgeKind::HasType, 1.0);
                    }
                }
                if let Some(bid) = self.expand_term(body, nid, depth + 1) {
                    self.add_edge(nid, bid, EdgeKind::BindsOver, 1.0);
                }
                Some(nid)
            },
            Term::Pi {
                param,
                param_type,
                body,
            } => {
                let label = format!("pi_{}", param);
                let nid = self.add_node(NodeKind::Binder, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                if let Some(tid) = self.expand_term(param_type, nid, depth + 1) {
                    self.add_edge(nid, tid, EdgeKind::HasType, 1.0);
                }
                if let Some(bid) = self.expand_term(body, nid, depth + 1) {
                    self.add_edge(nid, bid, EdgeKind::BindsOver, 1.0);
                }
                Some(nid)
            },
            Term::Sigma {
                param,
                param_type,
                body,
            } => {
                let label = format!("sigma_{}", param);
                let nid = self.add_node(NodeKind::Binder, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                if let Some(tid) = self.expand_term(param_type, nid, depth + 1) {
                    self.add_edge(nid, tid, EdgeKind::HasType, 1.0);
                }
                if let Some(bid) = self.expand_term(body, nid, depth + 1) {
                    self.add_edge(nid, bid, EdgeKind::BindsOver, 1.0);
                }
                Some(nid)
            },
            Term::Type(level) | Term::Sort(level) | Term::Universe(level) => {
                let label = format!("Type{}", level);
                let nid = self.add_or_get_node(NodeKind::TypeExpr, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                Some(nid)
            },
            Term::Let {
                name,
                ty,
                value,
                body,
            } => {
                let label = format!("let_{}", name);
                let nid = self.add_node(NodeKind::Binder, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                if let Some(t) = ty {
                    if let Some(tid) = self.expand_term(t, nid, depth + 1) {
                        self.add_edge(nid, tid, EdgeKind::HasType, 1.0);
                    }
                }
                self.expand_term(value, nid, depth + 1);
                if let Some(bid) = self.expand_term(body, nid, depth + 1) {
                    self.add_edge(nid, bid, EdgeKind::BindsOver, 1.0);
                }
                Some(nid)
            },
            Term::Match { scrutinee, .. } => {
                let label = format!("match@{}", depth);
                let nid = self.add_node(NodeKind::Subterm, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                self.expand_term(scrutinee, nid, depth + 1);
                Some(nid)
            },
            Term::Fix { name, ty, body } => {
                let label = format!("fix_{}", name);
                let nid = self.add_node(NodeKind::Binder, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);

                if let Some(t) = ty {
                    if let Some(tid) = self.expand_term(t, nid, depth + 1) {
                        self.add_edge(nid, tid, EdgeKind::HasType, 1.0);
                    }
                }
                if let Some(bid) = self.expand_term(body, nid, depth + 1) {
                    self.add_edge(nid, bid, EdgeKind::BindsOver, 1.0);
                }
                Some(nid)
            },
            Term::Hole(name) => {
                let label = format!("?{}", name);
                let nid = self.add_node(NodeKind::Subterm, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                Some(nid)
            },
            Term::Meta(id) => {
                let label = format!("?meta_{}", id);
                let nid = self.add_node(NodeKind::Subterm, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                Some(nid)
            },
            Term::ProverSpecific { prover, .. } => {
                let label = format!("<{}-opaque>", prover);
                let nid = self.add_node(NodeKind::Subterm, &label, depth);
                self.add_edge(parent_id, nid, EdgeKind::Contains, 1.0);
                Some(nid)
            },
        }
    }

    /// Add edges from a node to represent its [`TypeInfo`] annotations.
    ///
    /// Creates labelled subterm nodes for multiplicity, effect, and modality
    /// decorations and connects them with the appropriate edge kind.
    fn add_type_info_edges(&mut self, node_id: usize, info: &crate::types::TypeInfo) {
        if let Some(ref mult) = info.multiplicity {
            let label = format!("mult:{:?}", mult);
            let mid = self.add_node(NodeKind::Subterm, &label, 1);
            self.add_edge(node_id, mid, EdgeKind::HasMultiplicity, 1.0);
        }

        if !info.effects.is_empty() {
            for eff in &info.effects.effects {
                let label = format!("effect:{:?}", eff);
                let eid = self.add_node(NodeKind::Subterm, &label, 1);
                self.add_edge(node_id, eid, EdgeKind::HasEffect, 1.0);
            }
        }

        if let Some(ref modality) = info.modality {
            let label = format!("modality:{:?}", modality);
            let mid = self.add_node(NodeKind::Subterm, &label, 1);
            self.add_edge(node_id, mid, EdgeKind::HasModality, 1.0);
        }
    }

    /// Add shared-structure edges between premise nodes that share constants.
    ///
    /// Two premises sharing named constants likely have semantic overlap,
    /// which the GNN can exploit for better message passing.
    fn add_shared_structure_edges(&mut self, premise_ids: &[usize]) {
        // Collect constants reachable from each premise
        let mut premise_constants: Vec<Vec<usize>> = Vec::new();

        for &pid in premise_ids {
            let mut constants = Vec::new();
            self.collect_reachable_constants(pid, &mut constants, 0);
            premise_constants.push(constants);
        }

        // Add edges between premises sharing constants
        for i in 0..premise_ids.len() {
            for j in (i + 1)..premise_ids.len() {
                let shared = count_shared(&premise_constants[i], &premise_constants[j]);
                if shared > 0 {
                    let total = (premise_constants[i].len() + premise_constants[j].len()) as f32;
                    let weight = (2.0 * shared as f32) / total.max(1.0);
                    // Jaccard-like similarity as edge weight
                    if weight > 0.1 {
                        self.add_edge(
                            premise_ids[i],
                            premise_ids[j],
                            EdgeKind::SharedStructure,
                            weight,
                        );
                        self.add_edge(
                            premise_ids[j],
                            premise_ids[i],
                            EdgeKind::SharedStructure,
                            weight,
                        );
                    }
                }
            }
        }
    }

    /// Walk edges from a node to collect reachable Constant node ids.
    fn collect_reachable_constants(&self, node_id: usize, constants: &mut Vec<usize>, depth: u32) {
        if depth > self.max_depth {
            return;
        }

        for edge in &self.edges {
            if edge.source == node_id {
                let target_idx = self.nodes.iter().position(|n| n.id == edge.target);
                if let Some(idx) = target_idx {
                    if self.nodes[idx].kind == NodeKind::Constant {
                        constants.push(edge.target);
                    }
                    if matches!(edge.kind, EdgeKind::Contains | EdgeKind::BindsOver) {
                        self.collect_reachable_constants(edge.target, constants, depth + 1);
                    }
                }
            }
        }
    }

    /// Add a node, returning its id.
    fn add_node(&mut self, kind: NodeKind, label: &str, depth: u32) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.nodes.push(GraphNode {
            id,
            kind,
            label: label.to_string(),
            term_depth: depth,
            features: Vec::new(), // Populated later by TermFeatureExtractor
        });
        id
    }

    /// Add a node or return existing id if label was seen before.
    ///
    /// Used for constants and named variables to avoid duplicate nodes
    /// for the same symbol appearing in multiple terms.
    fn add_or_get_node(&mut self, kind: NodeKind, label: &str, depth: u32) -> usize {
        if let Some(&existing_id) = self.label_cache.get(label) {
            return existing_id;
        }
        let id = self.add_node(kind, label, depth);
        self.label_cache.insert(label.to_string(), id);
        id
    }

    /// Add a directed edge.
    fn add_edge(&mut self, source: usize, target: usize, kind: EdgeKind, weight: f32) {
        self.edges.push(GraphEdge {
            source,
            target,
            kind,
            weight,
        });
    }
}

/// Count elements shared between two sorted-or-unsorted vectors.
fn count_shared(a: &[usize], b: &[usize]) -> usize {
    let mut count = 0;
    for &x in a {
        if b.contains(&x) {
            count += 1;
        }
    }
    count
}

impl ProofGraph {
    /// Number of nodes in the graph.
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges in the graph.
    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }

    /// Get adjacency list representation (source -> vec of (target, edge_kind, weight)).
    pub fn adjacency_list(&self) -> HashMap<usize, Vec<(usize, EdgeKind, f32)>> {
        let mut adj: HashMap<usize, Vec<(usize, EdgeKind, f32)>> = HashMap::new();
        for edge in &self.edges {
            adj.entry(edge.source)
                .or_default()
                .push((edge.target, edge.kind, edge.weight));
        }
        adj
    }

    /// Get the sparse adjacency matrix as (row_indices, col_indices, values).
    ///
    /// This format is directly consumable by the Julia GNN encoder.
    pub fn sparse_adjacency(&self) -> (Vec<usize>, Vec<usize>, Vec<f32>) {
        let mut rows = Vec::with_capacity(self.edges.len());
        let mut cols = Vec::with_capacity(self.edges.len());
        let mut vals = Vec::with_capacity(self.edges.len());

        for edge in &self.edges {
            if let (Some(&src_idx), Some(&tgt_idx)) = (
                self.id_to_index.get(&edge.source),
                self.id_to_index.get(&edge.target),
            ) {
                rows.push(src_idx);
                cols.push(tgt_idx);
                vals.push(edge.weight);
            }
        }

        (rows, cols, vals)
    }

    /// Get the feature matrix as a flat row-major vector.
    ///
    /// Shape: (num_nodes, feature_dim). Feature dim is determined by
    /// the TermFeatureExtractor that populated node features.
    pub fn feature_matrix(&self) -> Vec<f32> {
        self.nodes
            .iter()
            .flat_map(|n| n.features.iter().copied())
            .collect()
    }

    /// Get a node by its id.
    pub fn get_node(&self, id: usize) -> Option<&GraphNode> {
        self.id_to_index.get(&id).map(|&idx| &self.nodes[idx])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, Hypothesis, Theorem, Variable};

    /// Helper: create a simple proof state with one goal and some context.
    fn sample_proof_state() -> ProofState {
        let goal_term = Term::Pi {
            param: "n".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::App {
                func: Box::new(Term::Const("is_even".to_string())),
                args: vec![Term::App {
                    func: Box::new(Term::Const("add".to_string())),
                    args: vec![Term::Var("n".to_string()), Term::Var("n".to_string())],
                }],
            }),
        };

        let hyp = Hypothesis {
            name: "h_nat".to_string(),
            ty: Term::Const("Nat".to_string()),
            body: None,
        };

        let theorem = Theorem {
            name: "even_add_self".to_string(),
            statement: Term::Pi {
                param: "m".to_string(),
                param_type: Box::new(Term::Const("Nat".to_string())),
                body: Box::new(Term::App {
                    func: Box::new(Term::Const("is_even".to_string())),
                    args: vec![Term::App {
                        func: Box::new(Term::Const("add".to_string())),
                        args: vec![Term::Var("m".to_string()), Term::Var("m".to_string())],
                    }],
                }),
            },
            proof: None,
            aspects: vec!["arithmetic".to_string()],
        };

        let theorem2 = Theorem {
            name: "zero_is_even".to_string(),
            statement: Term::App {
                func: Box::new(Term::Const("is_even".to_string())),
                args: vec![Term::Const("zero".to_string())],
            },
            proof: None,
            aspects: vec!["base_case".to_string()],
        };

        ProofState {
            goals: vec![Goal {
                id: "goal_0".to_string(),
                target: goal_term,
                hypotheses: vec![hyp],
            }],
            context: Context {
                theorems: vec![theorem, theorem2],
                axioms: Vec::new(),
                definitions: Vec::new(),
                variables: vec![Variable {
                    name: "n".to_string(),
                    ty: Term::Const("Nat".to_string()),
                }],
            },
            proof_script: Vec::new(),
            metadata: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_build_proof_graph_from_state() {
        let state = sample_proof_state();
        let mut builder = ProofGraphBuilder::new(4);
        let graph = builder.build_from_proof_state(&state);

        // Must have at least: 1 goal + 1 hyp + 2 premises + subterms
        assert!(
            graph.num_nodes() >= 4,
            "Expected at least 4 nodes, got {}",
            graph.num_nodes()
        );
        assert!(graph.num_edges() > 0, "Expected at least 1 edge");
        assert!(graph.goal_node_id.is_some(), "Must have a goal node");
        assert_eq!(graph.premise_node_ids.len(), 2, "Must have 2 premise nodes");
        assert_eq!(graph.metadata.num_goals, 1);
        assert_eq!(graph.metadata.num_premises, 2);
    }

    #[test]
    fn test_graph_has_goal_to_premise_edges() {
        let state = sample_proof_state();
        let mut builder = ProofGraphBuilder::new(3);
        let graph = builder.build_from_proof_state(&state);

        let goal_id = graph.goal_node_id.unwrap();

        // There should be DependsOn edges from goal to premises
        let depends_on_edges: Vec<_> = graph
            .edges
            .iter()
            .filter(|e| e.source == goal_id && e.kind == EdgeKind::DependsOn)
            .collect();

        assert!(
            !depends_on_edges.is_empty(),
            "Goal must have DependsOn edges to context"
        );
    }

    #[test]
    fn test_shared_structure_detection() {
        let state = sample_proof_state();
        let mut builder = ProofGraphBuilder::new(4);
        let graph = builder.build_from_proof_state(&state);

        // Both theorems share "is_even" and "add" constants, so there
        // should be SharedStructure edges between them
        let shared_edges: Vec<_> = graph
            .edges
            .iter()
            .filter(|e| e.kind == EdgeKind::SharedStructure)
            .collect();

        assert!(
            !shared_edges.is_empty(),
            "Premises sharing constants should have SharedStructure edges"
        );
    }

    #[test]
    fn test_sparse_adjacency_format() {
        let state = sample_proof_state();
        let mut builder = ProofGraphBuilder::new(2);
        let graph = builder.build_from_proof_state(&state);

        let (rows, cols, vals) = graph.sparse_adjacency();
        assert_eq!(rows.len(), cols.len());
        assert_eq!(rows.len(), vals.len());
        assert_eq!(rows.len(), graph.num_edges());

        // All indices must be valid
        let n = graph.num_nodes();
        for (&r, &c) in rows.iter().zip(cols.iter()) {
            assert!(r < n, "Row index {} out of bounds (n={})", r, n);
            assert!(c < n, "Col index {} out of bounds (n={})", c, n);
        }
    }

    #[test]
    fn test_empty_proof_state() {
        let state = ProofState::default();
        let mut builder = ProofGraphBuilder::new(4);
        let graph = builder.build_from_proof_state(&state);

        assert_eq!(graph.num_nodes(), 0);
        assert_eq!(graph.num_edges(), 0);
        assert!(graph.goal_node_id.is_none());
    }

    #[test]
    fn test_depth_limit_prevents_blowup() {
        // Create a deeply nested term
        let mut term = Term::Var("x".to_string());
        for _ in 0..20 {
            term = Term::Lambda {
                param: "a".to_string(),
                param_type: Some(Box::new(Term::Const("T".to_string()))),
                body: Box::new(term),
            };
        }

        let state = ProofState::new(term);
        let mut builder = ProofGraphBuilder::new(3); // Shallow limit
        let graph = builder.build_from_proof_state(&state);

        // Should not have expanded all 20 levels
        assert!(
            graph.num_nodes() < 50,
            "Depth limit should prevent node explosion, got {} nodes",
            graph.num_nodes()
        );
    }

    #[test]
    fn test_constant_deduplication() {
        // Two goals referencing the same constant "Nat" should share the node
        let state = ProofState {
            goals: vec![
                Goal {
                    id: "g0".to_string(),
                    target: Term::Const("Nat".to_string()),
                    hypotheses: vec![],
                },
                Goal {
                    id: "g1".to_string(),
                    target: Term::Const("Nat".to_string()),
                    hypotheses: vec![],
                },
            ],
            context: Context::default(),
            proof_script: Vec::new(),
            metadata: std::collections::HashMap::new(),
        };

        let mut builder = ProofGraphBuilder::new(4);
        let graph = builder.build_from_proof_state(&state);

        // Count Constant nodes labeled "Nat"
        let nat_nodes: Vec<_> = graph
            .nodes
            .iter()
            .filter(|n| n.kind == NodeKind::Constant && n.label == "Nat")
            .collect();

        assert_eq!(
            nat_nodes.len(),
            1,
            "Constant 'Nat' should be deduplicated to 1 node, got {}",
            nat_nodes.len()
        );
    }
}
