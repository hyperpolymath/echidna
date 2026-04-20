// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Monte Carlo Tree Search over tactic space.
//!
//! Each node = a `ProofState`. Each edge = a `Tactic` proposed by the
//! policy network (or the prover's own `suggest_tactics`). UCB1
//! selection with a neural prior; expansion calls the prover backend
//! to apply one tactic; value comes from either a rollout or the
//! value-network head. Reward 1 if a descendant reaches a closed
//! proof state, 0 otherwise.
//!
//! This is the search layer that lets one pass through the policy
//! escape local minima — essential for the self-improving loop,
//! because improvements of the *policy* alone saturate quickly
//! without explicit lookahead.

#![allow(dead_code)]

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use async_trait::async_trait;
use tokio::sync::Mutex;

use crate::core::{ProofState, Tactic, TacticResult};
use crate::provers::ProverBackend;

/// UCB1 exploration constant. 1.4 ≈ √2 — the theoretical default.
/// Tune upward on wider tactic spaces; downward when the prior is
/// already sharp.
pub const UCB1_C: f64 = 1.4;

/// Abstract policy head: given a state, return (tactic, prior)
/// pairs. A real implementation calls the Julia ML server's
/// `/tactic/rank` endpoint; for cold-start, backends' own
/// `suggest_tactics` is a fine substitute.
#[async_trait]
pub trait TacticPolicy: Send + Sync {
    async fn propose(&self, state: &ProofState, top_k: usize)
        -> anyhow::Result<Vec<(Tactic, f64)>>;
}

/// Abstract value head: given a state, return an estimate of
/// probability-of-proof in [0, 1]. Cold-start: constant 0.5.
#[async_trait]
pub trait ValueHead: Send + Sync {
    async fn estimate(&self, state: &ProofState) -> anyhow::Result<f64>;
}

pub struct ConstantValue(pub f64);

#[async_trait]
impl ValueHead for ConstantValue {
    async fn estimate(&self, _state: &ProofState) -> anyhow::Result<f64> {
        Ok(self.0)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SearchConfig {
    pub budget: Duration,
    pub max_depth: usize,
    pub top_k_expand: usize,
    pub min_rollout: usize,
}

impl Default for SearchConfig {
    fn default() -> Self {
        SearchConfig {
            budget: Duration::from_secs(10),
            max_depth: 30,
            top_k_expand: 8,
            min_rollout: 3,
        }
    }
}

#[derive(Debug)]
struct Node {
    state: ProofState,
    parent: Option<usize>,
    children: Vec<(Tactic, usize)>,
    visits: u64,
    value_sum: f64,
    prior: f64,
    terminal: Option<bool>,
}

/// Outcome of a search run.
#[derive(Debug)]
pub struct SearchResult {
    pub proof_found: bool,
    pub best_script: Vec<Tactic>,
    pub nodes_expanded: usize,
}

pub struct Search<'a> {
    backend: &'a dyn ProverBackend,
    policy: Arc<dyn TacticPolicy>,
    value: Arc<dyn ValueHead>,
    cfg: SearchConfig,
    nodes: Vec<Node>,
    state_index: HashMap<String, usize>,
}

impl<'a> Search<'a> {
    pub fn new(
        backend: &'a dyn ProverBackend,
        policy: Arc<dyn TacticPolicy>,
        value: Arc<dyn ValueHead>,
        cfg: SearchConfig,
    ) -> Self {
        Search {
            backend,
            policy,
            value,
            cfg,
            nodes: Vec::new(),
            state_index: HashMap::new(),
        }
    }

    /// Run MCTS from `root_state`. Stops at the first closed proof or
    /// when the time budget is exhausted.
    pub async fn run(&mut self, root_state: ProofState) -> anyhow::Result<SearchResult> {
        let start = Instant::now();
        let root = self.register(root_state, None, 1.0);
        let mut best_terminal: Option<usize> = None;

        while start.elapsed() < self.cfg.budget {
            let leaf = self.select(root);
            if self.nodes[leaf].terminal == Some(true) {
                best_terminal = Some(leaf);
                break;
            }
            let expanded = self.expand(leaf).await?;
            let value = self.simulate(expanded).await?;
            self.backpropagate(expanded, value);
            if self.nodes[expanded].terminal == Some(true) {
                best_terminal = Some(expanded);
                break;
            }
        }

        let proof_found = best_terminal.is_some();
        let best_script = best_terminal
            .map(|idx| self.reconstruct(idx))
            .unwrap_or_default();
        Ok(SearchResult {
            proof_found,
            best_script,
            nodes_expanded: self.nodes.len(),
        })
    }

    fn register(&mut self, state: ProofState, parent: Option<usize>, prior: f64) -> usize {
        let key = state_key(&state);
        if let Some(&idx) = self.state_index.get(&key) {
            return idx;
        }
        let terminal = if state.goals.is_empty() {
            Some(true)
        } else {
            None
        };
        let idx = self.nodes.len();
        self.nodes.push(Node {
            state,
            parent,
            children: Vec::new(),
            visits: 0,
            value_sum: 0.0,
            prior,
            terminal,
        });
        self.state_index.insert(key, idx);
        idx
    }

    fn select(&self, mut node: usize) -> usize {
        while !self.nodes[node].children.is_empty() && self.nodes[node].terminal.is_none() {
            let parent_visits = self.nodes[node].visits.max(1);
            let mut best_child = None;
            let mut best_score = f64::NEG_INFINITY;
            for &(_, child_idx) in &self.nodes[node].children {
                let c = &self.nodes[child_idx];
                let q = if c.visits == 0 {
                    0.0
                } else {
                    c.value_sum / c.visits as f64
                };
                let u = UCB1_C
                    * c.prior
                    * ((parent_visits as f64).ln() / (1.0 + c.visits as f64)).sqrt();
                let score = q + u;
                if score > best_score {
                    best_score = score;
                    best_child = Some(child_idx);
                }
            }
            match best_child {
                Some(c) => node = c,
                None => break,
            }
        }
        node
    }

    async fn expand(&mut self, leaf: usize) -> anyhow::Result<usize> {
        if self.nodes[leaf].terminal == Some(true) {
            return Ok(leaf);
        }
        let state = self.nodes[leaf].state.clone();
        let proposals = self.policy.propose(&state, self.cfg.top_k_expand).await?;
        let mut first_child = leaf;
        for (tactic, prior) in proposals {
            let result = self.backend.apply_tactic(&state, &tactic).await?;
            let next_state = match result {
                TacticResult::Success(s) => s,
                TacticResult::Error(_) => continue,
                TacticResult::QED => {
                    // QED → synthesise an empty-goals state so the node
                    // is marked terminal by `register`.
                    let mut closed = state.clone();
                    closed.goals.clear();
                    closed.proof_script.push(tactic.clone());
                    closed
                },
            };
            let child = self.register(next_state, Some(leaf), prior);
            self.nodes[leaf].children.push((tactic, child));
            if first_child == leaf {
                first_child = child;
            }
            if self.nodes[child].terminal == Some(true) {
                return Ok(child);
            }
        }
        Ok(first_child)
    }

    async fn simulate(&self, node: usize) -> anyhow::Result<f64> {
        if self.nodes[node].terminal == Some(true) {
            return Ok(1.0);
        }
        self.value.estimate(&self.nodes[node].state).await
    }

    fn backpropagate(&mut self, mut node: usize, value: f64) {
        loop {
            self.nodes[node].visits += 1;
            self.nodes[node].value_sum += value;
            match self.nodes[node].parent {
                Some(p) => node = p,
                None => break,
            }
        }
    }

    fn reconstruct(&self, mut node: usize) -> Vec<Tactic> {
        let mut script = Vec::new();
        while let Some(parent) = self.nodes[node].parent {
            let edge = self.nodes[parent]
                .children
                .iter()
                .find(|(_, idx)| *idx == node)
                .map(|(t, _)| t.clone());
            if let Some(t) = edge {
                script.push(t);
            }
            node = parent;
        }
        script.reverse();
        script
    }
}

fn state_key(state: &ProofState) -> String {
    let goals: Vec<_> = state
        .goals
        .iter()
        .map(|g| format!("{}", g.target))
        .collect();
    goals.join("||")
}

/// Locked reference to a shared Search — convenience for actor-model
/// callers.
pub type SharedSearch<'a> = Arc<Mutex<Search<'a>>>;
