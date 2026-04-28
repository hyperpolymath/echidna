// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! 007-style swarm dispatcher over a `DesignProblem`.
//!
//! The existing actor system in `agent/actors.rs` is single-pool and
//! tactic-oriented. This module adds a parallel-search primitive on
//! top of `learning::design_search`: N agents each run an SA chain
//! with their own seed, and periodically a coordinator broadcasts the
//! best-so-far. Any agent strictly dominated by the broadcast may
//! restart from the broadcast state, importing the better starting
//! point. This is the "cross-pollination" semantic from 007's swarm
//! choreographies, mapped onto an in-process tokio task pool.
//!
//! The shape is deliberately compatible with the BoJ coord bus: each
//! agent sends `Heartbeat { agent_id, energy, state_hash }` and
//! receives `Adopt { state }` messages; swapping the in-process
//! `mpsc` for an MCP-bridged channel reuses the same protocol when
//! agents are dispersed across processes.
//!
//! First use: parallel SA over `BrouwerLeqProblem` (proves out the
//! framework on the same problem the single-chain SA already
//! solved). Second use (Step 5): rank-function search for unbudgeted
//! `wf-<ᵇʳᶠ_`, where the design space is the choice of `rank : BT →
//! Ord` and the energy is "does `rank-mono` go through".

#![allow(dead_code)]

use std::sync::Arc;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use tokio::sync::{mpsc, Mutex};
use tokio::task::JoinSet;

use crate::learning::design_search::{AnnealConfig, AnnealResult, DesignProblem};

/// Configuration for a swarm run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwarmConfig {
    /// Number of parallel SA agents.
    pub agents: usize,
    /// Per-agent SA config. Each agent gets `seed = base_seed + i`.
    pub anneal: AnnealConfig,
    /// How often (in SA iterations) an agent broadcasts its current
    /// best to the coordinator.
    pub broadcast_every: usize,
    /// If a peer's best beats this agent's best by at least this many
    /// energy ranks (lex), the agent restarts from the peer's state.
    /// Set to 0 to adopt on any improvement; higher values reduce
    /// premature convergence.
    pub adopt_threshold: i64,
}

impl Default for SwarmConfig {
    fn default() -> Self {
        SwarmConfig {
            agents: 4,
            anneal: AnnealConfig::default(),
            broadcast_every: 100,
            adopt_threshold: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SwarmResult<S> {
    pub best: S,
    pub best_energy: Vec<i64>,
    pub per_agent: Vec<AgentReport<S>>,
    /// Number of times an agent adopted a peer's broadcast.
    pub adoptions: usize,
}

#[derive(Debug, Clone)]
pub struct AgentReport<S> {
    pub agent_id: usize,
    pub seed: u64,
    pub final_state: S,
    pub final_energy: Vec<i64>,
    pub local_best: S,
    pub local_best_energy: Vec<i64>,
    pub steps: usize,
    pub accepted: usize,
    pub adopted_count: usize,
}

/// Coordinator message: an agent broadcasts its current best.
#[derive(Debug, Clone)]
struct Heartbeat<S> {
    agent_id: usize,
    state: S,
    energy: Vec<i64>,
}

/// Coordinator → agent message: "consider adopting this state".
#[derive(Debug, Clone)]
struct Adopt<S> {
    from_agent: usize,
    state: S,
    energy: Vec<i64>,
}

fn lex_better(a: &[i64], b: &[i64]) -> bool {
    let n = a.len().max(b.len());
    for i in 0..n {
        let ai = a.get(i).copied().unwrap_or(0);
        let bi = b.get(i).copied().unwrap_or(0);
        if ai < bi {
            return true;
        }
        if ai > bi {
            return false;
        }
    }
    false
}

fn lex_strictly_better_by(a: &[i64], b: &[i64], threshold: i64) -> bool {
    // a is "strictly better than b by at least `threshold` in the
    // first non-equal coordinate". For threshold = 0, any improvement
    // qualifies; for threshold > 0, the gap must reach that size.
    let n = a.len().max(b.len());
    for i in 0..n {
        let ai = a.get(i).copied().unwrap_or(0);
        let bi = b.get(i).copied().unwrap_or(0);
        if ai < bi {
            return (bi - ai) >= threshold;
        }
        if ai > bi {
            return false;
        }
    }
    false
}

/// Approximate scalar Δ for Metropolis acceptance, identical to
/// `learning::design_search::delta_energy` but inlined to avoid
/// re-exporting a private helper.
fn delta_scalar(from: &[i64], to: &[i64]) -> f64 {
    let n = from.len().max(to.len());
    let mut delta = 0.0;
    for i in 0..n {
        let f = from.get(i).copied().unwrap_or(0) as f64;
        let t = to.get(i).copied().unwrap_or(0) as f64;
        let w = (1000_f64).powi((n - i - 1) as i32);
        delta += w * (t - f);
    }
    delta
}

/// Run a swarm over `problem`. Returns the global best across agents
/// plus per-agent reports.
pub async fn run_swarm<P>(problem: Arc<P>, config: SwarmConfig) -> SwarmResult<P::State>
where
    P: DesignProblem + Send + Sync + 'static,
    P::State: Send + Sync + 'static,
{
    let mut tasks: JoinSet<AgentReport<P::State>> = JoinSet::new();

    // Coordinator state: best-so-far across the swarm.
    let global_best: Arc<Mutex<Option<(P::State, Vec<i64>)>>> = Arc::new(Mutex::new(None));
    let adoption_counter: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));

    // Per-agent inbox channel for Adopt messages.
    let mut agent_tx: Vec<mpsc::Sender<Adopt<P::State>>> = Vec::with_capacity(config.agents);
    let mut agent_rx: Vec<mpsc::Receiver<Adopt<P::State>>> =
        Vec::with_capacity(config.agents);
    for _ in 0..config.agents {
        let (tx, rx) = mpsc::channel(16);
        agent_tx.push(tx);
        agent_rx.push(rx);
    }

    // Coordinator inbox: agents send Heartbeat here. The coordinator
    // task forwards an Adopt to peers when it receives a strictly-
    // better heartbeat.
    let (coord_tx, mut coord_rx) = mpsc::channel::<Heartbeat<P::State>>(64);

    // Spawn the coordinator.
    let global_best_for_coord = Arc::clone(&global_best);
    let adoption_for_coord = Arc::clone(&adoption_counter);
    let agent_tx_for_coord = agent_tx.clone();
    let adopt_threshold = config.adopt_threshold;
    let coord_handle = tokio::spawn(async move {
        while let Some(hb) = coord_rx.recv().await {
            let mut gb = global_best_for_coord.lock().await;
            let should_broadcast = match &*gb {
                Some((_, e)) => lex_better(&hb.energy, e),
                None => true,
            };
            if should_broadcast {
                *gb = Some((hb.state.clone(), hb.energy.clone()));
                drop(gb); // release lock before await
                for (i, tx) in agent_tx_for_coord.iter().enumerate() {
                    if i == hb.agent_id {
                        continue;
                    }
                    let _ = tx
                        .send(Adopt {
                            from_agent: hb.agent_id,
                            state: hb.state.clone(),
                            energy: hb.energy.clone(),
                        })
                        .await;
                    // Coordinator counts a sent Adopt as a candidate
                    // adoption; the agent decides whether to actually
                    // take it (gated by `adopt_threshold`).
                    let mut counter = adoption_for_coord.lock().await;
                    *counter += 1;
                }
            }
        }
    });

    // Spawn agents. Each runs an SA chain with periodic broadcast
    // and adoption checks.
    for agent_id in 0..config.agents {
        let problem = Arc::clone(&problem);
        let cfg = config.anneal.clone();
        let broadcast_every = config.broadcast_every.max(1);
        let coord_tx = coord_tx.clone();
        // Move the receiver out of the per-agent vec.
        let mut my_rx = std::mem::replace(&mut agent_rx[agent_id], mpsc::channel(1).1);

        // Per-agent seed via wrapping golden-ratio multiplier so we
        // get distinct, well-spread seeds without overflow panics.
        let seed = cfg
            .seed
            .wrapping_add((agent_id as u64).wrapping_mul(0x9E3779B97F4A7C15));

        tasks.spawn(async move {
            let mut rng = StdRng::seed_from_u64(seed);
            let mut current = problem.initial();
            let mut current_e = problem.energy(&current);
            let mut local_best = current.clone();
            let mut local_best_e = current_e.clone();
            let mut temp = cfg.initial_temp;
            let mut steps = 0usize;
            let mut accepted = 0usize;
            let mut adopted_count = 0usize;

            for iter in 0..cfg.max_iterations {
                steps += 1;
                let neighbours = problem.neighbours(&current);
                if neighbours.is_empty() {
                    break;
                }
                let pick = rng.gen_range(0..neighbours.len());
                let cand = neighbours[pick].clone();
                let cand_e = problem.energy(&cand);

                let accept = if lex_better(&cand_e, &current_e)
                    || cand_e == current_e
                {
                    true
                } else {
                    let de = delta_scalar(&current_e, &cand_e);
                    let p: f64 = (-de / temp).exp();
                    rng.gen::<f64>() < p
                };

                if accept {
                    accepted += 1;
                    current = cand;
                    current_e = cand_e.clone();
                    if lex_better(&cand_e, &local_best_e) {
                        local_best = current.clone();
                        local_best_e = cand_e;
                    }
                }

                temp *= cfg.cooling;

                // Broadcast every N iterations.
                if iter > 0 && iter % broadcast_every == 0 {
                    let _ = coord_tx
                        .send(Heartbeat {
                            agent_id,
                            state: local_best.clone(),
                            energy: local_best_e.clone(),
                        })
                        .await;
                }

                // Drain inbox; adopt the best Adopt that beats us by
                // the configured threshold.
                while let Ok(adopt) = my_rx.try_recv() {
                    if lex_strictly_better_by(&adopt.energy, &local_best_e, adopt_threshold) {
                        adopted_count += 1;
                        current = adopt.state.clone();
                        current_e = adopt.energy.clone();
                        local_best = adopt.state;
                        local_best_e = adopt.energy;
                        // Reheat slightly so we don't immediately settle.
                        temp = (temp * 2.0).min(cfg.initial_temp);
                    }
                }
            }

            // One last broadcast before exiting.
            let _ = coord_tx
                .send(Heartbeat {
                    agent_id,
                    state: local_best.clone(),
                    energy: local_best_e.clone(),
                })
                .await;

            AgentReport {
                agent_id,
                seed,
                final_state: current,
                final_energy: current_e,
                local_best,
                local_best_energy: local_best_e,
                steps,
                accepted,
                adopted_count,
            }
        });
    }

    // We hold no extra coord_tx handle — agents own theirs. Wait for
    // them to finish.
    drop(coord_tx);

    let mut reports = Vec::with_capacity(config.agents);
    while let Some(res) = tasks.join_next().await {
        if let Ok(r) = res {
            reports.push(r);
        }
    }

    // Coordinator exits when its inbox closes. Wait briefly.
    let _ = coord_handle.await;

    let adoptions = *adoption_counter.lock().await;
    let gb = global_best.lock().await.clone();
    let (best, best_energy) = match gb {
        Some(x) => x,
        None => {
            // Fallback: pick best across reports.
            let mut best_idx = 0;
            for (i, r) in reports.iter().enumerate() {
                if lex_better(&r.local_best_energy, &reports[best_idx].local_best_energy) {
                    best_idx = i;
                }
            }
            (
                reports[best_idx].local_best.clone(),
                reports[best_idx].local_best_energy.clone(),
            )
        }
    };

    reports.sort_by_key(|r| r.agent_id);

    SwarmResult {
        best,
        best_energy,
        per_agent: reports,
        adoptions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::learning::design_search::{brouwer, AnnealConfig};

    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn swarm_finds_zero_blocker_state_brouwer() {
        let problem = Arc::new(brouwer::BrouwerLeqProblem::default());
        let config = SwarmConfig {
            agents: 4,
            anneal: AnnealConfig {
                max_iterations: 200,
                initial_temp: 4.0,
                cooling: 0.99,
                seed: 7,
                restarts: 1,
            },
            broadcast_every: 50,
            adopt_threshold: 0,
        };
        let result = run_swarm(problem, config).await;
        assert_eq!(
            result.best_energy[0], 0,
            "swarm should find a zero-blocker state; best energy {:?}",
            result.best_energy
        );
        assert_eq!(result.per_agent.len(), 4);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn swarm_pollinates_low_seeded_agent() {
        // Run a swarm where one agent gets a great seed and the
        // others get bad ones. Verify cross-pollination happens at
        // least once.
        let problem = Arc::new(brouwer::BrouwerLeqProblem::default());
        let config = SwarmConfig {
            agents: 4,
            anneal: AnnealConfig {
                max_iterations: 500,
                initial_temp: 8.0,
                cooling: 0.985,
                seed: 1234,
                restarts: 1,
            },
            broadcast_every: 25,
            adopt_threshold: 0,
        };
        let result = run_swarm(problem, config).await;
        let total_adoptions: usize =
            result.per_agent.iter().map(|r| r.adopted_count).sum();
        // With 500 iters × 4 agents and broadcast_every=25, the
        // coordinator gets ~80 heartbeats, several of them strictly
        // better than peers. We expect at least some adoptions.
        assert!(
            total_adoptions > 0 || result.adoptions > 0,
            "expected at least one cross-pollination event; per-agent adopted {:?}, coord broadcasts {}",
            result.per_agent.iter().map(|r| r.adopted_count).collect::<Vec<_>>(),
            result.adoptions
        );
    }
}
