// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: design. Moved verbatim from main.rs (hotspot split).

use super::*;
use crate::output::OutputFormatter;
use anyhow::Result;

/// Design-search command — simulated annealing over candidate
/// axiomatisations, single-chain or parallel swarm. The first
/// concrete problem is `brouwer-leq`, targeting echo-types' Phase 1.3
/// `_≤_` redesign.
pub(crate) async fn design_command(op: DesignOp, formatter: &OutputFormatter) -> Result<()> {
    use echidna::agent::swarm::{run_swarm, SwarmConfig};
    use echidna::learning::design_search::{anneal, brouwer, AnnealConfig, DesignProblem};
    use std::sync::Arc;

    match op {
        DesignOp::Search {
            problem,
            iterations,
            restarts,
            temp,
            cooling,
            seed,
            top,
        } => {
            let cfg = AnnealConfig {
                max_iterations: iterations,
                initial_temp: temp,
                cooling,
                seed,
                restarts,
            };

            match problem.as_str() {
                "brouwer-leq" => {
                    let p = brouwer::BrouwerLeqProblem::default();
                    let result = anneal(&p, &cfg);
                    formatter.info(&format!(
                        "annealer: {} steps, {} accepted ({:.1}%); best energy {:?}",
                        result.steps,
                        result.accepted,
                        100.0 * result.accepted as f64 / result.steps.max(1) as f64,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest design (energy = {:?}):\n  {}\n",
                        result.best_energy,
                        p.describe(&result.best)
                    );
                    println!("top {} distinct candidates:", top.min(result.topk.len()));
                    for (i, (state, e)) in result.topk.iter().take(top).enumerate() {
                        println!("  {:2}. energy {:?}  {}", i + 1, e, p.describe(state));
                    }
                    println!(
                        "\nlegend: energy = [mono-blockers, K-hazards, ctor-count, style-pref]"
                    );
                    println!(
                        "        style-pref: 0 = recursive, 1 = data (recursive preferred when tied)"
                    );
                },
                "buchholz-rank" => {
                    use echidna::learning::buchholz_rank::{
                        render_rank_mono_skeleton, BuchholzRankProblem,
                    };
                    let p = BuchholzRankProblem::with_baseline_corpus();
                    let result = anneal(&p, &cfg);
                    formatter.info(&format!(
                        "annealer: {} steps, {} accepted ({:.1}%); best energy {:?}",
                        result.steps,
                        result.accepted,
                        100.0 * result.accepted as f64 / result.steps.max(1) as f64,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest rank shape (energy = {:?}):\n{}\n",
                        result.best_energy,
                        p.describe(&result.best)
                    );
                    println!("top {} distinct candidates:", top.min(result.topk.len()));
                    for (i, (state, e)) in result.topk.iter().take(top).enumerate() {
                        println!("  {:2}. energy {:?}", i + 1, e);
                        for line in p.describe(state).lines() {
                            println!("       {}", line);
                        }
                    }
                    println!(
                        "\nlegend: energy = [downstream-blockers, capability-gaps, structural-cost]"
                    );
                    println!(
                        "        downstream-blockers: # of new lemmas to prove (Phase-1.3 / 2.2)"
                    );
                    println!(
                        "        capability-gaps:     # of primitives missing from current corpus"
                    );
                    println!("\n--- Agda skeleton for the recommended shape ---");
                    println!("{}", render_rank_mono_skeleton(&result.best));
                },
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown design problem '{}' (available: brouwer-leq, buchholz-rank)",
                        other
                    ))
                },
            }
        },

        DesignOp::Swarm {
            problem,
            agents,
            iterations,
            temp,
            cooling,
            seed,
            broadcast_every,
            adopt_threshold,
        } => {
            let anneal_cfg = AnnealConfig {
                max_iterations: iterations,
                initial_temp: temp,
                cooling,
                seed,
                restarts: 1, // each swarm agent is its own "restart"
            };
            let swarm_cfg = SwarmConfig {
                agents,
                anneal: anneal_cfg,
                broadcast_every,
                adopt_threshold,
            };

            match problem.as_str() {
                "brouwer-leq" => {
                    let p = Arc::new(brouwer::BrouwerLeqProblem::default());
                    let p_describe = brouwer::BrouwerLeqProblem::default();
                    let result = run_swarm(p, swarm_cfg).await;
                    formatter.info(&format!(
                        "swarm: {} agents, {} adoptions; best energy {:?}",
                        result.per_agent.len(),
                        result.adoptions,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest design (energy = {:?}):\n  {}\n",
                        result.best_energy,
                        p_describe.describe(&result.best)
                    );
                    println!("per-agent reports:");
                    for r in &result.per_agent {
                        println!(
                            "  agent {:2} (seed {:#x}): {} steps, {} accepted, {} adoptions; best {:?}",
                            r.agent_id,
                            r.seed,
                            r.steps,
                            r.accepted,
                            r.adopted_count,
                            r.local_best_energy,
                        );
                    }
                },
                "buchholz-rank" => {
                    use echidna::learning::buchholz_rank::{
                        render_rank_mono_skeleton, BuchholzRankProblem,
                    };
                    let p = Arc::new(BuchholzRankProblem::with_baseline_corpus());
                    let p_describe = BuchholzRankProblem::with_baseline_corpus();
                    let result = run_swarm(p, swarm_cfg).await;
                    formatter.info(&format!(
                        "swarm: {} agents, {} adoptions; best energy {:?}",
                        result.per_agent.len(),
                        result.adoptions,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest rank shape (energy = {:?}):\n{}\n",
                        result.best_energy,
                        p_describe.describe(&result.best)
                    );
                    println!("per-agent reports:");
                    for r in &result.per_agent {
                        println!(
                            "  agent {:2} (seed {:#x}): {} steps, {} accepted, {} adoptions; best {:?}",
                            r.agent_id,
                            r.seed,
                            r.steps,
                            r.accepted,
                            r.adopted_count,
                            r.local_best_energy,
                        );
                    }
                    println!("\n--- Agda skeleton for the recommended shape ---");
                    println!("{}", render_rank_mono_skeleton(&result.best));
                },
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown design problem '{}' (available: brouwer-leq, buchholz-rank)",
                        other
                    ))
                },
            }
        },
    }
    Ok(())
}
