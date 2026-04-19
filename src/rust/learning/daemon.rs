// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Continuous self-learning daemon.
//!
//! Long-lived tokio task that closes the expert-iteration loop:
//!
//!   1. Pick the next variant via `Curriculum`.
//!   2. Search for a proof via `mcts::Search`.
//!   3. POST the outcome (proved / failed / timeout + script) to
//!      VeriSimDB's `/api/v1/proof_attempts` endpoint.
//!   4. Emit fresh variants into the candidate pool (only from
//!      proofs that succeeded — failures don't graduate).
//!   5. Every `retrain_interval` attempts, call the Julia ML server's
//!      `/reload` endpoint (triggered by
//!      `scripts/retrain_from_verisim.jl` running on a separate
//!      schedule) so the policy head reflects fresh data.
//!
//! The daemon does NOT train the model in-process — Julia owns that.
//! The daemon's only job is to drive the *data-generation* side of
//! the loop continuously.

#![allow(dead_code)]

use std::sync::Arc;
use std::time::Duration;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use tokio::time::sleep;

use super::curriculum::{Curriculum, CurriculumConfig};
use super::mcts::{ConstantValue, SearchConfig, TacticPolicy, ValueHead};
use super::self_play::{SelfPlayGenerator, Variant};
use crate::core::ProofState;
use crate::provers::{ProverConfig, ProverFactory, ProverKind};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DaemonConfig {
    pub verisim_url: String,
    pub prover_kind: ProverKind,
    pub search: SearchConfig,
    pub curriculum: CurriculumConfig,
    pub retrain_every_n_attempts: u64,
    pub tick_pause: Duration,
    pub max_pool_size: usize,
}

impl Default for DaemonConfig {
    fn default() -> Self {
        DaemonConfig {
            verisim_url: std::env::var("VERISIM_URL")
                .unwrap_or_else(|_| "http://localhost:8080".to_string()),
            prover_kind: ProverKind::Lean,
            search: SearchConfig::default(),
            curriculum: CurriculumConfig::default(),
            retrain_every_n_attempts: 100,
            tick_pause: Duration::from_secs(1),
            max_pool_size: 10_000,
        }
    }
}

#[derive(Debug, Serialize)]
struct AttemptRow<'a> {
    prover: &'a str,
    goal: String,
    proved: bool,
    nodes_expanded: usize,
    script: Vec<String>,
    ts: String,
    rationale: &'a str,
}

pub struct Daemon {
    cfg: DaemonConfig,
    curriculum: Curriculum,
    generator: SelfPlayGenerator,
    pool: Vec<Variant>,
    attempts: u64,
    http: reqwest::Client,
}

impl Daemon {
    pub fn new(cfg: DaemonConfig) -> Self {
        Daemon {
            curriculum: Curriculum::new(cfg.curriculum),
            generator: SelfPlayGenerator::new(),
            pool: Vec::new(),
            attempts: 0,
            http: reqwest::Client::builder()
                .timeout(Duration::from_secs(5))
                .build()
                .unwrap_or_else(|_| reqwest::Client::new()),
            cfg,
        }
    }

    /// Seed the pool with variants of a known-good proven state.
    pub fn seed(&mut self, proven: &ProofState) {
        let variants = self.generator.emit_variants(proven);
        self.push_variants(variants);
    }

    fn push_variants(&mut self, mut variants: Vec<Variant>) {
        let headroom = self.cfg.max_pool_size.saturating_sub(self.pool.len());
        variants.truncate(headroom);
        self.pool.extend(variants);
    }

    /// Drive one self-play step. Returns Some(true) on success,
    /// Some(false) on refutation, None on an exhausted pool.
    pub async fn step(
        &mut self,
        policy: Arc<dyn TacticPolicy>,
        value: Arc<dyn ValueHead>,
    ) -> Result<Option<bool>> {
        let chosen_idx = {
            let picked = self.curriculum.pick(&self.pool);
            match picked {
                Some(v) => self.pool.iter().position(|u| std::ptr::eq(u, v)),
                None => None,
            }
        };
        let chosen = match chosen_idx {
            Some(i) => self.pool.swap_remove(i),
            None => return Ok(None),
        };

        let prover_config = ProverConfig::default();
        let backend = ProverFactory::create(self.cfg.prover_kind, prover_config)
            .context("daemon: create backend")?;

        let mut search = super::mcts::Search::new(
            backend.as_ref(),
            policy,
            value,
            self.cfg.search.clone(),
        );
        let outcome = search.run(chosen.state.clone()).await?;

        self.curriculum.record_outcome(outcome.proof_found);
        self.attempts += 1;

        self.post_attempt(&chosen, &outcome)
            .await
            .unwrap_or_else(|err| {
                tracing::warn!(error = %err, "daemon: attempt POST failed — continuing");
            });

        if outcome.proof_found {
            let mut fresh = ProofState::default();
            fresh.goals = chosen.state.goals.clone();
            fresh.proof_script = outcome.best_script.clone();
            let variants = self.generator.emit_variants(&fresh);
            self.push_variants(variants);
        }

        Ok(Some(outcome.proof_found))
    }

    async fn post_attempt(
        &self,
        variant: &Variant,
        outcome: &super::mcts::SearchResult,
    ) -> Result<()> {
        let goal_str = variant
            .state
            .goals
            .first()
            .map(|g| format!("{}", g.target))
            .unwrap_or_default();
        let row = AttemptRow {
            prover: prover_tag(self.cfg.prover_kind),
            goal: goal_str,
            proved: outcome.proof_found,
            nodes_expanded: outcome.nodes_expanded,
            script: outcome
                .best_script
                .iter()
                .map(|t| format!("{:?}", t))
                .collect(),
            ts: chrono::Utc::now().to_rfc3339(),
            rationale: &variant.rationale,
        };
        let url = format!(
            "{}/api/v1/proof_attempts",
            self.cfg.verisim_url.trim_end_matches('/')
        );
        self.http
            .post(url)
            .json(&row)
            .send()
            .await
            .context("posting attempt")?
            .error_for_status()
            .context("attempt response")?;
        Ok(())
    }

    pub async fn run(
        &mut self,
        policy: Arc<dyn TacticPolicy>,
        value: Arc<dyn ValueHead>,
    ) -> Result<()> {
        loop {
            let regime = self.curriculum.regime();
            tracing::debug!(?regime, attempts = self.attempts, pool = self.pool.len(),
                           "daemon tick");
            match self.step(policy.clone(), value.clone()).await? {
                Some(_) => {}
                None => {
                    tracing::info!("daemon: pool exhausted — pausing");
                    sleep(self.cfg.tick_pause * 10).await;
                }
            }
            if self.cfg.tick_pause > Duration::ZERO {
                sleep(self.cfg.tick_pause).await;
            }
        }
    }
}

fn prover_tag(kind: ProverKind) -> &'static str {
    // Match what scripts/retrain_from_verisim.jl expects.
    match kind {
        ProverKind::Lean => "Lean",
        ProverKind::Isabelle => "Isabelle",
        ProverKind::Coq => "Coq",
        ProverKind::Agda => "Agda",
        ProverKind::Metamath => "Metamath",
        _ => "Unknown",
    }
}

/// Convenience: default value head that returns 0.5 — for cold-start
/// before a real value network is trained.
pub fn cold_start_value() -> Arc<dyn ValueHead> {
    Arc::new(ConstantValue(0.5))
}
