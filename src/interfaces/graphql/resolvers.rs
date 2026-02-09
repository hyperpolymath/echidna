// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL resolvers - wired to ECHIDNA core

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use echidna::core::{ProofState as CoreProofState, Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};

/// A proof session managed by the GraphQL server
pub struct ProofSession {
    pub id: String,
    pub prover_kind: CoreProverKind,
    pub prover: Box<dyn ProverBackend>,
    pub state: Option<CoreProofState>,
    pub goal: String,
    pub status: SessionStatus,
    pub history: Vec<String>,
    pub start_time: std::time::Instant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionStatus {
    Pending,
    InProgress,
    Success,
    Failed,
}

/// Shared state for GraphQL context
pub struct EchidnaContext {
    pub sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    pub ml_client: reqwest::Client,
    pub ml_api_url: String,
}

impl EchidnaContext {
    pub fn new() -> Self {
        let ml_client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(10))
            .build()
            .expect("Failed to create HTTP client");

        EchidnaContext {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            ml_client,
            ml_api_url: "http://127.0.0.1:8090".to_string(),
        }
    }

    pub async fn create_session(&self, goal: &str, kind: CoreProverKind) -> anyhow::Result<String> {
        let config = ProverConfig::default();
        let prover = ProverFactory::create(kind, config)?;

        let proof_id = uuid::Uuid::new_v4().to_string();

        let proof_state = prover.parse_string(goal).await?;

        let session = ProofSession {
            id: proof_id.clone(),
            prover_kind: kind,
            prover,
            state: Some(proof_state),
            goal: goal.to_string(),
            status: SessionStatus::InProgress,
            history: vec![],
            start_time: std::time::Instant::now(),
        };

        self.sessions
            .write()
            .await
            .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

        Ok(proof_id)
    }

    pub async fn apply_tactic(&self, proof_id: &str, tactic: CoreTactic) -> anyhow::Result<CoreTacticResult> {
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(proof_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found: {}", proof_id))?
            .clone();
        drop(sessions);

        let mut session = session_arc.lock().await;
        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No proof state"))?;

        let result = session.prover.apply_tactic(proof_state, &tactic).await?;

        match &result {
            CoreTacticResult::Success(new_state) => {
                let complete = new_state.is_complete();
                session.state = Some(new_state.clone());
                session.history.push(format!("{:?}", tactic));
                if complete {
                    session.status = SessionStatus::Success;
                }
            }
            CoreTacticResult::QED => {
                session.status = SessionStatus::Success;
                if let Some(s) = session.state.as_mut() {
                    s.goals.clear();
                }
            }
            CoreTacticResult::Error(_) => {}
        }

        Ok(result)
    }

    pub async fn suggest_tactics(&self, proof_id: &str, limit: usize) -> anyhow::Result<Vec<CoreTactic>> {
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(proof_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found: {}", proof_id))?
            .clone();
        drop(sessions);

        let session = session_arc.lock().await;
        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No proof state"))?;

        // Try Julia ML first
        let goal_str = proof_state
            .goals
            .first()
            .map(|g| format!("{}", g.target))
            .unwrap_or_default();

        let julia_req = serde_json::json!({
            "goal": goal_str,
            "prover": format!("{:?}", session.prover_kind),
            "top_k": limit
        });

        if let Ok(resp) = self.ml_client
            .post(format!("{}/suggest", self.ml_api_url))
            .json(&julia_req)
            .send()
            .await
        {
            if resp.status().is_success() {
                if let Ok(ml_resp) = resp.json::<serde_json::Value>().await {
                    if let Some(suggestions_arr) = ml_resp["suggestions"].as_array() {
                        let tactics: Vec<CoreTactic> = suggestions_arr
                            .iter()
                            .filter_map(|s| {
                                let name = s["tactic"].as_str()?;
                                Some(CoreTactic::Custom {
                                    prover: "ml".to_string(),
                                    command: name.to_string(),
                                    args: vec![],
                                })
                            })
                            .collect();

                        if !tactics.is_empty() {
                            return Ok(tactics);
                        }
                    }
                }
            }
        }

        // Fallback to prover suggestions
        session.prover.suggest_tactics(proof_state, limit).await
    }
}
