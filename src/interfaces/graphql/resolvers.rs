// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL resolvers - wired to ECHIDNA core

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use echidna::core::{ProofState as CoreProofState, Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};

// Import FFI wrapper
use crate::ffi_wrapper;;

/// Wrapper for FFI-based prover backend
struct FfiProverBackend {
    handle: i32,
}

impl FfiProverBackend {
    pub fn new(handle: i32) -> Self {
        FfiProverBackend { handle }
    }
}

#[async_trait::async_trait]
impl ProverBackend for FfiProverBackend {
    async fn parse_file(&self, path: std::path::PathBuf) -> anyhow::Result<CoreProofState> {
        let content = std::fs::read_to_string(&path)?;
        ffi_wrapper::parse_string(self.handle, &content)?;
        Ok(CoreProofState::new(content))
    }

    async fn parse_string(&self, content: &str) -> anyhow::Result<CoreProofState> {
        ffi_wrapper::parse_string(self.handle, content)?;
        Ok(CoreProofState::new(content.to_string()))
    }

    async fn verify_proof(&self, state: &CoreProofState) -> anyhow::Result<bool> {
        ffi_wrapper::verify_proof(self.handle)
    }

    async fn apply_tactic(&self, state: &CoreProofState, tactic: &CoreTactic) -> anyhow::Result<CoreTacticResult> {
        let tactic_str = format!("{:?}", tactic);
        if ffi_wrapper::apply_tactic(self.handle, &tactic_str)? {
            Ok(CoreTacticResult::Success(Box::new(state.clone())))
        } else {
            Ok(CoreTacticResult::Error("Tactic failed".to_string()))
        }
    }

    async fn suggest_tactics(&self, state: &CoreProofState, limit: usize) -> anyhow::Result<Vec<CoreTactic>> {
        let tactic_names = ffi_wrapper::suggest_tactics(self.handle, limit)?;
        let tactics = tactic_names.into_iter().map(|name| {
            CoreTactic::Custom {
                prover: "ffi".to_string(),
                command: name,
                args: vec![],
            }
        }).collect();
        Ok(tactics)
    }

    async fn export(&self, state: &CoreProofState) -> anyhow::Result<String> {
        ffi_wrapper::export_proof(self.handle)
    }

    async fn version(&self) -> anyhow::Result<String> {
        ffi_wrapper::get_version()
    }

    fn kind(&self) -> CoreProverKind {
        // This is a bit simplified - in a real implementation we'd track the kind
        CoreProverKind::Lean // Default, would need to be set during creation
    }
}

/// Helper trait to convert between GraphQL and core types
pub trait ProverKindExt {
    fn from_core(kind: CoreProverKind) -> Self;
    fn to_core(&self) -> CoreProverKind;
}

impl ProverKindExt for crate::schema::ProverKind {
    fn from_core(kind: CoreProverKind) -> Self {
        match kind {
            CoreProverKind::Agda => crate::schema::ProverKind::Agda,
            CoreProverKind::Coq => crate::schema::ProverKind::Coq,
            CoreProverKind::Lean => crate::schema::ProverKind::Lean,
            CoreProverKind::Isabelle => crate::schema::ProverKind::Isabelle,
            CoreProverKind::Z3 => crate::schema::ProverKind::Z3,
            CoreProverKind::CVC5 => crate::schema::ProverKind::CVC5,
            CoreProverKind::Metamath => crate::schema::ProverKind::Metamath,
            CoreProverKind::HOLLight => crate::schema::ProverKind::HOLLight,
            CoreProverKind::Mizar => crate::schema::ProverKind::Mizar,
            CoreProverKind::PVS => crate::schema::ProverKind::PVS,
            CoreProverKind::ACL2 => crate::schema::ProverKind::ACL2,
            CoreProverKind::HOL4 => crate::schema::ProverKind::HOL4,
            CoreProverKind::Idris2 => crate::schema::ProverKind::Idris2,
            CoreProverKind::Vampire => crate::schema::ProverKind::Vampire,
            CoreProverKind::EProver => crate::schema::ProverKind::EProver,
            CoreProverKind::SPASS => crate::schema::ProverKind::SPASS,
            CoreProverKind::AltErgo => crate::schema::ProverKind::AltErgo,
            CoreProverKind::FStar => crate::schema::ProverKind::FStar,
            CoreProverKind::Dafny => crate::schema::ProverKind::Dafny,
            CoreProverKind::Why3 => crate::schema::ProverKind::Why3,
            CoreProverKind::TLAPS => crate::schema::ProverKind::TLAPS,
            CoreProverKind::Twelf => crate::schema::ProverKind::Twelf,
            CoreProverKind::Nuprl => crate::schema::ProverKind::Nuprl,
            CoreProverKind::Minlog => crate::schema::ProverKind::Minlog,
            CoreProverKind::Imandra => crate::schema::ProverKind::Imandra,
            CoreProverKind::GLPK => crate::schema::ProverKind::GLPK,
            CoreProverKind::SCIP => crate::schema::ProverKind::SCIP,
            CoreProverKind::MiniZinc => crate::schema::ProverKind::MiniZinc,
            CoreProverKind::Chuffed => crate::schema::ProverKind::Chuffed,
            CoreProverKind::ORTools => crate::schema::ProverKind::ORTools,
        }
    }

    fn to_core(&self) -> CoreProverKind {
        match self {
            crate::schema::ProverKind::Agda => CoreProverKind::Agda,
            crate::schema::ProverKind::Coq => CoreProverKind::Coq,
            crate::schema::ProverKind::Lean => CoreProverKind::Lean,
            crate::schema::ProverKind::Isabelle => CoreProverKind::Isabelle,
            crate::schema::ProverKind::Z3 => CoreProverKind::Z3,
            crate::schema::ProverKind::CVC5 => CoreProverKind::CVC5,
            crate::schema::ProverKind::Metamath => CoreProverKind::Metamath,
            crate::schema::ProverKind::HOLLight => CoreProverKind::HOLLight,
            crate::schema::ProverKind::Mizar => CoreProverKind::Mizar,
            crate::schema::ProverKind::PVS => CoreProverKind::PVS,
            crate::schema::ProverKind::ACL2 => CoreProverKind::ACL2,
            crate::schema::ProverKind::HOL4 => CoreProverKind::HOL4,
            crate::schema::ProverKind::Idris2 => CoreProverKind::Idris2,
            crate::schema::ProverKind::Vampire => CoreProverKind::Vampire,
            crate::schema::ProverKind::EProver => CoreProverKind::EProver,
            crate::schema::ProverKind::SPASS => CoreProverKind::SPASS,
            crate::schema::ProverKind::AltErgo => CoreProverKind::AltErgo,
            crate::schema::ProverKind::FStar => CoreProverKind::FStar,
            crate::schema::ProverKind::Dafny => CoreProverKind::Dafny,
            crate::schema::ProverKind::Why3 => CoreProverKind::Why3,
            crate::schema::ProverKind::TLAPS => CoreProverKind::TLAPS,
            crate::schema::ProverKind::Twelf => CoreProverKind::Twelf,
            crate::schema::ProverKind::Nuprl => CoreProverKind::Nuprl,
            crate::schema::ProverKind::Minlog => CoreProverKind::Minlog,
            crate::schema::ProverKind::Imandra => CoreProverKind::Imandra,
            crate::schema::ProverKind::GLPK => CoreProverKind::GLPK,
            crate::schema::ProverKind::SCIP => CoreProverKind::SCIP,
            crate::schema::ProverKind::MiniZinc => CoreProverKind::MiniZinc,
            crate::schema::ProverKind::Chuffed => CoreProverKind::Chuffed,
            crate::schema::ProverKind::ORTools => CoreProverKind::ORTools,
        }
    }
}

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
    pub ffi_initialized: bool,
}

impl EchidnaContext {
    pub fn new() -> Self {
        let ml_client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(10))
            .build()
            .expect("Failed to create HTTP client");

        // Initialize FFI layer
        let ffi_initialized = ffi_wrapper::init_ffi().is_ok();
        if ffi_initialized {
            tracing::info!("FFI layer initialized successfully");
        } else {
            tracing::warn!("FFI layer initialization failed, falling back to direct Rust calls");
        }

        EchidnaContext {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            ml_client,
            ml_api_url: "http://127.0.0.1:8090".to_string(),
            ffi_initialized,
        }
    }

    pub async fn create_session(&self, goal: &str, kind: CoreProverKind) -> anyhow::Result<String> {
        let proof_id = uuid::Uuid::new_v4().to_string();

        if self.ffi_initialized {
            // Use FFI path
            let ffi_kind = ffi_wrapper::prover_kind_to_ffi(&crate::schema::ProverKind::from_core(kind));
            match ffi_wrapper::create_prover(ffi_kind) {
                Ok(handle) => {
                    // Parse via FFI
                    if ffi_wrapper::parse_string(handle, goal).is_ok() {
                        let session = ProofSession {
                            id: proof_id.clone(),
                            prover_kind: kind,
                            prover: Box::new(FfiProverBackend::new(handle)),
                            state: Some(CoreProofState::new(goal.to_string())),
                            goal: goal.to_string(),
                            status: SessionStatus::InProgress,
                            history: vec![],
                            start_time: std::time::Instant::now(),
                        };

                        self.sessions
                            .write()
                            .await
                            .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

                        return Ok(proof_id);
                    }
                }
                Err(e) => {
                    tracing::warn!("FFI path failed, falling back to direct: {}", e);
                }
            }
        }

        // Fallback to direct Rust path
        let config = ProverConfig::default();
        let prover = ProverFactory::create(kind, config)?;

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
