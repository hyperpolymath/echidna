// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA gRPC Server - wired to core

use tonic::{transport::Server, Request, Response, Status};
use echidna_proto::v1::proof_service_server::{ProofService, ProofServiceServer};
use echidna_proto::v1::*;
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};

pub mod echidna_proto {
    pub mod v1 {
        tonic::include_proto!("echidna.v1");
    }
}

struct ProofSession {
    prover_kind: CoreProverKind,
    prover: Box<dyn ProverBackend>,
    state: Option<echidna::core::ProofState>,
    goal: String,
    status: i32,
    history: Vec<String>,
    start_time: std::time::Instant,
}

#[derive(Debug)]
pub struct ProofServiceImpl {
    sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
}

impl Default for ProofServiceImpl {
    fn default() -> Self {
        ProofServiceImpl {
            sessions: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

#[tonic::async_trait]
impl ProofService for ProofServiceImpl {
    async fn submit_proof(
        &self,
        request: Request<SubmitProofRequest>,
    ) -> Result<Response<ProofResponse>, Status> {
        let req = request.into_inner();

        let core_kind = proto_kind_to_core(req.prover)
            .ok_or_else(|| Status::invalid_argument("Unknown prover kind"))?;

        let mut config = ProverConfig::default();
        if let Some(timeout) = req.timeout_seconds {
            config.timeout = timeout as u64;
        }

        let prover = ProverFactory::create(core_kind, config)
            .map_err(|e| Status::internal(e.to_string()))?;

        let proof_id = uuid::Uuid::new_v4().to_string();

        let proof_state = prover
            .parse_string(&req.goal)
            .await
            .map_err(|e| Status::invalid_argument(format!("Parse error: {}", e)))?;

        let valid = prover.verify_proof(&proof_state).await.unwrap_or(false);

        let status = if valid || proof_state.goals.is_empty() {
            ProofStatus::Success as i32
        } else {
            ProofStatus::InProgress as i32
        };

        let script: Vec<String> = proof_state
            .proof_script
            .iter()
            .map(|t| format!("{:?}", t))
            .collect();

        let session = ProofSession {
            prover_kind: core_kind,
            prover,
            state: Some(proof_state),
            goal: req.goal.clone(),
            status,
            history: vec![],
            start_time: std::time::Instant::now(),
        };

        self.sessions
            .write()
            .await
            .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

        Ok(Response::new(ProofResponse {
            proof_id,
            prover: req.prover,
            goal: req.goal,
            status,
            proof_script: script,
            time_elapsed: None,
            error_message: None,
        }))
    }

    async fn get_proof_status(
        &self,
        request: Request<GetProofStatusRequest>,
    ) -> Result<Response<ProofResponse>, Status> {
        let req = request.into_inner();
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(&req.proof_id)
            .ok_or_else(|| Status::not_found("Proof not found"))?
            .clone();
        drop(sessions);

        let session = session_arc.lock().await;
        let elapsed = session.start_time.elapsed().as_secs_f64();

        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        Ok(Response::new(ProofResponse {
            proof_id: req.proof_id,
            prover: core_kind_to_proto(&session.prover_kind),
            goal: session.goal.clone(),
            status: session.status,
            proof_script: script,
            time_elapsed: Some(elapsed),
            error_message: None,
        }))
    }

    type StreamProofStream = tokio_stream::wrappers::ReceiverStream<Result<ProofUpdate, Status>>;

    async fn stream_proof(
        &self,
        request: Request<StreamProofRequest>,
    ) -> Result<Response<Self::StreamProofStream>, Status> {
        let req = request.into_inner();
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(&req.proof_id)
            .ok_or_else(|| Status::not_found("Proof not found"))?
            .clone();
        drop(sessions);

        let proof_id = req.proof_id.clone();
        let (tx, rx) = tokio::sync::mpsc::channel(16);

        tokio::spawn(async move {
            let session = session_arc.lock().await;
            let status = session.status;

            // Send initial status
            let _ = tx.send(Ok(ProofUpdate {
                proof_id: proof_id.clone(),
                status,
                message: "Proof session active".to_string(),
                progress: Some(0.0),
            })).await;

            // Send current state
            if let Some(state) = &session.state {
                let goals = state.goals.len();
                let progress = if goals == 0 { 1.0 } else { 0.5 };

                let _ = tx.send(Ok(ProofUpdate {
                    proof_id: proof_id.clone(),
                    status,
                    message: format!("{} goals remaining", goals),
                    progress: Some(progress),
                })).await;
            }

            // Send completion
            let _ = tx.send(Ok(ProofUpdate {
                proof_id,
                status,
                message: "Stream complete".to_string(),
                progress: Some(1.0),
            })).await;
        });

        Ok(Response::new(tokio_stream::wrappers::ReceiverStream::new(rx)))
    }

    async fn apply_tactic(
        &self,
        request: Request<ApplyTacticRequest>,
    ) -> Result<Response<TacticResponse>, Status> {
        let req = request.into_inner();

        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(&req.proof_id)
            .ok_or_else(|| Status::not_found("Proof not found"))?
            .clone();
        drop(sessions);

        let mut session = session_arc.lock().await;

        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| Status::failed_precondition("No proof state"))?;

        let tactic = parse_tactic(&req.tactic_name, &req.tactic_args);

        let result = session
            .prover
            .apply_tactic(proof_state, &tactic)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        let success = match &result {
            CoreTacticResult::Success(new_state) => {
                let complete = new_state.is_complete();
                session.state = Some(new_state.clone());
                session.history.push(format!("{:?}", tactic));
                if complete {
                    session.status = ProofStatus::Success as i32;
                }
                true
            }
            CoreTacticResult::QED => {
                session.status = ProofStatus::Success as i32;
                if let Some(s) = session.state.as_mut() {
                    s.goals.clear();
                }
                true
            }
            CoreTacticResult::Error(_) => false,
        };

        let elapsed = session.start_time.elapsed().as_secs_f64();
        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        Ok(Response::new(TacticResponse {
            success,
            proof_state: Some(ProofResponse {
                proof_id: req.proof_id,
                prover: core_kind_to_proto(&session.prover_kind),
                goal: session.goal.clone(),
                status: session.status,
                proof_script: script,
                time_elapsed: Some(elapsed),
                error_message: match &result {
                    CoreTacticResult::Error(msg) => Some(msg.clone()),
                    _ => None,
                },
            }),
        }))
    }

    async fn cancel_proof(
        &self,
        request: Request<CancelProofRequest>,
    ) -> Result<Response<CancelProofResponse>, Status> {
        let req = request.into_inner();
        let mut sessions = self.sessions.write().await;
        let success = sessions.remove(&req.proof_id).is_some();
        Ok(Response::new(CancelProofResponse { success }))
    }

    async fn list_provers(
        &self,
        _request: Request<ListProversRequest>,
    ) -> Result<Response<ListProversResponse>, Status> {
        let provers: Vec<echidna_proto::v1::ProverInfo> = CoreProverKind::all()
            .into_iter()
            .map(|kind| echidna_proto::v1::ProverInfo {
                kind: core_kind_to_proto(&kind),
                version: format!("{:?} (ECHIDNA v0.1.0)", kind),
                tier: kind.tier() as i32,
                complexity: kind.complexity() as i32,
                available: true,
            })
            .collect();

        Ok(Response::new(ListProversResponse { provers }))
    }

    async fn suggest_tactics(
        &self,
        request: Request<SuggestTacticsRequest>,
    ) -> Result<Response<SuggestTacticsResponse>, Status> {
        let req = request.into_inner();
        let limit = req.limit.unwrap_or(5) as usize;

        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(&req.proof_id)
            .ok_or_else(|| Status::not_found("Proof not found"))?
            .clone();
        drop(sessions);

        let session = session_arc.lock().await;
        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| Status::failed_precondition("No proof state"))?;

        let core_tactics = session
            .prover
            .suggest_tactics(proof_state, limit)
            .await
            .unwrap_or_default();

        let tactics: Vec<echidna_proto::v1::Tactic> = core_tactics
            .iter()
            .map(|t| echidna_proto::v1::Tactic {
                name: format!("{:?}", t),
                args: vec![],
                description: Some("Prover-suggested tactic".to_string()),
                confidence: None,
            })
            .collect();

        Ok(Response::new(SuggestTacticsResponse { tactics }))
    }
}

// ========== Helpers ==========

fn parse_tactic(name: &str, args: &[String]) -> CoreTactic {
    match name.to_lowercase().as_str() {
        "apply" => CoreTactic::Apply(args.first().cloned().unwrap_or_default()),
        "intro" => CoreTactic::Intro(args.first().cloned()),
        "rewrite" => CoreTactic::Rewrite(args.first().cloned().unwrap_or_default()),
        "simplify" | "simp" => CoreTactic::Simplify,
        "reflexivity" | "refl" => CoreTactic::Reflexivity,
        "assumption" => CoreTactic::Assumption,
        _ => CoreTactic::Custom {
            prover: "grpc".to_string(),
            command: name.to_string(),
            args: args.to_vec(),
        },
    }
}

fn proto_kind_to_core(kind: i32) -> Option<CoreProverKind> {
    match kind {
        1 => Some(CoreProverKind::Agda),
        2 => Some(CoreProverKind::Coq),
        3 => Some(CoreProverKind::Lean),
        4 => Some(CoreProverKind::Isabelle),
        5 => Some(CoreProverKind::Z3),
        6 => Some(CoreProverKind::CVC5),
        7 => Some(CoreProverKind::Metamath),
        8 => Some(CoreProverKind::HOLLight),
        9 => Some(CoreProverKind::Mizar),
        10 => Some(CoreProverKind::PVS),
        11 => Some(CoreProverKind::ACL2),
        12 => Some(CoreProverKind::HOL4),
        13 => Some(CoreProverKind::Idris2),
        14 => Some(CoreProverKind::Vampire),
        15 => Some(CoreProverKind::EProver),
        16 => Some(CoreProverKind::SPASS),
        17 => Some(CoreProverKind::AltErgo),
        _ => None,
    }
}

fn core_kind_to_proto(kind: &CoreProverKind) -> i32 {
    match kind {
        CoreProverKind::Agda => 1,
        CoreProverKind::Coq => 2,
        CoreProverKind::Lean => 3,
        CoreProverKind::Isabelle => 4,
        CoreProverKind::Z3 => 5,
        CoreProverKind::CVC5 => 6,
        CoreProverKind::Metamath => 7,
        CoreProverKind::HOLLight => 8,
        CoreProverKind::Mizar => 9,
        CoreProverKind::PVS => 10,
        CoreProverKind::ACL2 => 11,
        CoreProverKind::HOL4 => 12,
        CoreProverKind::Idris2 => 13,
        CoreProverKind::Vampire => 14,
        CoreProverKind::EProver => 15,
        CoreProverKind::SPASS => 16,
        CoreProverKind::AltErgo => 17,
        _ => 0,
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    let addr = "[::1]:50051".parse()?;
    let proof_service = ProofServiceImpl::default();

    tracing::info!("gRPC server listening on {}", addr);

    Server::builder()
        .add_service(ProofServiceServer::new(proof_service))
        .serve(addr)
        .await?;

    Ok(())
}
