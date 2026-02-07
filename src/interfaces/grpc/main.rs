// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA gRPC Server

use tonic::{transport::Server, Request, Response, Status};
use echidna::v1::proof_service_server::{ProofService, ProofServiceServer};
use echidna::v1::*;

pub mod echidna {
    pub mod v1 {
        tonic::include_proto!("echidna.v1");
    }
}

#[derive(Debug, Default)]
pub struct ProofServiceImpl {}

#[tonic::async_trait]
impl ProofService for ProofServiceImpl {
    async fn submit_proof(
        &self,
        request: Request<SubmitProofRequest>,
    ) -> Result<Response<ProofResponse>, Status> {
        let req = request.into_inner();

        // TODO: Forward to ECHIDNA core
        let response = ProofResponse {
            proof_id: uuid::Uuid::new_v4().to_string(),
            prover: req.prover as i32,
            goal: req.goal,
            status: ProofStatus::Pending as i32,
            proof_script: vec![],
            time_elapsed: None,
            error_message: None,
        };

        Ok(Response::new(response))
    }

    async fn get_proof_status(
        &self,
        request: Request<GetProofStatusRequest>,
    ) -> Result<Response<ProofResponse>, Status> {
        // TODO: Query ECHIDNA core
        Err(Status::unimplemented("Not implemented"))
    }

    type StreamProofStream = tokio_stream::wrappers::ReceiverStream<Result<ProofUpdate, Status>>;

    async fn stream_proof(
        &self,
        request: Request<StreamProofRequest>,
    ) -> Result<Response<Self::StreamProofStream>, Status> {
        let (tx, rx) = tokio::sync::mpsc::channel(4);

        // TODO: Stream from ECHIDNA core
        tokio::spawn(async move {
            // Placeholder stream
        });

        Ok(Response::new(tokio_stream::wrappers::ReceiverStream::new(rx)))
    }

    async fn apply_tactic(
        &self,
        request: Request<ApplyTacticRequest>,
    ) -> Result<Response<TacticResponse>, Status> {
        // TODO: Forward to ECHIDNA core
        Err(Status::unimplemented("Not implemented"))
    }

    async fn cancel_proof(
        &self,
        request: Request<CancelProofRequest>,
    ) -> Result<Response<CancelProofResponse>, Status> {
        // TODO: Cancel in ECHIDNA core
        Ok(Response::new(CancelProofResponse { success: false }))
    }

    async fn list_provers(
        &self,
        request: Request<ListProversRequest>,
    ) -> Result<Response<ListProversResponse>, Status> {
        // TODO: Query ECHIDNA core
        let provers = vec![
            ProverInfo {
                kind: ProverKind::Vampire as i32,
                version: "4.8".to_string(),
                tier: 5,
                complexity: 2,
                available: true,
            },
        ];

        Ok(Response::new(ListProversResponse { provers }))
    }

    async fn suggest_tactics(
        &self,
        request: Request<SuggestTacticsRequest>,
    ) -> Result<Response<SuggestTacticsResponse>, Status> {
        // TODO: Call ECHIDNA neural premise selection
        Ok(Response::new(SuggestTacticsResponse { tactics: vec![] }))
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
