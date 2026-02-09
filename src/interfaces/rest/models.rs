// SPDX-License-Identifier: PMPL-1.0-or-later
// REST API data models

use serde::{Deserialize, Serialize};
use utoipa::ToSchema;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ToSchema)]
#[serde(rename_all = "snake_case")]
pub enum ProverKind {
    Agda, Coq, Lean, Isabelle, Z3, Cvc5,
    Metamath, HolLight, Mizar,
    Pvs, Acl2, Hol4,
    Idris2, Vampire, EProver, Spass, AltErgo,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ToSchema)]
#[serde(rename_all = "snake_case")]
pub enum ProofStatus {
    Pending, InProgress, Success, Failed, Timeout, Error,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ProverInfo {
    pub kind: ProverKind,
    pub version: String,
    pub tier: u8,
    pub complexity: u8,
    pub available: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ProofRequest {
    pub goal: String,
    pub prover: ProverKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout_seconds: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ProofResponse {
    pub id: String,
    pub prover: ProverKind,
    pub goal: String,
    pub status: ProofStatus,
    pub proof_script: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_elapsed: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct TacticRequest {
    pub name: String,
    pub args: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct TacticResponse {
    pub success: bool,
    pub proof_state: ProofResponse,
}

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct Tactic {
    pub name: String,
    pub args: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub confidence: Option<f32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ListProofsQuery {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub status: Option<ProofStatus>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit: Option<usize>,
}
