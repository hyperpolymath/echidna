// SPDX-License-Identifier: PMPL-1.0-or-later
// REST API data models

use serde::{Deserialize, Serialize};
use utoipa::ToSchema;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ToSchema)]
#[serde(rename_all = "snake_case")]
pub enum ProverKind {
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    Cvc5,
    Metamath,
    HolLight,
    Mizar,
    Pvs,
    Acl2,
    Hol4,
    Idris2,
    Vampire,
    EProver,
    Spass,
    AltErgo,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ToSchema)]
#[serde(rename_all = "snake_case")]
pub enum ProofStatus {
    Pending,
    InProgress,
    Success,
    Failed,
    Timeout,
    Error,
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

/// Cross-prover proof-exchange format. Selects which exporter/importer
/// the `/api/v1/proofs/:id/export` and `/api/v1/exchange/import`
/// endpoints route through.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ToSchema)]
#[serde(rename_all = "snake_case")]
pub enum ExchangeFormat {
    /// OpenTheory — HOL-family cross-checking (HOL4 / HOL Light /
    /// Isabelle-HOL). Article shape lives in
    /// `echidna::exchange::opentheory::OpenTheoryArticle`.
    OpenTheory,
    /// Dedukti / Lambdapi — universal λΠ-calculus-modulo format. Module
    /// shape lives in `echidna::exchange::dedukti::DeduktiModule`.
    Dedukti,
}

/// Query string for `GET /api/v1/proofs/:id/export?format=...`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportQuery {
    pub format: ExchangeFormat,
}

/// Body of an export response. `content` carries the exported article /
/// module as a structured JSON value — clients deserialize it into the
/// concrete format type when they need typed access.
#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ExportResponse {
    pub format: ExchangeFormat,
    /// Exported article / module, serde-serialized from the echidna
    /// exchange module type. Untyped in the wire envelope so this
    /// schema stays stable if the exporter's internal struct grows.
    pub content: serde_json::Value,
}

/// Body of `POST /api/v1/exchange/import`. `content` is a JSON-serialized
/// `OpenTheoryArticle` or `DeduktiModule` — the format field selects the
/// importer to dispatch to.
#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ImportRequest {
    pub format: ExchangeFormat,
    pub content: serde_json::Value,
}

/// Body of an import response. Echidna imports the article / module and
/// returns the resulting `ProofState` as a JSON value (round-trip tests
/// compare this against an independently-derived reference).
#[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
pub struct ImportResponse {
    pub proof_state: serde_json::Value,
}
