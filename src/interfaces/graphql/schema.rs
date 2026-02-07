// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL schema definitions

use async_graphql::{Context, Object, Result, SimpleObject, Enum};

/// Supported theorem provers in ECHIDNA
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProverKind {
    // Tier 1
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    CVC5,
    // Tier 2
    Metamath,
    HOLLight,
    Mizar,
    // Tier 3
    PVS,
    ACL2,
    // Tier 4
    HOL4,
    // Extended
    Idris2,
    // Tier 5
    Vampire,
    EProver,
    SPASS,
    AltErgo,
}

/// Status of a proof attempt
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProofStatus {
    Pending,
    InProgress,
    Success,
    Failed,
    Timeout,
    Error,
}

/// Proof state representation
#[derive(Debug, Clone, SimpleObject)]
pub struct ProofState {
    pub id: String,
    pub prover: ProverKind,
    pub goal: String,
    pub status: ProofStatus,
    pub proof_script: Vec<String>,
    pub time_elapsed: Option<f64>,
    pub error_message: Option<String>,
}

/// Tactic representation
#[derive(Debug, Clone, SimpleObject)]
pub struct Tactic {
    pub name: String,
    pub args: Vec<String>,
    pub description: Option<String>,
}

/// Prover information
#[derive(Debug, Clone, SimpleObject)]
pub struct ProverInfo {
    pub kind: ProverKind,
    pub version: String,
    pub tier: i32,
    pub complexity: i32,
    pub available: bool,
}

pub struct QueryRoot;

#[Object]
impl QueryRoot {
    /// Get all available provers
    async fn provers(&self) -> Result<Vec<ProverInfo>> {
        // TODO: Call ECHIDNA core to get actual prover list
        Ok(vec![
            ProverInfo {
                kind: ProverKind::Vampire,
                version: "4.8".to_string(),
                tier: 5,
                complexity: 2,
                available: true,
            },
            ProverInfo {
                kind: ProverKind::Lean,
                version: "4.0".to_string(),
                tier: 1,
                complexity: 3,
                available: true,
            },
        ])
    }

    /// Get proof state by ID
    async fn proof_state(&self, id: String) -> Result<Option<ProofState>> {
        // TODO: Fetch from ECHIDNA core
        Ok(None)
    }

    /// List all proof attempts
    async fn list_proofs(&self, limit: Option<i32>, status: Option<ProofStatus>) -> Result<Vec<ProofState>> {
        // TODO: Query ECHIDNA core
        Ok(vec![])
    }

    /// Get suggested tactics for a proof state
    async fn suggest_tactics(&self, proof_id: String, limit: Option<i32>) -> Result<Vec<Tactic>> {
        // TODO: Call ECHIDNA neural premise selection
        Ok(vec![])
    }

    /// Health check
    async fn health(&self) -> String {
        "OK".to_string()
    }
}

pub struct MutationRoot;

#[Object]
impl MutationRoot {
    /// Submit a new proof goal
    async fn submit_proof(&self, goal: String, prover: ProverKind) -> Result<ProofState> {
        // TODO: Submit to ECHIDNA core
        Ok(ProofState {
            id: uuid::Uuid::new_v4().to_string(),
            prover,
            goal,
            status: ProofStatus::Pending,
            proof_script: vec![],
            time_elapsed: None,
            error_message: None,
        })
    }

    /// Apply a tactic to a proof state
    async fn apply_tactic(&self, proof_id: String, tactic: String, args: Vec<String>) -> Result<ProofState> {
        // TODO: Send to ECHIDNA core
        Err("Not implemented".into())
    }

    /// Cancel a proof attempt
    async fn cancel_proof(&self, proof_id: String) -> Result<bool> {
        // TODO: Cancel in ECHIDNA core
        Ok(false)
    }
}
