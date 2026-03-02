//! Client for communicating with ECHIDNA Core

use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use super::{ProofResult, ProofStatus, ProverKind, TacticSuggestion};
use crate::config::{EchidnaApiMode, EchidnaConfig};
use crate::error::{Error, Result};
use tracing::warn;

/// Client for ECHIDNA Core GraphQL API
pub struct EchidnaClient {
    client: Client,
    endpoint: String,
    rest_endpoint: String,
    timeout: Duration,
    mode: EchidnaApiMode,
}

impl EchidnaClient {
    /// Create a new ECHIDNA client
    pub fn new(config: &EchidnaConfig) -> Self {
        let client = Client::builder()
            .timeout(Duration::from_secs(config.timeout_secs))
            .build()
            .expect("Failed to create HTTP client");

        Self {
            client,
            endpoint: config.endpoint.clone(),
            rest_endpoint: config.rest_endpoint.clone(),
            timeout: Duration::from_secs(config.timeout_secs),
            mode: config.mode,
        }
    }

    /// Verify a proof using ECHIDNA Core
    pub async fn verify_proof(&self, prover: ProverKind, content: &str) -> Result<ProofResult> {
        match self.mode {
            EchidnaApiMode::Graphql => self.verify_proof_graphql(prover, content).await,
            EchidnaApiMode::Rest => self.verify_proof_rest(prover, content).await,
            EchidnaApiMode::Auto => match self.verify_proof_graphql(prover, content).await {
                Ok(result) => Ok(result),
                Err(err) => {
                    warn!("GraphQL verify failed, falling back to REST: {}", err);
                    self.verify_proof_rest(prover, content).await
                }
            },
        }
    }

    /// Request tactic suggestions from ECHIDNA's Julia ML component
    pub async fn suggest_tactics(
        &self,
        prover: ProverKind,
        context: &str,
        goal_state: &str,
    ) -> Result<Vec<TacticSuggestion>> {
        match self.mode {
            EchidnaApiMode::Graphql => {
                self.suggest_tactics_graphql(prover, context, goal_state).await
            }
            EchidnaApiMode::Rest => self.suggest_tactics_rest(prover, context, goal_state).await,
            EchidnaApiMode::Auto => {
                match self
                    .suggest_tactics_graphql(prover, context, goal_state)
                    .await
                {
                    Ok(result) => Ok(result),
                    Err(err) => {
                        warn!("GraphQL suggest failed, falling back to REST: {}", err);
                        self.suggest_tactics_rest(prover, context, goal_state).await
                    }
                }
            }
        }
    }

    /// Check if ECHIDNA Core is available and healthy
    pub async fn health_check(&self) -> Result<bool> {
        match self.mode {
            EchidnaApiMode::Graphql => self.health_check_graphql().await,
            EchidnaApiMode::Rest => self.health_check_rest().await,
            EchidnaApiMode::Auto => match self.health_check_graphql().await {
                Ok(true) => Ok(true),
                _ => self.health_check_rest().await,
            },
        }
    }

    /// Check prover availability
    pub async fn prover_status(&self, prover: ProverKind) -> Result<ProverStatus> {
        match self.mode {
            EchidnaApiMode::Graphql => self.prover_status_graphql(prover).await,
            EchidnaApiMode::Rest => self.prover_status_rest(prover).await,
            EchidnaApiMode::Auto => match self.prover_status_graphql(prover).await {
                Ok(result) => Ok(result),
                Err(err) => {
                    warn!("GraphQL prover_status failed, falling back to REST: {}", err);
                    self.prover_status_rest(prover).await
                }
            },
        }
    }

    fn rest_url(&self, path: &str) -> String {
        let base = self.rest_endpoint.trim_end_matches('/');
        format!("{}{}", base, path)
    }

    async fn verify_proof_graphql(
        &self,
        prover: ProverKind,
        content: &str,
    ) -> Result<ProofResult> {
        let query = GraphQLRequest {
            query: r#"
                mutation VerifyProof($prover: String!, $content: String!) {
                    verifyProof(prover: $prover, content: $content) {
                        status
                        message
                        proverOutput
                        durationMs
                        artifacts
                    }
                }
            "#
            .to_string(),
            variables: serde_json::json!({
                "prover": format!("{:?}", prover).to_lowercase(),
                "content": content
            }),
        };

        let response = self
            .client
            .post(&self.endpoint)
            .json(&query)
            .timeout(self.timeout)
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Err(Error::Echidna(format!(
                "ECHIDNA returned status {}",
                response.status()
            )));
        }

        let gql_response: GraphQLResponse<VerifyProofResponse> =
            response.json().await.map_err(Error::Http)?;

        if let Some(errors) = gql_response.errors {
            return Err(Error::Echidna(
                errors.into_iter().map(|e| e.message).collect::<Vec<_>>().join(", "),
            ));
        }

        let data = gql_response
            .data
            .ok_or_else(|| Error::Echidna("No data in response".to_string()))?;

        Ok(ProofResult {
            status: parse_proof_status(&data.verify_proof.status),
            message: data.verify_proof.message,
            prover_output: data.verify_proof.prover_output,
            duration_ms: data.verify_proof.duration_ms,
            artifacts: data.verify_proof.artifacts,
        })
    }

    async fn suggest_tactics_graphql(
        &self,
        prover: ProverKind,
        context: &str,
        goal_state: &str,
    ) -> Result<Vec<TacticSuggestion>> {
        let query = GraphQLRequest {
            query: r#"
                mutation SuggestTactics($prover: String!, $context: String!, $goalState: String!) {
                    suggestTactics(prover: $prover, context: $context, goalState: $goalState) {
                        tactic
                        confidence
                        explanation
                    }
                }
            "#
            .to_string(),
            variables: serde_json::json!({
                "prover": format!("{:?}", prover).to_lowercase(),
                "context": context,
                "goalState": goal_state
            }),
        };

        let response = self
            .client
            .post(&self.endpoint)
            .json(&query)
            .timeout(self.timeout)
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Err(Error::Echidna(format!(
                "ECHIDNA returned status {}",
                response.status()
            )));
        }

        let gql_response: GraphQLResponse<SuggestTacticsResponse> =
            response.json().await.map_err(Error::Http)?;

        if let Some(errors) = gql_response.errors {
            return Err(Error::Echidna(
                errors.into_iter().map(|e| e.message).collect::<Vec<_>>().join(", "),
            ));
        }

        let data = gql_response
            .data
            .ok_or_else(|| Error::Echidna("No data in response".to_string()))?;

        Ok(data
            .suggest_tactics
            .into_iter()
            .map(|s| TacticSuggestion {
                tactic: s.tactic,
                confidence: s.confidence,
                explanation: s.explanation,
            })
            .collect())
    }

    async fn health_check_graphql(&self) -> Result<bool> {
        let query = GraphQLRequest {
            query: "{ __typename }".to_string(),
            variables: serde_json::json!({}),
        };

        let response = self
            .client
            .post(&self.endpoint)
            .json(&query)
            .timeout(Duration::from_secs(5))
            .send()
            .await;

        match response {
            Ok(r) => Ok(r.status().is_success()),
            Err(_) => Ok(false),
        }
    }

    async fn prover_status_graphql(&self, prover: ProverKind) -> Result<ProverStatus> {
        let query = GraphQLRequest {
            query: r#"
                query ProverStatus($prover: String!) {
                    proverStatus(prover: $prover) {
                        available
                        message
                    }
                }
            "#
            .to_string(),
            variables: serde_json::json!({
                "prover": format!("{:?}", prover).to_lowercase()
            }),
        };

        let response = self
            .client
            .post(&self.endpoint)
            .json(&query)
            .timeout(Duration::from_secs(10))
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Ok(ProverStatus::Unavailable);
        }

        let gql_response: GraphQLResponse<ProverStatusResponse> =
            response.json().await.map_err(Error::Http)?;

        match gql_response.data {
            Some(data) if data.prover_status.available => Ok(ProverStatus::Available),
            Some(_) => Ok(ProverStatus::Unavailable),
            None => Ok(ProverStatus::Unknown),
        }
    }

    async fn verify_proof_rest(&self, prover: ProverKind, content: &str) -> Result<ProofResult> {
        let request = RestVerifyRequest {
            prover: prover_to_echidna_name(prover),
            content: content.to_string(),
        };

        let response = self
            .client
            .post(self.rest_url("/api/verify"))
            .json(&request)
            .timeout(self.timeout)
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Err(Error::Echidna(format!(
                "ECHIDNA REST returned status {}",
                response.status()
            )));
        }

        let data: RestVerifyResponse = response.json().await.map_err(Error::Http)?;
        Ok(ProofResult {
            status: if data.valid {
                ProofStatus::Verified
            } else {
                ProofStatus::Failed
            },
            message: if data.valid {
                "Proof verified successfully".to_string()
            } else {
                "Proof verification failed".to_string()
            },
            prover_output: String::new(),
            duration_ms: 0,
            artifacts: Vec::new(),
        })
    }

    async fn suggest_tactics_rest(
        &self,
        prover: ProverKind,
        context: &str,
        goal_state: &str,
    ) -> Result<Vec<TacticSuggestion>> {
        let content = if !goal_state.trim().is_empty() {
            goal_state.to_string()
        } else {
            context.to_string()
        };

        let request = RestSuggestRequest {
            prover: prover_to_echidna_name(prover),
            content,
            limit: Some(5),
        };

        let response = self
            .client
            .post(self.rest_url("/api/suggest"))
            .json(&request)
            .timeout(self.timeout)
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Err(Error::Echidna(format!(
                "ECHIDNA REST returned status {}",
                response.status()
            )));
        }

        let data: RestSuggestResponse = response.json().await.map_err(Error::Http)?;
        Ok(data
            .suggestions
            .into_iter()
            .map(|tactic| TacticSuggestion {
                tactic,
                confidence: 0.5,
                explanation: Some("REST heuristic suggestion".to_string()),
            })
            .collect())
    }

    async fn health_check_rest(&self) -> Result<bool> {
        let response = self
            .client
            .get(self.rest_url("/api/health"))
            .timeout(Duration::from_secs(5))
            .send()
            .await;

        match response {
            Ok(resp) => Ok(resp.status().is_success()),
            Err(_) => Ok(false),
        }
    }

    async fn prover_status_rest(&self, prover: ProverKind) -> Result<ProverStatus> {
        let response = self
            .client
            .get(self.rest_url("/api/provers"))
            .timeout(Duration::from_secs(10))
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            return Ok(ProverStatus::Unknown);
        }

        let data: RestProversResponse = response.json().await.map_err(Error::Http)?;
        let target = prover_to_echidna_name(prover).to_lowercase();
        let available = data
            .provers
            .into_iter()
            .any(|info| info.name.to_lowercase() == target);

        Ok(if available {
            ProverStatus::Available
        } else {
            ProverStatus::Unavailable
        })
    }
}

// =============================================================================
// REST Types
// =============================================================================

#[derive(Serialize)]
struct RestVerifyRequest {
    prover: String,
    content: String,
}

#[derive(Deserialize)]
struct RestVerifyResponse {
    valid: bool,
    #[allow(dead_code)]
    goals_remaining: usize,
    #[allow(dead_code)]
    tactics_used: usize,
}

#[derive(Serialize)]
struct RestSuggestRequest {
    prover: String,
    content: String,
    limit: Option<usize>,
}

#[derive(Deserialize)]
struct RestSuggestResponse {
    suggestions: Vec<String>,
}

#[derive(Deserialize)]
struct RestProversResponse {
    provers: Vec<RestProverInfo>,
}

#[derive(Deserialize)]
struct RestProverInfo {
    name: String,
    #[allow(dead_code)]
    tier: u8,
    #[allow(dead_code)]
    complexity: u8,
}

fn prover_to_echidna_name(prover: ProverKind) -> String {
    match prover {
        ProverKind::Agda => "Agda",
        ProverKind::Coq => "Coq",
        ProverKind::Lean => "Lean",
        ProverKind::Isabelle => "Isabelle",
        ProverKind::Z3 => "Z3",
        ProverKind::Cvc5 => "CVC5",
        ProverKind::Metamath => "Metamath",
        ProverKind::HolLight => "HOLLight",
        ProverKind::Mizar => "Mizar",
        ProverKind::Pvs => "PVS",
        ProverKind::Acl2 => "ACL2",
        ProverKind::Hol4 => "HOL4",
    }
    .to_string()
}

// =============================================================================
// GraphQL Types
// =============================================================================

#[derive(Serialize)]
struct GraphQLRequest {
    query: String,
    variables: serde_json::Value,
}

#[derive(Deserialize)]
struct GraphQLResponse<T> {
    data: Option<T>,
    errors: Option<Vec<GraphQLError>>,
}

#[derive(Deserialize)]
struct GraphQLError {
    message: String,
}

#[derive(Deserialize)]
struct VerifyProofResponse {
    #[serde(rename = "verifyProof")]
    verify_proof: VerifyProofData,
}

#[derive(Deserialize)]
struct VerifyProofData {
    status: String,
    message: String,
    #[serde(rename = "proverOutput")]
    prover_output: String,
    #[serde(rename = "durationMs")]
    duration_ms: u64,
    artifacts: Vec<String>,
}

#[derive(Deserialize)]
struct SuggestTacticsResponse {
    #[serde(rename = "suggestTactics")]
    suggest_tactics: Vec<TacticSuggestionData>,
}

#[derive(Deserialize)]
struct TacticSuggestionData {
    tactic: String,
    confidence: f64,
    explanation: Option<String>,
}

#[derive(Deserialize)]
struct ProverStatusResponse {
    #[serde(rename = "proverStatus")]
    prover_status: ProverStatusData,
}

#[derive(Deserialize)]
struct ProverStatusData {
    available: bool,
    #[allow(dead_code)]
    message: Option<String>,
}

/// Prover availability status
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProverStatus {
    Available,
    Degraded,
    Unavailable,
    Unknown,
}

fn parse_proof_status(s: &str) -> ProofStatus {
    match s.to_uppercase().as_str() {
        "VERIFIED" | "PASS" | "SUCCESS" => ProofStatus::Verified,
        "FAILED" | "FAIL" => ProofStatus::Failed,
        "TIMEOUT" => ProofStatus::Timeout,
        "ERROR" => ProofStatus::Error,
        _ => ProofStatus::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prover_file_extensions() {
        assert!(ProverKind::Metamath.file_extensions().contains(&".mm"));
        assert!(ProverKind::Lean.file_extensions().contains(&".lean"));
        assert!(ProverKind::Coq.file_extensions().contains(&".v"));
    }

    #[test]
    fn test_prover_from_extension() {
        assert_eq!(ProverKind::from_extension(".mm"), Some(ProverKind::Metamath));
        assert_eq!(ProverKind::from_extension("lean"), Some(ProverKind::Lean));
        assert_eq!(ProverKind::from_extension(".xyz"), None);
    }

    #[test]
    fn test_prover_tier() {
        assert_eq!(ProverKind::Metamath.tier(), 2);
        assert_eq!(ProverKind::Lean.tier(), 1);
        assert_eq!(ProverKind::Hol4.tier(), 3);
    }
}
