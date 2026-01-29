// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Integration layer connecting Rust backend ↔ Julia ML ↔ ReScript UI
//!
//! This module provides the glue code for end-to-end proof workflows:
//! 1. UI sends proof request → Rust API
//! 2. Rust queries Julia ML for tactic suggestions
//! 3. Rust executes tactics on prover backend
//! 4. Results stream back to UI via WebSocket

use anyhow::{Context as AnyhowContext, Result};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

use crate::core::{Goal, ProofState, Tactic, Term};
use crate::provers::{ProverBackend, ProverKind};

// ============================================================================
// Types
// ============================================================================

/// Request from UI to prove a theorem
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveRequest {
    /// Prover to use
    pub prover: ProverKind,

    /// Goal to prove
    pub goal: String,

    /// Optional context/hypotheses
    pub context: Vec<String>,

    /// Optional initial tactics
    pub tactics: Vec<String>,

    /// Enable neural suggestions
    pub use_neural: bool,
}

/// Response sent back to UI
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveResponse {
    /// Unique proof session ID
    pub session_id: String,

    /// Current proof state
    pub state: ProofStateDTO,

    /// Whether proof is complete
    pub complete: bool,

    /// Suggested next tactics (from neural ML)
    pub suggestions: Vec<TacticSuggestion>,

    /// Execution trace
    pub trace: Vec<ProofStep>,
}

/// Data Transfer Object for ProofState (UI-friendly)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStateDTO {
    pub goals: Vec<String>,
    pub hypotheses: Vec<String>,
    pub proof_script: Vec<String>,
}

/// Neural tactic suggestion
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticSuggestion {
    /// Tactic name
    pub tactic: String,

    /// Confidence score (0.0-1.0)
    pub confidence: f32,

    /// Human-readable explanation
    pub explanation: String,
}

/// Single step in proof execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStep {
    /// Step number
    pub step: usize,

    /// Tactic applied
    pub tactic: String,

    /// Resulting state (goals remaining)
    pub goals_after: usize,

    /// Time taken (ms)
    pub time_ms: u64,

    /// Success or error
    pub result: StepResult,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum StepResult {
    Success,
    Error { message: String },
}

// ============================================================================
// Integration Service
// ============================================================================

/// Main integration service coordinating all components
pub struct IntegrationService {
    /// Julia ML API endpoint
    ml_endpoint: String,

    /// Active proof sessions
    sessions: std::sync::Arc<tokio::sync::RwLock<std::collections::HashMap<String, ProofSession>>>,
}

/// Active proof session
struct ProofSession {
    prover_kind: ProverKind,
    current_state: ProofState,
    trace: Vec<ProofStep>,
    created_at: std::time::Instant,
}

impl IntegrationService {
    /// Create new integration service
    pub fn new(ml_endpoint: String) -> Self {
        IntegrationService {
            ml_endpoint,
            sessions: std::sync::Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }

    /// Handle prove request from UI
    pub async fn handle_prove_request(
        &self,
        request: ProveRequest,
        backend: Box<dyn ProverBackend>,
    ) -> Result<ProveResponse> {
        // Generate unique session ID
        let session_id = uuid::Uuid::new_v4().to_string();

        // Create initial proof state
        let goal = Goal {
            term: Term::Const(request.goal.clone()),
            name: Some("main_goal".to_string()),
        };

        let mut state = ProofState {
            goals: vec![goal],
            context: crate::core::Context {
                definitions: vec![],
                axioms: vec![],
            },
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        };

        // Apply initial tactics if provided
        let mut trace = Vec::new();
        for (step, tactic_str) in request.tactics.iter().enumerate() {
            let start = std::time::Instant::now();

            // Parse tactic
            let tactic = self.parse_tactic(tactic_str)?;

            // Apply tactic
            match backend.apply_tactic(&state, &tactic).await {
                Ok(result) => {
                    state = result.new_state;
                    trace.push(ProofStep {
                        step,
                        tactic: tactic_str.clone(),
                        goals_after: state.goals.len(),
                        time_ms: start.elapsed().as_millis() as u64,
                        result: StepResult::Success,
                    });
                }
                Err(e) => {
                    trace.push(ProofStep {
                        step,
                        tactic: tactic_str.clone(),
                        goals_after: state.goals.len(),
                        time_ms: start.elapsed().as_millis() as u64,
                        result: StepResult::Error {
                            message: e.to_string(),
                        },
                    });
                    break;
                }
            }
        }

        // Get neural suggestions if requested
        let suggestions = if request.use_neural {
            self.get_neural_suggestions(&state, request.prover).await
                .unwrap_or_else(|_| vec![])
        } else {
            vec![]
        };

        // Store session
        {
            let mut sessions = self.sessions.write().await;
            sessions.insert(
                session_id.clone(),
                ProofSession {
                    prover_kind: request.prover,
                    current_state: state.clone(),
                    trace: trace.clone(),
                    created_at: std::time::Instant::now(),
                },
            );
        }

        // Build response
        Ok(ProveResponse {
            session_id,
            state: self.state_to_dto(&state),
            complete: state.goals.is_empty(),
            suggestions,
            trace,
        })
    }

    /// Get neural tactic suggestions from Julia ML service
    async fn get_neural_suggestions(
        &self,
        state: &ProofState,
        prover: ProverKind,
    ) -> Result<Vec<TacticSuggestion>> {
        // Build request to Julia ML API
        let ml_request = serde_json::json!({
            "goal": state.goals.first().map(|g| format!("{:?}", g.term)).unwrap_or_default(),
            "context": state.context.definitions.iter()
                .map(|d| format!("{:?}", d))
                .collect::<Vec<_>>(),
            "prover": format!("{:?}", prover),
            "limit": 5,
        });

        // Call Julia ML API
        let client = reqwest::Client::new();
        let response = client
            .post(&format!("{}/suggest", self.ml_endpoint))
            .json(&ml_request)
            .send()
            .await
            .context("Failed to call ML service")?;

        let ml_response: serde_json::Value = response.json().await
            .context("Failed to parse ML response")?;

        // Parse suggestions
        let suggestions = ml_response["suggestions"]
            .as_array()
            .context("No suggestions in response")?
            .iter()
            .filter_map(|s| {
                Some(TacticSuggestion {
                    tactic: s["tactic"].as_str()?.to_string(),
                    confidence: s["confidence"].as_f64()? as f32,
                    explanation: s["explanation"].as_str()?.to_string(),
                })
            })
            .collect();

        Ok(suggestions)
    }

    /// Parse tactic string to Tactic enum
    fn parse_tactic(&self, tactic_str: &str) -> Result<Tactic> {
        // Simple parser for common tactics
        // TODO: Make this prover-specific
        if tactic_str.starts_with("apply") {
            Ok(Tactic::Apply {
                theorem: tactic_str.strip_prefix("apply ").unwrap_or("").to_string(),
            })
        } else if tactic_str == "intro" {
            Ok(Tactic::Intro { name: None })
        } else if tactic_str.starts_with("rewrite") {
            Ok(Tactic::Rewrite {
                theorem: tactic_str.strip_prefix("rewrite ").unwrap_or("").to_string(),
            })
        } else {
            Ok(Tactic::Custom {
                name: tactic_str.to_string(),
                args: vec![],
            })
        }
    }

    /// Convert ProofState to DTO
    fn state_to_dto(&self, state: &ProofState) -> ProofStateDTO {
        ProofStateDTO {
            goals: state.goals.iter()
                .map(|g| format!("{:?}", g.term))
                .collect(),
            hypotheses: state.context.definitions.iter()
                .map(|d| format!("{:?}", d))
                .collect(),
            proof_script: state.proof_script.iter()
                .map(|t| format!("{:?}", t))
                .collect(),
        }
    }

    /// Apply tactic to existing session
    pub async fn apply_tactic_to_session(
        &self,
        session_id: &str,
        tactic: String,
        backend: Box<dyn ProverBackend>,
    ) -> Result<ProveResponse> {
        // Get session
        let mut sessions = self.sessions.write().await;
        let session = sessions.get_mut(session_id)
            .context("Session not found")?;

        // Parse and apply tactic
        let tactic_obj = self.parse_tactic(&tactic)?;
        let start = std::time::Instant::now();

        match backend.apply_tactic(&session.current_state, &tactic_obj).await {
            Ok(result) => {
                // Update session state
                session.current_state = result.new_state.clone();
                session.trace.push(ProofStep {
                    step: session.trace.len(),
                    tactic: tactic.clone(),
                    goals_after: result.new_state.goals.len(),
                    time_ms: start.elapsed().as_millis() as u64,
                    result: StepResult::Success,
                });

                // Get new suggestions
                let suggestions = self.get_neural_suggestions(&result.new_state, session.prover_kind).await
                    .unwrap_or_else(|_| vec![]);

                Ok(ProveResponse {
                    session_id: session_id.to_string(),
                    state: self.state_to_dto(&result.new_state),
                    complete: result.new_state.goals.is_empty(),
                    suggestions,
                    trace: session.trace.clone(),
                })
            }
            Err(e) => {
                session.trace.push(ProofStep {
                    step: session.trace.len(),
                    tactic: tactic.clone(),
                    goals_after: session.current_state.goals.len(),
                    time_ms: start.elapsed().as_millis() as u64,
                    result: StepResult::Error {
                        message: e.to_string(),
                    },
                });

                Err(e).context("Tactic application failed")
            }
        }
    }

    /// Get session status
    pub async fn get_session(&self, session_id: &str) -> Result<ProveResponse> {
        let sessions = self.sessions.read().await;
        let session = sessions.get(session_id)
            .context("Session not found")?;

        Ok(ProveResponse {
            session_id: session_id.to_string(),
            state: self.state_to_dto(&session.current_state),
            complete: session.current_state.goals.is_empty(),
            suggestions: vec![],
            trace: session.trace.clone(),
        })
    }

    /// Clean up old sessions (older than 1 hour)
    pub async fn cleanup_old_sessions(&self) {
        let mut sessions = self.sessions.write().await;
        let now = std::time::Instant::now();

        sessions.retain(|_, session| {
            now.duration_since(session.created_at).as_secs() < 3600
        });
    }
}

// ============================================================================
// WebSocket Message Types
// ============================================================================

/// Messages from UI to backend via WebSocket
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum UIMessage {
    /// Start new proof session
    StartProof {
        prover: ProverKind,
        goal: String,
    },

    /// Apply tactic to current session
    ApplyTactic {
        session_id: String,
        tactic: String,
    },

    /// Request neural suggestions
    GetSuggestions {
        session_id: String,
        limit: usize,
    },

    /// Subscribe to proof updates
    Subscribe {
        session_id: String,
    },
}

/// Messages from backend to UI via WebSocket
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum BackendMessage {
    /// Proof state update
    StateUpdate {
        session_id: String,
        state: ProofStateDTO,
        complete: bool,
    },

    /// Neural suggestions available
    Suggestions {
        session_id: String,
        suggestions: Vec<TacticSuggestion>,
    },

    /// Tactic execution result
    TacticResult {
        session_id: String,
        step: ProofStep,
    },

    /// Error occurred
    Error {
        session_id: String,
        message: String,
    },
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Check if Julia ML service is available
pub async fn check_ml_service(endpoint: &str) -> bool {
    let client = reqwest::Client::new();
    client
        .get(&format!("{}/health", endpoint))
        .send()
        .await
        .map(|r| r.status().is_success())
        .unwrap_or(false)
}

/// Get system status for health check
#[derive(Debug, Serialize)]
pub struct SystemStatus {
    pub version: String,
    pub provers_available: Vec<String>,
    pub ml_service_connected: bool,
    pub active_sessions: usize,
    pub uptime_seconds: u64,
}

impl SystemStatus {
    pub async fn collect(
        integration: &IntegrationService,
        start_time: std::time::Instant,
    ) -> Self {
        let sessions = integration.sessions.read().await;

        SystemStatus {
            version: env!("CARGO_PKG_VERSION").to_string(),
            provers_available: ProverKind::all_core()
                .iter()
                .map(|k| format!("{:?}", k))
                .collect(),
            ml_service_connected: check_ml_service(&integration.ml_endpoint).await,
            active_sessions: sessions.len(),
            uptime_seconds: start_time.elapsed().as_secs(),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prove_request_deserialize() {
        let json = r#"{
            "prover": "Lean",
            "goal": "∀ x, x = x",
            "context": [],
            "tactics": [],
            "use_neural": true
        }"#;

        let req: ProveRequest = serde_json::from_str(json).unwrap();
        assert_eq!(req.prover, ProverKind::Lean);
        assert!(req.use_neural);
    }

    #[test]
    fn test_tactic_suggestion_serialize() {
        let suggestion = TacticSuggestion {
            tactic: "intro".to_string(),
            confidence: 0.85,
            explanation: "Introduce universal quantifier".to_string(),
        };

        let json = serde_json::to_string(&suggestion).unwrap();
        assert!(json.contains("intro"));
        assert!(json.contains("0.85"));
    }

    #[tokio::test]
    async fn test_integration_service_creation() {
        let service = IntegrationService::new("http://localhost:8000".to_string());
        assert_eq!(service.ml_endpoint, "http://localhost:8000");
    }
}
