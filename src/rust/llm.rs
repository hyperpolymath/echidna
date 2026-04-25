// SPDX-License-Identifier: PMPL-1.0-or-later
//! Frontier LLM integration for ECHIDNA
//!
//! Connects to frontier language models (Claude, GPT-4, etc.) via BoJ Server
//! for intelligent proof guidance. The LLM acts as an advisor — it suggests
//! tactics, ranks provers, decomposes goals, and generates auxiliary lemmas.
//!
//! # Trust Invariant (CRITICAL)
//!
//! The LLM **cannot** influence trust levels. Every suggestion flows through
//! the existing dispatch.rs trust pipeline. The LLM optimises *which path*
//! to take, never *what the answer is*.
//!
//! # Architecture
//!
//! ```text
//! ProofState ──► LlmAdvisor ──► BoJ REST API ──► Frontier LLM
//!                    │                                 │
//!                    │◄── structured suggestions ◄─────┘
//!                    │
//!                    ▼
//!             ProverDispatcher (trust pipeline unchanged)
//! ```
//!
//! # BoJ Integration
//!
//! BoJ Server (localhost:7700) exposes cartridges as REST endpoints.
//! The LLM advisor calls BoJ's model-router for cost-aware model selection,
//! then routes to the appropriate frontier model for tactic generation.

use crate::core::{ProofState, Tactic};
use crate::neural::ScoredTactic;
use crate::provers::ProverKind;
use anyhow::{bail, Context, Result};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use tracing::{debug, info, warn};

// ─── Configuration ──────────────────────────────────────────────────────────

/// Configuration for frontier LLM advisor
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LlmConfig {
    /// BoJ server URL (default: http://localhost:7700)
    pub boj_url: String,
    /// Request timeout in milliseconds
    pub timeout_ms: u64,
    /// Preferred model tier: "opus", "sonnet", "haiku"
    pub preferred_model: String,
    /// Whether to use model-router for cost-aware selection
    pub use_model_router: bool,
    /// Maximum tokens for LLM response
    pub max_tokens: u32,
    /// Temperature (0.0 = deterministic, 1.0 = creative)
    pub temperature: f32,
    /// Fall back to Julia neural if LLM unavailable
    pub fallback_to_neural: bool,
    /// Number of tactic suggestions to request
    pub top_k: usize,
    /// Enable ephemeral session tokens for security
    pub ephemeral_sessions: bool,
}

impl Default for LlmConfig {
    fn default() -> Self {
        Self {
            boj_url: "http://localhost:7700".to_string(),
            timeout_ms: 15000,
            preferred_model: "sonnet".to_string(),
            use_model_router: true,
            max_tokens: 2048,
            temperature: 0.2,
            fallback_to_neural: true,
            top_k: 10,
            ephemeral_sessions: true,
        }
    }
}

// ─── Request/Response Types ─────────────────────────────────────────────────

/// Structured request for tactic suggestions
#[allow(dead_code)]
#[derive(Debug, Serialize)]
struct TacticSuggestionRequest {
    /// The proof goal in human-readable form
    goal: String,
    /// Available hypotheses/context
    hypotheses: Vec<String>,
    /// Which prover system we're targeting
    prover: String,
    /// Aspect tags (e.g. "arithmetic", "inductive")
    aspects: Vec<String>,
    /// Number of suggestions wanted
    top_k: usize,
    /// Proof history (previous attempts and their outcomes)
    history: Vec<ProofAttemptSummary>,
}

/// Summary of a previous proof attempt (for learning)
#[derive(Debug, Serialize)]
struct ProofAttemptSummary {
    prover: String,
    tactic: String,
    succeeded: bool,
    time_ms: u64,
}

/// Structured response with ranked tactic suggestions
#[allow(dead_code)]
#[derive(Debug, Deserialize)]
struct TacticSuggestionResponse {
    /// Ranked tactic suggestions
    tactics: Vec<LlmScoredTactic>,
    /// Recommended provers (ranked)
    recommended_provers: Vec<ProverRecommendation>,
    /// Optional goal decomposition
    decomposition: Option<GoalDecomposition>,
    /// Auxiliary lemmas the LLM thinks would help
    auxiliary_lemmas: Vec<String>,
    /// LLM's reasoning (for logging/debugging)
    reasoning: String,
    /// Model used
    model: String,
    /// Response latency
    latency_ms: u64,
}

/// A tactic suggestion from the LLM
#[allow(dead_code)]
#[derive(Debug, Deserialize)]
struct LlmScoredTactic {
    /// Tactic text (e.g. "apply nat_add_comm", "induction n")
    tactic: String,
    /// Confidence score (0.0 to 1.0)
    confidence: f32,
    /// Which prover this tactic is for
    target_prover: String,
    /// Brief rationale
    rationale: String,
}

/// Prover recommendation from the LLM
#[derive(Debug, Deserialize)]
pub struct ProverRecommendation {
    /// Prover to try
    pub prover: String,
    /// Confidence that this prover will succeed
    pub confidence: f32,
    /// Reasoning
    pub reason: String,
}

/// Goal decomposition suggestion
#[derive(Debug, Deserialize)]
pub struct GoalDecomposition {
    /// Strategy name (e.g. "split_conjunction", "induction", "case_analysis")
    pub strategy: String,
    /// Sub-goals
    pub subgoals: Vec<String>,
    /// Ordering recommendation
    pub recommended_order: Vec<usize>,
}

/// Free-form Q&A response from /api/v1/consult.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsultResponse {
    /// Markdown-formatted answer suitable for direct display.
    pub answer: String,
    /// Which model BoJ routed to (cost-aware tier vs frontier).
    pub model: Option<String>,
    /// Round-trip latency including LLM inference (milliseconds).
    pub latency_ms: u64,
}

/// Request to BoJ cartridge
#[allow(dead_code)]
#[derive(Debug, Serialize)]
struct BojCartridgeRequest {
    operation: String,
    params: serde_json::Value,
}

/// Response from BoJ cartridge
#[allow(dead_code)]
#[derive(Debug, Deserialize)]
struct BojCartridgeResponse {
    cartridge: Option<String>,
    result: Option<serde_json::Value>,
    error: Option<String>,
    latency_ms: Option<u64>,
}

/// Model router classification result
#[allow(dead_code)]
#[derive(Debug, Deserialize)]
struct ModelRouterResult {
    complexity: String,
    model: String,
    confidence: f64,
    #[serde(rename = "canDelegate")]
    can_delegate: bool,
}

// ─── LLM Advisor ────────────────────────────────────────────────────────────

/// Frontier LLM advisor for proof guidance
///
/// Connects to BoJ Server to access frontier language models.
/// All suggestions are advisory — the trust pipeline is inviolable.
pub struct LlmAdvisor {
    config: LlmConfig,
    client: Client,
    available: bool,
    /// Current ephemeral session token (rotated per proof attempt)
    #[allow(dead_code)]
    session_token: Option<String>,
    /// Proof attempt history for in-context learning
    history: Vec<ProofAttemptSummary>,
}

impl LlmAdvisor {
    /// Create a new LLM advisor with default configuration
    pub fn new() -> Self {
        Self::with_config(LlmConfig::default())
    }

    /// Create with custom configuration
    pub fn with_config(config: LlmConfig) -> Self {
        let client = Client::builder()
            .timeout(Duration::from_millis(config.timeout_ms))
            .build()
            .expect("Failed to create HTTP client for LLM advisor");

        Self {
            config,
            client,
            available: false,
            session_token: None,
            history: Vec::new(),
        }
    }

    /// Check if BoJ server is available and LLM is reachable
    pub async fn check_health(&mut self) -> Result<bool> {
        let url = format!("{}/health", self.config.boj_url);

        match self.client.get(&url).send().await {
            Ok(response) => {
                self.available = response.status().is_success();
                if self.available {
                    info!("BoJ server healthy — LLM advisor online");
                } else {
                    warn!("BoJ server returned {}", response.status());
                }
                Ok(self.available)
            },
            Err(e) => {
                debug!("BoJ server not available: {}", e);
                self.available = false;
                Ok(false)
            },
        }
    }

    /// Get tactic suggestions from frontier LLM
    ///
    /// This is the primary integration point. Given a proof state,
    /// the LLM suggests tactics, ranks provers, and optionally
    /// decomposes the goal into sub-goals.
    pub async fn suggest_tactics(&self, state: &ProofState) -> Vec<ScoredTactic> {
        if !self.available {
            debug!("LLM advisor not available, returning empty suggestions");
            return Vec::new();
        }

        match self.call_tactic_api(state).await {
            Ok(response) => {
                info!(
                    "LLM suggested {} tactics via {} in {}ms",
                    response.tactics.len(),
                    response.model,
                    response.latency_ms
                );

                response
                    .tactics
                    .into_iter()
                    .map(|t| ScoredTactic {
                        tactic: Tactic::Apply(t.tactic),
                        score: t.confidence,
                        premise_name: None,
                    })
                    .collect()
            },
            Err(e) => {
                warn!("LLM tactic suggestion failed: {}", e);
                Vec::new()
            },
        }
    }

    /// Rank provers for a given goal using LLM reasoning
    ///
    /// Returns provers ordered by likelihood of success.
    /// This feeds into the dispatch pipeline's prover selection.
    pub async fn rank_provers(
        &self,
        state: &ProofState,
        available_provers: &[ProverKind],
    ) -> Vec<(ProverKind, f32)> {
        if !self.available {
            return Vec::new();
        }

        match self.call_tactic_api(state).await {
            Ok(response) => {
                let mut ranked: Vec<(ProverKind, f32)> = Vec::new();

                for rec in &response.recommended_provers {
                    if let Some(kind) = parse_prover_kind(&rec.prover) {
                        if available_provers.contains(&kind) {
                            ranked.push((kind, rec.confidence));
                        }
                    }
                }

                // Sort by confidence descending
                ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
                ranked
            },
            Err(e) => {
                warn!("LLM prover ranking failed: {}", e);
                Vec::new()
            },
        }
    }

    /// Suggest goal decomposition
    pub async fn suggest_decomposition(&self, state: &ProofState) -> Option<GoalDecomposition> {
        if !self.available {
            return None;
        }

        match self.call_tactic_api(state).await {
            Ok(response) => response.decomposition,
            Err(e) => {
                warn!("LLM decomposition failed: {}", e);
                None
            },
        }
    }

    /// Record a proof attempt for in-context learning
    pub fn record_attempt(
        &mut self,
        prover: ProverKind,
        tactic: &str,
        succeeded: bool,
        time_ms: u64,
    ) {
        self.history.push(ProofAttemptSummary {
            prover: format!("{:?}", prover),
            tactic: tactic.to_string(),
            succeeded,
            time_ms,
        });

        // Keep history bounded (last 50 attempts)
        if self.history.len() > 50 {
            self.history.drain(0..self.history.len() - 50);
        }
    }

    /// Get LLM-optimised dispatch configuration
    ///
    /// The LLM analyses the proof and suggests optimal dispatch parameters.
    /// The trust pipeline itself is unchanged — only the routing is optimised.
    pub async fn optimise_dispatch(&self, state: &ProofState) -> Option<DispatchOptimisation> {
        if !self.available {
            return None;
        }

        match self.call_tactic_api(state).await {
            Ok(response) => {
                // Build optimisation from LLM response
                let primary = response
                    .recommended_provers
                    .first()
                    .and_then(|r| parse_prover_kind(&r.prover));

                let cross_checkers: Vec<ProverKind> = response
                    .recommended_provers
                    .iter()
                    .skip(1)
                    .take(2)
                    .filter_map(|r| parse_prover_kind(&r.prover))
                    .collect();

                Some(DispatchOptimisation {
                    primary_prover: primary,
                    cross_check_provers: cross_checkers,
                    suggested_timeout: None,
                    reasoning: response.reasoning,
                })
            },
            Err(_) => None,
        }
    }

    // ── Private API call methods ────────────────────────────────────────────

    /// Build the LLM prompt and call BoJ
    async fn call_tactic_api(&self, state: &ProofState) -> Result<TacticSuggestionResponse> {
        let start = Instant::now();

        // Format the proof state as a structured prompt
        let goal_str = state
            .goals
            .first()
            .map(|g| format!("{:?}", g.target))
            .unwrap_or_else(|| "no goal".to_string());

        let hypotheses: Vec<String> = state
            .context
            .variables
            .iter()
            .map(|v| format!("{}: {:?}", v.name, v.ty))
            .chain(
                state
                    .context
                    .theorems
                    .iter()
                    .map(|t| format!("{}: {:?}", t.name, t.statement)),
            )
            .collect();

        // Build the system prompt for structured tactic generation
        let system_prompt = build_system_prompt();
        let user_prompt =
            build_user_prompt(&goal_str, &hypotheses, &self.history, self.config.top_k);

        // Call BoJ cartridge invoke endpoint
        let url = format!("{}/cartridge/echidna-llm/invoke", self.config.boj_url);

        let request_body = serde_json::json!({
            "operation": "suggest_tactics",
            "params": {
                "system": system_prompt,
                "prompt": user_prompt,
                "model": self.config.preferred_model,
                "max_tokens": self.config.max_tokens,
                "temperature": self.config.temperature,
                "response_format": "json"
            }
        });

        let response = self
            .client
            .post(&url)
            .json(&request_body)
            .send()
            .await
            .context("Failed to reach BoJ LLM endpoint")?;

        if !response.status().is_success() {
            // Try fallback: direct model router
            return self.call_via_model_router(state).await;
        }

        let boj_response: BojCartridgeResponse = response.json().await?;

        if let Some(error) = boj_response.error {
            bail!("BoJ LLM error: {}", error);
        }

        let result_json = boj_response
            .result
            .ok_or_else(|| anyhow::anyhow!("Empty BoJ response"))?;

        let mut parsed: TacticSuggestionResponse =
            serde_json::from_value(result_json).context("Failed to parse LLM tactic response")?;

        parsed.latency_ms = start.elapsed().as_millis() as u64;

        Ok(parsed)
    }

    /// Fallback: call via BoJ's model-router for cost-aware routing
    async fn call_via_model_router(&self, state: &ProofState) -> Result<TacticSuggestionResponse> {
        let goal_str = state
            .goals
            .first()
            .map(|g| format!("{:?}", g.target))
            .unwrap_or_else(|| "no goal".to_string());

        // Use model-router to classify the task complexity
        let classify_url = format!("{}/cartridge/model-router-mcp/invoke", self.config.boj_url);
        let classify_body = serde_json::json!({
            "operation": "classify_task",
            "params": {
                "task": format!("Suggest proof tactics for the goal: {}", goal_str)
            }
        });

        let _classify_response = self
            .client
            .post(&classify_url)
            .json(&classify_body)
            .send()
            .await;

        // Return empty response as fallback — the main flow handles this gracefully
        bail!("LLM model-router fallback not yet fully wired")
    }

    /// Free-form Q&A consultation. The /api/consult endpoint takes a
    /// natural-language question + optional context (recent jobs, current
    /// proof state summary) and returns a markdown-formatted answer.
    ///
    /// Routes through BoJ's cartridge invoke endpoint with operation
    /// `consult`. The cartridge can dispatch to whichever LLM is
    /// classified as "right-sized" for the question (cheap models for
    /// routine status queries, frontier models for proof-strategy
    /// reasoning) — that classification is BoJ's job, not echidna's.
    ///
    /// Returns Err when BoJ is unreachable / cartridge is unconfigured;
    /// callers should treat this as "no LLM enrichment available".
    pub async fn consult(
        &self,
        question: &str,
        context: Option<&str>,
    ) -> Result<ConsultResponse> {
        let start = Instant::now();

        if !self.available {
            bail!("LLM advisor not available — call check_health() first");
        }

        let url = format!("{}/cartridge/echidna-llm/invoke", self.config.boj_url);

        let request_body = serde_json::json!({
            "operation": "consult",
            "params": {
                "question": question,
                "context": context.unwrap_or(""),
                "model": self.config.preferred_model,
                "max_tokens": self.config.max_tokens,
                "temperature": self.config.temperature,
                "response_format": "markdown"
            }
        });

        let response = self
            .client
            .post(&url)
            .json(&request_body)
            .send()
            .await
            .context("Failed to reach BoJ LLM endpoint for consult")?;

        if !response.status().is_success() {
            bail!("BoJ consult returned {}", response.status());
        }

        let boj_response: BojCartridgeResponse = response.json().await?;

        if let Some(error) = boj_response.error {
            bail!("BoJ consult error: {}", error);
        }

        let result_json = boj_response
            .result
            .ok_or_else(|| anyhow::anyhow!("Empty BoJ consult response"))?;

        let answer = result_json
            .get("answer")
            .and_then(|v| v.as_str())
            .ok_or_else(|| anyhow::anyhow!("BoJ consult: missing 'answer' field"))?
            .to_string();
        let model = result_json
            .get("model")
            .and_then(|v| v.as_str())
            .map(String::from);

        Ok(ConsultResponse {
            answer,
            model,
            latency_ms: start.elapsed().as_millis() as u64,
        })
    }

    /// Whether the LLM advisor is available
    pub fn is_available(&self) -> bool {
        self.available
    }

    /// Get current configuration
    pub fn config(&self) -> &LlmConfig {
        &self.config
    }
}

impl Default for LlmAdvisor {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Dispatch Optimisation ──────────────────────────────────────────────────

/// LLM-suggested dispatch optimisation
///
/// Advisory only — the trust pipeline remains inviolable.
#[derive(Debug, Clone)]
pub struct DispatchOptimisation {
    /// Recommended primary prover
    pub primary_prover: Option<ProverKind>,
    /// Recommended cross-check provers
    pub cross_check_provers: Vec<ProverKind>,
    /// Suggested timeout override (seconds)
    pub suggested_timeout: Option<u64>,
    /// LLM's reasoning
    pub reasoning: String,
}

// ─── Prompt Construction ────────────────────────────────────────────────────

/// Build the system prompt for the frontier LLM
fn build_system_prompt() -> String {
    r#"You are ECHIDNA's proof advisor — a specialist in formal theorem proving across 30 prover backends.

Your role is ADVISORY ONLY. You suggest tactics and strategies. The formal provers verify everything.
Your suggestions NEVER bypass the trust pipeline. You optimise which path to take, not what the answer is.

Available provers:
- Interactive: Coq/Rocq, Lean 4, Isabelle/HOL, Agda, Idris2, F*
- SMT: Z3, CVC5, Alt-Ergo
- Auto-Active: Dafny, Why3
- First-Order: Vampire, E Prover, SPASS
- Specialised: Metamath, HOL Light, Mizar, HOL4, PVS, ACL2, TLAPS, Twelf, Nuprl, Minlog, Imandra
- Constraint: GLPK, SCIP, MiniZinc, Chuffed, OR-Tools

Respond with valid JSON matching this schema:
{
  "tactics": [{"tactic": "...", "confidence": 0.0-1.0, "target_prover": "...", "rationale": "..."}],
  "recommended_provers": [{"prover": "...", "confidence": 0.0-1.0, "reason": "..."}],
  "decomposition": null | {"strategy": "...", "subgoals": ["..."], "recommended_order": [0,1,2]},
  "auxiliary_lemmas": ["..."],
  "reasoning": "brief explanation of your strategy"
}"#
    .to_string()
}

/// Build the user prompt with proof state and history
fn build_user_prompt(
    goal: &str,
    hypotheses: &[String],
    history: &[ProofAttemptSummary],
    top_k: usize,
) -> String {
    let mut prompt = format!("Goal to prove:\n  {}\n\n", goal);

    if !hypotheses.is_empty() {
        prompt.push_str("Available hypotheses:\n");
        for h in hypotheses {
            prompt.push_str(&format!("  - {}\n", h));
        }
        prompt.push('\n');
    }

    if !history.is_empty() {
        prompt.push_str("Previous attempts on this goal:\n");
        for attempt in history.iter().rev().take(10) {
            let status = if attempt.succeeded { "OK" } else { "FAILED" };
            prompt.push_str(&format!(
                "  - {} via {} [{}] ({}ms)\n",
                attempt.tactic, attempt.prover, status, attempt.time_ms
            ));
        }
        prompt.push('\n');
    }

    prompt.push_str(&format!(
        "Suggest up to {} tactics. Rank provers by likelihood of success.\n\
         If the goal can be decomposed, suggest subgoals.\n\
         If auxiliary lemmas would help, suggest them.",
        top_k
    ));

    prompt
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Parse a prover name string into ProverKind
fn parse_prover_kind(name: &str) -> Option<ProverKind> {
    match name.to_lowercase().as_str() {
        "coq" | "rocq" => Some(ProverKind::Coq),
        "lean" | "lean4" => Some(ProverKind::Lean),
        "isabelle" | "isabelle/hol" => Some(ProverKind::Isabelle),
        "agda" => Some(ProverKind::Agda),
        "idris2" | "idris" => Some(ProverKind::Idris2),
        "fstar" | "f*" => Some(ProverKind::FStar),
        "z3" => Some(ProverKind::Z3),
        "cvc5" => Some(ProverKind::CVC5),
        "alt-ergo" | "altergo" => Some(ProverKind::AltErgo),
        "dafny" => Some(ProverKind::Dafny),
        "why3" => Some(ProverKind::Why3),
        "vampire" => Some(ProverKind::Vampire),
        "eprover" | "e" => Some(ProverKind::EProver),
        "spass" => Some(ProverKind::SPASS),
        "metamath" => Some(ProverKind::Metamath),
        "hol_light" | "hol light" | "hollight" => Some(ProverKind::HOLLight),
        "mizar" => Some(ProverKind::Mizar),
        "hol4" => Some(ProverKind::HOL4),
        "pvs" => Some(ProverKind::PVS),
        "acl2" => Some(ProverKind::ACL2),
        "tlaps" => Some(ProverKind::TLAPS),
        "twelf" => Some(ProverKind::Twelf),
        "nuprl" => Some(ProverKind::Nuprl),
        "minlog" => Some(ProverKind::Minlog),
        "imandra" => Some(ProverKind::Imandra),
        _ => None,
    }
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_llm_config_default() {
        let config = LlmConfig::default();
        assert_eq!(config.boj_url, "http://localhost:7700");
        assert_eq!(config.preferred_model, "sonnet");
        assert!(config.fallback_to_neural);
        assert_eq!(config.top_k, 10);
    }

    #[test]
    fn test_llm_advisor_creation() {
        let advisor = LlmAdvisor::new();
        assert!(!advisor.is_available());
    }

    #[test]
    fn test_parse_prover_kind() {
        assert_eq!(parse_prover_kind("Lean"), Some(ProverKind::Lean));
        assert_eq!(parse_prover_kind("lean4"), Some(ProverKind::Lean));
        assert_eq!(parse_prover_kind("coq"), Some(ProverKind::Coq));
        assert_eq!(parse_prover_kind("Z3"), Some(ProverKind::Z3));
        assert_eq!(parse_prover_kind("unknown"), None);
    }

    #[test]
    fn test_build_system_prompt() {
        let prompt = build_system_prompt();
        assert!(prompt.contains("ECHIDNA"));
        assert!(prompt.contains("ADVISORY ONLY"));
        assert!(prompt.contains("trust pipeline"));
    }

    #[test]
    fn test_build_user_prompt() {
        let prompt = build_user_prompt("forall n, n + 0 = n", &["n : nat".to_string()], &[], 5);
        assert!(prompt.contains("forall n"));
        assert!(prompt.contains("n : nat"));
        assert!(prompt.contains("5 tactics"));
    }

    #[test]
    fn test_record_attempt() {
        let mut advisor = LlmAdvisor::new();
        advisor.record_attempt(ProverKind::Lean, "induction n", true, 1500);
        assert_eq!(advisor.history.len(), 1);
        assert!(advisor.history[0].succeeded);
    }

    #[tokio::test]
    async fn test_suggest_tactics_no_connection() {
        let advisor = LlmAdvisor::new();
        let goal = crate::core::Term::Const("test".to_string());
        let state = ProofState::new(goal);
        let tactics = advisor.suggest_tactics(&state).await;
        assert!(tactics.is_empty()); // Not available, empty result
    }

    #[tokio::test]
    async fn test_rank_provers_no_connection() {
        let advisor = LlmAdvisor::new();
        let goal = crate::core::Term::Const("test".to_string());
        let state = ProofState::new(goal);
        let ranked = advisor
            .rank_provers(&state, &[ProverKind::Lean, ProverKind::Coq])
            .await;
        assert!(ranked.is_empty());
    }
}
