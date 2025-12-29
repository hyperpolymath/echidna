// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Integration tests for agentic theorem proving

use echidna::agent::{
    AgentCore, AgentConfig, AgenticGoal, Priority,
    memory::{ProofMemory, SqliteMemory},
    planner::{Planner, RulePlanner},
    router::ProverRouter,
    explanations::ExplanationGenerator,
};
use echidna::core::{Goal, Term};
use echidna::provers::{ProverBackend, ProverKind};
use tempfile::TempDir;

/// Mock prover for testing
#[derive(Clone)]
struct MockProver {
    kind: ProverKind,
    always_succeeds: bool,
    config: echidna::provers::ProverConfig,
}

impl MockProver {
    fn new(kind: ProverKind, always_succeeds: bool) -> Self {
        MockProver {
            kind,
            always_succeeds,
            config: echidna::provers::ProverConfig::default(),
        }
    }
}

#[async_trait::async_trait]
impl ProverBackend for MockProver {
    fn kind(&self) -> ProverKind {
        self.kind
    }

    async fn version(&self) -> anyhow::Result<String> {
        Ok("MockProver 1.0".to_string())
    }

    async fn parse_file(&self, _path: std::path::PathBuf) -> anyhow::Result<echidna::core::ProofState> {
        Ok(echidna::core::ProofState {
            goals: vec![],
            context: Default::default(),
            proof_script: vec![],
            metadata: Default::default(),
        })
    }

    async fn parse_string(&self, _content: &str) -> anyhow::Result<echidna::core::ProofState> {
        Ok(echidna::core::ProofState {
            goals: vec![],
            context: Default::default(),
            proof_script: vec![],
            metadata: Default::default(),
        })
    }

    async fn apply_tactic(
        &self,
        _state: &echidna::core::ProofState,
        _tactic: &echidna::core::Tactic,
    ) -> anyhow::Result<echidna::core::TacticResult> {
        Ok(echidna::core::TacticResult::Success(echidna::core::ProofState {
            goals: vec![],
            context: Default::default(),
            proof_script: vec![],
            metadata: Default::default(),
        }))
    }

    async fn verify_proof(&self, _state: &echidna::core::ProofState) -> anyhow::Result<bool> {
        Ok(self.always_succeeds)
    }

    async fn export(&self, _state: &echidna::core::ProofState) -> anyhow::Result<String> {
        Ok("-- Mock proof export".to_string())
    }

    async fn suggest_tactics(
        &self,
        _state: &echidna::core::ProofState,
        _limit: usize,
    ) -> anyhow::Result<Vec<echidna::core::Tactic>> {
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> anyhow::Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &echidna::provers::ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: echidna::provers::ProverConfig) {
        self.config = config;
    }

    fn prove(&self, _goal: &Goal) -> anyhow::Result<echidna::core::ProofState> {
        if self.always_succeeds {
            Ok(echidna::core::ProofState {
                goals: vec![],
                context: Default::default(),
                proof_script: vec![],
                metadata: Default::default(),
            })
        } else {
            Err(anyhow::anyhow!("Mock prover failed"))
        }
    }
}

#[tokio::test]
#[ignore = "Requires API updates to SqliteMemory"]
async fn test_proof_memory_storage_and_retrieval() {
    todo!("API updates needed for SqliteMemory")
}

#[tokio::test]
#[ignore = "Requires API updates to ProverRouter"]
async fn test_prover_router_learning() {
    todo!("API updates needed for ProverRouter")
}

#[tokio::test]
#[ignore = "Requires API updates to RulePlanner"]
async fn test_goal_decomposition() {
    todo!("API updates needed for RulePlanner")
}

#[tokio::test]
#[ignore = "Requires API updates to AgentCore"]
async fn test_agent_queue_priority() {
    todo!("API updates needed for AgentCore")
}

#[test]
fn test_explanation_generation() {
    let generator = ExplanationGenerator::new();

    let goal = AgenticGoal {
        goal: Goal {
            id: "test_explain".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 2,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["algebra".to_string()],
        parent: None,
    };

    // Test failure explanation
    let failure_exp = generator.explain_failure(&goal, "timeout", Some(ProverKind::Coq));
    assert!(failure_exp.title.contains("Failed"));
    assert!(!failure_exp.suggestions.is_empty());

    // Test success explanation
    let success_exp = generator.explain_success(&goal, ProverKind::Lean, 150);
    assert!(success_exp.title.contains("Succeeded"));
    assert_eq!(success_exp.details.get("Time"), Some(&"150ms".to_string()));

    // Test prover selection explanation
    let selection_exp = generator.explain_prover_selection(
        &goal,
        ProverKind::Z3,
        0.92,
        "High aspect similarity"
    );
    assert!(selection_exp.title.contains("Selection"));
    assert!(selection_exp.message.contains("0.92"));

    // Test decomposition explanation
    let sub_goals = vec![
        AgenticGoal {
            goal: Goal {
                id: "sub1".to_string(),
                target: Term::Var("X".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![],
            parent: Some(goal.goal.id.clone()),
        },
    ];

    let decomp_exp = generator.explain_decomposition(&goal, &sub_goals, "implication");
    assert!(decomp_exp.title.contains("Decomposition"));
    assert_eq!(decomp_exp.details.get("Number of Sub-goals"), Some(&"1".to_string()));
}

#[tokio::test]
#[ignore = "Requires API updates to SqliteMemory"]
async fn test_memory_failure_tracking() {
    todo!("API updates needed for SqliteMemory")
}

#[tokio::test]
#[ignore = "Requires API updates to ProverRouter"]
async fn test_router_aspect_scoring() {
    todo!("API updates needed for ProverRouter")
}

#[test]
fn test_priority_ordering() {
    assert!(Priority::Critical > Priority::High);
    assert!(Priority::High > Priority::Medium);
    assert!(Priority::Medium > Priority::Low);
}
