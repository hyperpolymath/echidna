// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: PMPL-1.0-or-later

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
async fn test_proof_memory_storage_and_retrieval() {
    let tmp = TempDir::new().unwrap();
    let memory = SqliteMemory::new(tmp.path().join("test.db"));
    memory.init().await.unwrap();

    let goal = AgenticGoal {
        goal: Goal {
            id: "mem_test".to_string(),
            target: Term::Var("P".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["logic".to_string()],
        parent: None,
    };

    let proof = echidna::core::ProofState {
        goals: vec![],
        context: Default::default(),
        proof_script: vec![],
        metadata: Default::default(),
    };

    // Store a success
    memory
        .store_success(&goal, &proof, ProverKind::Coq, 250)
        .await
        .unwrap();

    // Retrieve successes
    let successes = memory.get_successes().await.unwrap();
    assert_eq!(successes.len(), 1);
    assert_eq!(successes[0].goal_id, "mem_test");
    assert_eq!(successes[0].prover, ProverKind::Coq);
    assert_eq!(successes[0].time_ms, 250);
    assert_eq!(successes[0].aspects, vec!["logic".to_string()]);

    // Check stats
    let stats = memory.stats().await.unwrap();
    assert_eq!(stats.total_proofs, 1);
    assert_eq!(stats.total_failures, 0);
    assert!((stats.success_rate - 1.0).abs() < f64::EPSILON);
    assert!((stats.avg_proof_time_ms - 250.0).abs() < f64::EPSILON);
}

#[tokio::test]
async fn test_prover_router_learning() {
    let router = ProverRouter::new();

    let goal = AgenticGoal {
        goal: Goal {
            id: "router_test".to_string(),
            target: Term::Var("X".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["arithmetic".to_string()],
        parent: None,
    };

    // Record several Z3 successes for arithmetic
    for _ in 0..5 {
        router.record_success(&goal, ProverKind::Z3).await;
    }

    // Record Coq failures for arithmetic
    for _ in 0..5 {
        router.record_failure(&goal, ProverKind::Coq).await;
    }

    // Verify global stats reflect the history
    let stats = router.get_all_stats().await;
    let z3_stats = stats.get(&ProverKind::Z3).unwrap();
    assert_eq!(z3_stats.successes, 5);
    assert_eq!(z3_stats.failures, 0);
    assert!((z3_stats.success_rate() - 1.0).abs() < f64::EPSILON);

    let coq_stats = stats.get(&ProverKind::Coq).unwrap();
    assert_eq!(coq_stats.successes, 0);
    assert_eq!(coq_stats.failures, 5);
    assert!((coq_stats.success_rate() - 0.0).abs() < f64::EPSILON);
}

#[tokio::test]
async fn test_goal_decomposition() {
    let planner = RulePlanner::new();

    // Create an implication goal: A → B
    let impl_goal = AgenticGoal {
        goal: Goal {
            id: "impl_test".to_string(),
            target: Term::Pi {
                param: "x".to_string(),
                param_type: Box::new(Term::Var("A".to_string())),
                body: Box::new(Term::Var("B".to_string())),
            },
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["logic".to_string()],
        parent: None,
    };

    let sub_goals = planner.decompose(&impl_goal).await.unwrap();
    assert!(!sub_goals.is_empty(), "Implication should decompose into sub-goals");

    // The conclusion sub-goal should target B
    let conclusion = &sub_goals[0];
    assert_eq!(conclusion.goal.id, "impl_test_conclusion");
    assert_eq!(conclusion.parent, Some("impl_test".to_string()));

    // A non-decomposable goal should return empty
    let atomic_goal = AgenticGoal {
        goal: Goal {
            id: "atomic_test".to_string(),
            target: Term::Var("X".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Low,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec![],
        parent: None,
    };

    // Non-decomposable goals return themselves as-is (vec![goal.clone()])
    let no_sub = planner.decompose(&atomic_goal).await.unwrap();
    assert_eq!(no_sub.len(), 1, "Atomic goal returns itself unchanged");
    assert_eq!(no_sub[0].goal.id, "atomic_test");
}

#[tokio::test]
async fn test_agent_queue_priority() {
    let prover: Box<dyn ProverBackend> = Box::new(MockProver::new(ProverKind::Z3, true));
    let tmp = TempDir::new().unwrap();
    let memory = SqliteMemory::new(tmp.path().join("queue_test.db"));
    memory.init().await.unwrap();
    let planner = RulePlanner::new();
    let router = ProverRouter::new();

    let config = AgentConfig::default();
    let agent = AgentCore::new(
        Box::new(memory),
        Box::new(planner),
        router,
        vec![prover],
        config,
    );

    // Add goals with different priorities
    let make_goal = |id: &str, priority: Priority| AgenticGoal {
        goal: Goal {
            id: id.to_string(),
            target: Term::Var("X".to_string()),
            hypotheses: vec![],
        },
        priority,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec![],
        parent: None,
    };

    agent.add_goal(make_goal("low", Priority::Low)).await.unwrap();
    agent.add_goal(make_goal("high", Priority::High)).await.unwrap();
    agent.add_goal(make_goal("critical", Priority::Critical)).await.unwrap();
    agent.add_goal(make_goal("medium", Priority::Medium)).await.unwrap();

    // Critical should come first (highest priority at front)
    let first = agent.next_goal().await.expect("Should have a goal");
    assert_eq!(first.goal.id, "critical");

    let second = agent.next_goal().await.expect("Should have a goal");
    assert_eq!(second.goal.id, "high");

    let third = agent.next_goal().await.expect("Should have a goal");
    assert_eq!(third.goal.id, "medium");

    let fourth = agent.next_goal().await.expect("Should have a goal");
    assert_eq!(fourth.goal.id, "low");

    assert!(agent.next_goal().await.is_none(), "Queue should be empty");
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
async fn test_memory_failure_tracking() {
    let tmp = TempDir::new().unwrap();
    let memory = SqliteMemory::new(tmp.path().join("failure_test.db"));
    memory.init().await.unwrap();

    let goal1 = AgenticGoal {
        goal: Goal {
            id: "fail1".to_string(),
            target: Term::Var("P".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 1,
        max_attempts: 3,
        preferred_prover: Some(ProverKind::Coq),
        aspects: vec!["inductive".to_string()],
        parent: None,
    };

    let goal2 = AgenticGoal {
        goal: Goal {
            id: "fail2".to_string(),
            target: Term::Var("Q".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 1,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["arithmetic".to_string()],
        parent: None,
    };

    // Store failures
    memory.store_failure(&goal1, "timeout".to_string()).await.unwrap();
    memory.store_failure(&goal2, "unsupported tactic".to_string()).await.unwrap();

    // Verify failures stored
    let failures = memory.get_failures().await.unwrap();
    assert_eq!(failures.len(), 2);
    assert_eq!(failures[0].goal_id, "fail1");
    assert_eq!(failures[0].reason, "timeout");
    assert_eq!(failures[0].prover, Some(ProverKind::Coq));
    assert_eq!(failures[1].goal_id, "fail2");
    assert_eq!(failures[1].reason, "unsupported tactic");

    // Stats should show 0% success rate
    let stats = memory.stats().await.unwrap();
    assert_eq!(stats.total_proofs, 0);
    assert_eq!(stats.total_failures, 2);
    assert!((stats.success_rate - 0.0).abs() < f64::EPSILON);
}

#[tokio::test]
async fn test_router_aspect_scoring() {
    let router = ProverRouter::new();

    // Build history: Z3 is great at arithmetic, Coq is great at inductive
    let arith_goal = AgenticGoal {
        goal: Goal {
            id: "arith".to_string(),
            target: Term::Var("N".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["arithmetic".to_string()],
        parent: None,
    };

    let inductive_goal = AgenticGoal {
        goal: Goal {
            id: "induct".to_string(),
            target: Term::Var("P".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["inductive".to_string()],
        parent: None,
    };

    // Z3 succeeds on arithmetic
    for _ in 0..10 {
        router.record_success(&arith_goal, ProverKind::Z3).await;
    }

    // Coq succeeds on inductive
    for _ in 0..10 {
        router.record_success(&inductive_goal, ProverKind::Coq).await;
    }

    // Z3 fails on inductive
    for _ in 0..10 {
        router.record_failure(&inductive_goal, ProverKind::Z3).await;
    }

    // Verify aspect-specific routing works
    let all_stats = router.get_all_stats().await;

    // Z3 global: 10 successes (arithmetic) + 10 failures (inductive) = 20 attempts
    let z3 = all_stats.get(&ProverKind::Z3).unwrap();
    assert_eq!(z3.successes, 10);
    assert_eq!(z3.failures, 10);
    assert!((z3.success_rate() - 0.5).abs() < f64::EPSILON);

    // Coq global: 10 successes (inductive), 0 failures = 100% success
    let coq = all_stats.get(&ProverKind::Coq).unwrap();
    assert_eq!(coq.successes, 10);
    assert_eq!(coq.failures, 0);
    assert!((coq.success_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_priority_ordering() {
    assert!(Priority::Critical > Priority::High);
    assert!(Priority::High > Priority::Medium);
    assert!(Priority::Medium > Priority::Low);
}
