// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! Proof Memory - stores successful proofs and failures for learning
//!
//! Uses SQLite for structured storage and optionally LanceDB for vector similarity search.

use anyhow::Result;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use tokio::sync::RwLock;
use tracing::{debug, info};
#[cfg(feature = "verisim")]
use tracing::warn;

use super::AgenticGoal;
use crate::core::ProofState;
use crate::provers::ProverKind;

/// A cached proof entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedProof {
    /// Goal that was proved
    pub goal_id: String,

    /// The proof
    pub proof: ProofState,

    /// Prover used
    pub prover: ProverKind,

    /// Time taken (milliseconds)
    pub time_ms: u64,

    /// Timestamp
    pub timestamp: i64,

    /// Aspect tags
    pub aspects: Vec<String>,
}

/// A failed proof attempt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailedAttempt {
    /// Goal that failed
    pub goal_id: String,

    /// Prover used (if any)
    pub prover: Option<ProverKind>,

    /// Reason for failure
    pub reason: String,

    /// Timestamp
    pub timestamp: i64,

    /// Aspect tags
    pub aspects: Vec<String>,
}

/// Trait for proof memory implementations
#[async_trait]
pub trait ProofMemory: Send + Sync {
    /// Store a successful proof with elapsed time in milliseconds
    async fn store_success(
        &self,
        goal: &AgenticGoal,
        proof: &ProofState,
        prover: ProverKind,
        time_ms: u64,
    ) -> Result<()>;

    /// Store a failed attempt
    async fn store_failure(&self, goal: &AgenticGoal, reason: String) -> Result<()>;

    /// Find a similar proof in memory
    async fn find_similar(&self, goal: &AgenticGoal) -> Result<Option<CachedProof>>;

    /// Get all successful proofs
    async fn get_successes(&self) -> Result<Vec<CachedProof>>;

    /// Get all failed attempts
    async fn get_failures(&self) -> Result<Vec<FailedAttempt>>;

    /// Get statistics
    async fn stats(&self) -> Result<MemoryStats>;
}

/// Memory statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    pub total_proofs: usize,
    pub total_failures: usize,
    pub success_rate: f64,
    pub avg_proof_time_ms: f64,
}

/// SQLite-based proof memory
pub struct SqliteMemory {
    db_path: PathBuf,
    successes: RwLock<Vec<CachedProof>>,
    failures: RwLock<Vec<FailedAttempt>>,
}

impl SqliteMemory {
    /// Create a new SQLite memory
    pub fn new(db_path: PathBuf) -> Self {
        SqliteMemory {
            db_path,
            successes: RwLock::new(Vec::new()),
            failures: RwLock::new(Vec::new()),
        }
    }

    /// Initialize the database
    pub async fn init(&self) -> Result<()> {
        // Note: Full SQLite persistence is planned for v2.0.
        // Currently uses in-memory storage backed by Vec<CachedProof>/Vec<FailedAttempt>.
        // The db_path is stored for future migration to on-disk SQLite.
        info!(
            "Initialized proof memory at {:?} (in-memory mode)",
            self.db_path
        );
        Ok(())
    }
}

#[async_trait]
impl ProofMemory for SqliteMemory {
    async fn store_success(
        &self,
        goal: &AgenticGoal,
        proof: &ProofState,
        prover: ProverKind,
        time_ms: u64,
    ) -> Result<()> {
        let cached = CachedProof {
            goal_id: goal.goal.id.clone(),
            proof: proof.clone(),
            prover,
            time_ms,
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        let mut successes = self.successes.write().await;
        successes.push(cached);

        debug!("Stored successful proof for goal {}", goal.goal.id);
        Ok(())
    }

    async fn store_failure(&self, goal: &AgenticGoal, reason: String) -> Result<()> {
        let failed = FailedAttempt {
            goal_id: goal.goal.id.clone(),
            prover: goal.preferred_prover,
            reason,
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        let mut failures = self.failures.write().await;
        failures.push(failed);

        debug!("Stored failed attempt for goal {}", goal.goal.id);
        Ok(())
    }

    async fn find_similar(&self, goal: &AgenticGoal) -> Result<Option<CachedProof>> {
        let successes = self.successes.read().await;

        // Simple similarity: check if aspects overlap
        for cached in successes.iter() {
            let overlap = goal
                .aspects
                .iter()
                .filter(|a| cached.aspects.contains(a))
                .count();

            if overlap > 0 {
                debug!("Found similar proof: {} aspects overlap", overlap);
                return Ok(Some(cached.clone()));
            }
        }

        Ok(None)
    }

    async fn get_successes(&self) -> Result<Vec<CachedProof>> {
        Ok(self.successes.read().await.clone())
    }

    async fn get_failures(&self) -> Result<Vec<FailedAttempt>> {
        Ok(self.failures.read().await.clone())
    }

    async fn stats(&self) -> Result<MemoryStats> {
        let successes = self.successes.read().await;
        let failures = self.failures.read().await;

        let total_proofs = successes.len();
        let total_failures = failures.len();
        let total = total_proofs + total_failures;

        let success_rate = if total > 0 {
            total_proofs as f64 / total as f64
        } else {
            0.0
        };

        let avg_proof_time_ms = if !successes.is_empty() {
            successes.iter().map(|s| s.time_ms).sum::<u64>() as f64 / successes.len() as f64
        } else {
            0.0
        };

        Ok(MemoryStats {
            total_proofs,
            total_failures,
            success_rate,
            avg_proof_time_ms,
        })
    }
}

// ═══════════════════════════════════════════════════════════════════════
// VeriSimDB-backed proof memory (behind feature flag)
// ═══════════════════════════════════════════════════════════════════════

/// VeriSimDB-backed proof memory.
///
/// Stores proofs as octads in VeriSimDB (8-modality persistent storage)
/// while maintaining an in-memory cache for fast find_similar lookups.
/// Falls back gracefully to in-memory-only if VeriSimDB is unreachable.
///
/// Enabled with `--features verisim` in Cargo.toml.
#[cfg(feature = "verisim")]
pub struct VeriSimDBProofStore {
    /// VeriSimDB HTTP client
    client: crate::verisim_bridge::VeriSimDBClient,

    /// In-memory cache (fast lookups + fallback)
    local_successes: RwLock<Vec<CachedProof>>,
    local_failures: RwLock<Vec<FailedAttempt>>,

    /// Whether VeriSimDB is reachable (checked on init)
    connected: RwLock<bool>,
}

#[cfg(feature = "verisim")]
impl VeriSimDBProofStore {
    /// Create a new VeriSimDB proof store.
    ///
    /// # Arguments
    /// * `verisim_url` — Base URL of the VeriSimDB instance (e.g., "http://localhost:8081")
    pub fn new(verisim_url: &str) -> Self {
        VeriSimDBProofStore {
            client: crate::verisim_bridge::VeriSimDBClient::new(verisim_url),
            local_successes: RwLock::new(Vec::new()),
            local_failures: RwLock::new(Vec::new()),
            connected: RwLock::new(false),
        }
    }

    /// Fetch a goal embedding from the Julia inference service (port 8090).
    /// Returns a 512-dim f32 vector, or empty vec on failure.
    async fn fetch_goal_embedding(&self, goal: &crate::core::Goal) -> Result<Vec<f32>> {
        let julia_url = std::env::var("ECHIDNA_JULIA_URL")
            .unwrap_or_else(|_| "http://localhost:8090".to_string());

        let goal_display = format!("{}", goal.target);
        let body = serde_json::json!({
            "goal": goal_display,
            "model": "default"
        });

        let http = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(5))
            .build()?;

        match http
            .post(format!("{}/api/encode", julia_url))
            .json(&body)
            .send()
            .await
        {
            Ok(response) if response.status().is_success() => {
                let result: serde_json::Value = response.json().await?;
                if let Some(embedding) = result.get("embedding").and_then(|e| e.as_array()) {
                    let vec: Vec<f32> = embedding
                        .iter()
                        .filter_map(|v| v.as_f64().map(|f| f as f32))
                        .collect();
                    debug!(
                        "Got {}-dim embedding from Julia for goal {}",
                        vec.len(),
                        goal.id
                    );
                    return Ok(vec);
                }
                Ok(vec![])
            },
            Ok(_) => {
                debug!("Julia inference returned non-200 for goal {}", goal.id);
                Ok(vec![])
            },
            Err(e) => {
                debug!("Julia inference unreachable for goal {}: {}", goal.id, e);
                Ok(vec![])
            },
        }
    }

    /// Initialise the store and check VeriSimDB connectivity.
    pub async fn init(&self) -> Result<()> {
        let reachable = self.client.health_check().await;
        *self.connected.write().await = reachable;

        if reachable {
            info!("VeriSimDB proof store connected");
        } else {
            warn!("VeriSimDB unreachable — operating in cache-only mode");
        }

        Ok(())
    }
}

#[cfg(feature = "verisim")]
#[async_trait]
impl ProofMemory for VeriSimDBProofStore {
    async fn store_success(
        &self,
        goal: &AgenticGoal,
        proof: &ProofState,
        prover: ProverKind,
        time_ms: u64,
    ) -> Result<()> {
        let cached = CachedProof {
            goal_id: goal.goal.id.clone(),
            proof: proof.clone(),
            prover,
            time_ms,
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        // Always store locally for fast lookups
        self.local_successes.write().await.push(cached);

        // Build octad and send to VeriSimDB (best-effort)
        if *self.connected.read().await {
            use crate::verisim_bridge::{ProofOctadBuilder, ProofStatus};

            // Fetch goal embedding from Julia inference service (best-effort)
            let embedding = self
                .fetch_goal_embedding(&goal.goal)
                .await
                .unwrap_or_default();

            let octad = ProofOctadBuilder::new(&goal.goal.id, &goal.goal, prover)
                .with_proof_state(proof)
                .with_status(if proof.is_complete() {
                    ProofStatus::Complete
                } else {
                    ProofStatus::Partial
                })
                .with_aspects(goal.aspects.clone())
                .with_time_ms(time_ms)
                .with_embedding(embedding)
                .build()?;

            if let Err(e) = self.client.create_octad(&octad).await {
                warn!(
                    "Failed to store proof in VeriSimDB (continuing in-memory): {}",
                    e
                );
            } else {
                debug!("Stored proof octad {} in VeriSimDB", octad.key);
            }
        }

        debug!("Stored successful proof for goal {}", goal.goal.id);
        Ok(())
    }

    async fn store_failure(&self, goal: &AgenticGoal, reason: String) -> Result<()> {
        let failed = FailedAttempt {
            goal_id: goal.goal.id.clone(),
            prover: goal.preferred_prover,
            reason: reason.clone(),
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        self.local_failures.write().await.push(failed);

        // Store failure in VeriSimDB (best-effort)
        if *self.connected.read().await {
            use crate::verisim_bridge::{ProofOctadBuilder, ProofStatus};

            let prover = goal.preferred_prover.unwrap_or(ProverKind::Z3);
            let octad = ProofOctadBuilder::new(&goal.goal.id, &goal.goal, prover)
                .with_status(ProofStatus::Failed)
                .with_aspects(goal.aspects.clone())
                .build()?;

            if let Err(e) = self.client.create_octad(&octad).await {
                warn!("Failed to store failure in VeriSimDB: {}", e);
            }
        }

        debug!("Stored failed attempt for goal {}", goal.goal.id);
        Ok(())
    }

    async fn find_similar(&self, goal: &AgenticGoal) -> Result<Option<CachedProof>> {
        let successes = self.local_successes.read().await;

        // Check local cache first (fast path)
        for cached in successes.iter() {
            let overlap = goal
                .aspects
                .iter()
                .filter(|a| cached.aspects.contains(a))
                .count();

            if overlap > 0 {
                debug!(
                    "Found similar proof in local cache: {} aspects overlap",
                    overlap
                );
                return Ok(Some(cached.clone()));
            }
        }

        // VeriSimDB vector similarity search would go here in future
        // (requires neural embeddings in the vector modality)

        Ok(None)
    }

    async fn get_successes(&self) -> Result<Vec<CachedProof>> {
        Ok(self.local_successes.read().await.clone())
    }

    async fn get_failures(&self) -> Result<Vec<FailedAttempt>> {
        Ok(self.local_failures.read().await.clone())
    }

    async fn stats(&self) -> Result<MemoryStats> {
        let successes = self.local_successes.read().await;
        let failures = self.local_failures.read().await;

        let total_proofs = successes.len();
        let total_failures = failures.len();
        let total = total_proofs + total_failures;

        let success_rate = if total > 0 {
            total_proofs as f64 / total as f64
        } else {
            0.0
        };

        let avg_proof_time_ms = if !successes.is_empty() {
            successes.iter().map(|s| s.time_ms).sum::<u64>() as f64 / successes.len() as f64
        } else {
            0.0
        };

        Ok(MemoryStats {
            total_proofs,
            total_failures,
            success_rate,
            avg_proof_time_ms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::{AgenticGoal, Priority};
    use super::*;
    use crate::core::{Goal, Term};

    #[tokio::test]
    async fn test_memory_store_and_retrieve() {
        let memory = SqliteMemory::new(PathBuf::from(":memory:"));
        memory.init().await.unwrap();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test_goal".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec!["logic".to_string()],
            parent: None,
        };

        let proof = ProofState::new(Term::Var("A".to_string()));

        // Store success
        memory
            .store_success(&goal, &proof, ProverKind::Agda, 42)
            .await
            .unwrap();

        // Retrieve
        let successes = memory.get_successes().await.unwrap();
        assert_eq!(successes.len(), 1);
        assert_eq!(successes[0].goal_id, "test_goal");

        // Stats
        let stats = memory.stats().await.unwrap();
        assert_eq!(stats.total_proofs, 1);
        assert_eq!(stats.total_failures, 0);
        assert_eq!(stats.success_rate, 1.0);
    }
}
