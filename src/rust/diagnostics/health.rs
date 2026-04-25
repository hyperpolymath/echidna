// SPDX-License-Identifier: PMPL-1.0-or-later
// Health status monitoring for echidna services

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::fault_tolerance::CircuitState;

/// Overall system health status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthStatus {
    pub timestamp: DateTime<Utc>,
    pub prover_health: HashMap<String, ProverHealth>,
    pub gnn_model_health: ModelHealth,
    pub corpus_health: CorpusHealth,
    pub system_degradation: DegradationMode,
}

/// Health status of a single prover
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverHealth {
    pub name: String,
    pub is_available: bool,
    pub circuit_breaker_state: CircuitBreakerStateSnapshot,
    pub last_successful_proof: Option<DateTime<Utc>>,
    pub consecutive_failures: usize,
    pub avg_latency_ms: f64,
    pub success_rate: f64,  // 0.0 to 1.0
    pub total_invocations: u64,
    pub total_failures: u64,
}

/// Snapshot of circuit breaker state
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CircuitBreakerStateSnapshot {
    Closed,
    Open,
    HalfOpen,
}

impl From<CircuitState> for CircuitBreakerStateSnapshot {
    fn from(state: CircuitState) -> Self {
        match state {
            CircuitState::Closed => CircuitBreakerStateSnapshot::Closed,
            CircuitState::Open => CircuitBreakerStateSnapshot::Open,
            CircuitState::HalfOpen => CircuitBreakerStateSnapshot::HalfOpen,
        }
    }
}

/// Health of GNN model
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelHealth {
    pub is_loaded: bool,
    pub model_checksum: Option<String>,
    pub last_trained: Option<DateTime<Utc>>,
    pub last_validation_nDCG: f32,
    pub last_validation_MRR: f32,
    pub nDCG_meets_threshold: bool,
    pub fallback_active: bool,
    pub fallback_cache_hit_rate: f64,
    pub fallback_cache_size: usize,
    pub fallback_max_latency_ms: f64,
    pub fallback_sla_met: bool,  // Whether cosine fallback meets SLA thresholds
}

/// Health of training corpus
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorpusHealth {
    pub total_proofs: usize,
    pub total_premises: usize,
    pub last_updated: Option<DateTime<Utc>>,
    pub size_mb: f64,
    pub size_change_percent: f64,  // % change since last check
}

/// System degradation mode based on health
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DegradationMode {
    /// All systems operational
    Normal,
    /// Prefer cosine fallback ~30% of time; limit provers to top 5
    IncreasingFallback,
    /// Route all queries to cosine fallback only
    CosineOnly,
    /// Accept proofs but don't train; all fallback
    ReadOnly,
    /// Minimal mode; only accept pre-submitted proofs, no new proof search
    Minimal,
}

impl HealthStatus {
    pub fn new() -> Self {
        HealthStatus {
            timestamp: Utc::now(),
            prover_health: HashMap::new(),
            gnn_model_health: ModelHealth {
                is_loaded: false,
                model_checksum: None,
                last_trained: None,
                last_validation_nDCG: 0.0,
                last_validation_MRR: 0.0,
                nDCG_meets_threshold: false,
                fallback_active: true,
                fallback_cache_hit_rate: 0.0,
                fallback_cache_size: 0,
                fallback_max_latency_ms: 0.0,
                fallback_sla_met: true,  // Start as met until proven otherwise
            },
            corpus_health: CorpusHealth {
                total_proofs: 0,
                total_premises: 0,
                last_updated: None,
                size_mb: 0.0,
                size_change_percent: 0.0,
            },
            system_degradation: DegradationMode::Normal,
        }
    }

    /// Determine required degradation based on system health
    pub fn compute_degradation_mode(&mut self) {
        let failed_provers = self
            .prover_health
            .values()
            .filter(|p| !p.is_available)
            .count();

        let circuit_open_count = self
            .prover_health
            .values()
            .filter(|p| p.circuit_breaker_state == CircuitBreakerStateSnapshot::Open)
            .count();

        let available_provers = self.prover_health.len() - failed_provers;

        // Heuristic rules for degradation (priority order: most critical first)
        if !self.gnn_model_health.is_loaded || !self.gnn_model_health.nDCG_meets_threshold {
            // GNN model not available or not meeting quality threshold
            self.system_degradation = DegradationMode::CosineOnly;
        } else if !self.gnn_model_health.fallback_sla_met {
            // Fallback cosine similarity is violating SLA (latency or success rate)
            // Transition from Normal → IncreasingFallback, or escalate if already degraded
            if self.system_degradation == DegradationMode::Normal {
                self.system_degradation = DegradationMode::IncreasingFallback;
            } else if self.system_degradation == DegradationMode::IncreasingFallback {
                self.system_degradation = DegradationMode::CosineOnly;
            }
            // If already CosineOnly or ReadOnly, stay there (escalation only, no downgrade)
        } else if failed_provers >= 3 {
            // Too many failed provers
            self.system_degradation = DegradationMode::CosineOnly;
        } else if available_provers < 3 {
            // Critical: too few provers available
            self.system_degradation = DegradationMode::ReadOnly;
        } else if circuit_open_count >= 2 {
            // Multiple circuit breakers open
            self.system_degradation = DegradationMode::IncreasingFallback;
        } else if self.gnn_model_health.fallback_cache_hit_rate < 0.5 {
            // Fallback cache not warmed up
            self.system_degradation = DegradationMode::IncreasingFallback;
        } else {
            self.system_degradation = DegradationMode::Normal;
        }
    }

    /// Overall system health percentage
    pub fn health_percentage(&self) -> f64 {
        if self.prover_health.is_empty() {
            return 100.0;
        }

        let available_provers = self
            .prover_health
            .values()
            .filter(|p| p.is_available)
            .count();
        let availability_rate = available_provers as f64 / self.prover_health.len() as f64;

        let avg_success_rate = self
            .prover_health
            .values()
            .map(|p| p.success_rate)
            .sum::<f64>()
            / self.prover_health.len() as f64;

        let gnn_health = if self.gnn_model_health.is_loaded {
            self.gnn_model_health.last_validation_nDCG as f64 / 1.0
        } else {
            0.5  // Fallback is always available
        };

        (availability_rate * 0.4 + avg_success_rate * 0.4 + gnn_health * 0.2) * 100.0
    }

    /// Check if degradation is active
    pub fn is_degraded(&self) -> bool {
        self.system_degradation != DegradationMode::Normal
    }

    /// List all provers in critical state (circuit open)
    pub fn critical_provers(&self) -> Vec<&String> {
        self.prover_health
            .iter()
            .filter(|(_, h)| h.circuit_breaker_state == CircuitBreakerStateSnapshot::Open)
            .map(|(name, _)| name)
            .collect()
    }

    /// Summary string for logging
    pub fn summary(&self) -> String {
        let health_pct = self.health_percentage();
        let failed = self
            .prover_health
            .values()
            .filter(|p| !p.is_available)
            .count();
        let critical = self.critical_provers().len();

        format!(
            "echidna health: {:.1}% | {} provers | {} failed | {} critical | degradation: {:?}",
            health_pct, self.prover_health.len(), failed, critical, self.system_degradation
        )
    }
}

impl Default for HealthStatus {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_health_status_creation() {
        let health = HealthStatus::new();
        assert!(health.prover_health.is_empty());
        assert_eq!(health.system_degradation, DegradationMode::Normal);
        assert_eq!(health.health_percentage(), 100.0);
    }

    #[test]
    fn test_degradation_mode_computation() {
        let mut health = HealthStatus::new();

        // Add multiple provers (at least 3) to avoid ReadOnly trigger
        for i in 0..5 {
            let name = format!("prover{}", i);
            let is_available = i < 4;  // 4 available, 1 unavailable
            let circuit_state = if i == 0 {
                CircuitBreakerStateSnapshot::Open
            } else {
                CircuitBreakerStateSnapshot::Closed
            };

            health.prover_health.insert(
                name.clone(),
                ProverHealth {
                    name,
                    is_available,
                    circuit_breaker_state: circuit_state,
                    last_successful_proof: None,
                    consecutive_failures: if is_available { 0 } else { 5 },
                    avg_latency_ms: if is_available { 50.0 } else { 100.0 },
                    success_rate: if is_available { 1.0 } else { 0.5 },
                    total_invocations: 10,
                    total_failures: if is_available { 0 } else { 5 },
                },
            );
        }

        // Load GNN model with good metrics
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.last_validation_nDCG = 0.65;
        health.gnn_model_health.nDCG_meets_threshold = true;

        health.compute_degradation_mode();
        // One open circuit breaker should trigger IncreasingFallback
        assert_eq!(health.system_degradation, DegradationMode::IncreasingFallback);
    }

    #[test]
    fn test_critical_provers() {
        let mut health = HealthStatus::new();

        health.prover_health.insert(
            "coq".to_string(),
            ProverHealth {
                name: "coq".to_string(),
                is_available: false,
                circuit_breaker_state: CircuitBreakerStateSnapshot::Open,
                last_successful_proof: None,
                consecutive_failures: 3,
                avg_latency_ms: 50.0,
                success_rate: 0.0,
                total_invocations: 5,
                total_failures: 5,
            },
        );

        let critical = health.critical_provers();
        assert_eq!(critical.len(), 1);
        assert_eq!(critical[0], "coq");
    }

    #[test]
    fn test_fallback_sla_enforcement_normal_to_degraded() {
        let mut health = HealthStatus::new();

        // Start in Normal mode
        health.gnn_model_health.is_loaded = true;
        health.gnn_model_health.nDCG_meets_threshold = true;
        health.gnn_model_health.fallback_sla_met = true;
        health.gnn_model_health.fallback_cache_hit_rate = 0.75;  // Warm cache to avoid IncreasingFallback trigger
        health.system_degradation = DegradationMode::Normal;

        // Add at least 3 provers to avoid ReadOnly trigger
        for i in 0..5 {
            health.prover_health.insert(
                format!("prover{}", i),
                ProverHealth {
                    name: format!("prover{}", i),
                    is_available: true,
                    circuit_breaker_state: CircuitBreakerStateSnapshot::Closed,
                    last_successful_proof: None,
                    consecutive_failures: 0,
                    avg_latency_ms: 50.0,
                    success_rate: 1.0,
                    total_invocations: 10,
                    total_failures: 0,
                },
            );
        }

        // Verify system is normal
        health.compute_degradation_mode();
        assert_eq!(health.system_degradation, DegradationMode::Normal);

        // Fallback SLA violation → transition to IncreasingFallback
        health.gnn_model_health.fallback_sla_met = false;
        health.compute_degradation_mode();
        assert_eq!(health.system_degradation, DegradationMode::IncreasingFallback);

        // If already degraded and SLA still violated → escalate
        health.compute_degradation_mode();
        assert_eq!(health.system_degradation, DegradationMode::CosineOnly);
    }
}
