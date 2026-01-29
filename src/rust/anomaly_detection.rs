// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// Anomaly detection for proof validation

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Anomaly {
    /// ML model is overconfident (>95%) for a complex theorem
    UnusuallyHighConfidence {
        goal: String,
        confidence: f64,
        complexity_score: usize,
    },

    /// Multiple provers disagree on provability
    ProverDisagreement {
        goal: String,
        agreeing: Vec<String>,
        disagreeing: Vec<String>,
    },

    /// Proof contains circular reasoning (conclusion in premises)
    CircularReasoning {
        goal: String,
        suspicious_premise: String,
    },

    /// Proof is unusually long for a simple theorem
    ExcessiveComplexity {
        goal: String,
        tactic_count: usize,
        expected_max: usize,
    },

    /// Type mismatch between premise and goal
    TypeMismatch {
        premise_type: String,
        goal_type: String,
    },

    /// Invalid tactic sequence (tactic doesn't apply)
    InvalidTacticSequence {
        tactic: String,
        state: String,
        reason: String,
    },

    /// Proof time is anomalous (too fast or too slow)
    AnomalousProofTime {
        goal: String,
        time_ms: u64,
        expected_range: (u64, u64),
    },
}

#[derive(Debug, Clone)]
pub struct BaselineMetrics {
    pub max_tactics: usize,
    pub max_complexity: usize,
    pub avg_proof_time_ms: u64,
    pub confidence_threshold: f64,
}

impl Default for BaselineMetrics {
    fn default() -> Self {
        Self {
            max_tactics: 20,
            max_complexity: 100,
            avg_proof_time_ms: 5000,
            confidence_threshold: 0.95,
        }
    }
}

pub struct AnomalyDetector {
    baseline: BaselineMetrics,
}

impl AnomalyDetector {
    pub fn new() -> Self {
        Self {
            baseline: BaselineMetrics::default(),
        }
    }

    pub fn with_baseline(baseline: BaselineMetrics) -> Self {
        Self { baseline }
    }

    /// Detect anomalies in a proof result
    pub fn detect(&self, result: &ProofResult) -> Vec<Anomaly> {
        let mut anomalies = Vec::new();

        // Check 1: Unusually high confidence for complex theorem
        if self.is_complex_theorem(&result.goal)
            && result.confidence > self.baseline.confidence_threshold
        {
            anomalies.push(Anomaly::UnusuallyHighConfidence {
                goal: result.goal.clone(),
                confidence: result.confidence,
                complexity_score: self.calculate_complexity(&result.goal),
            });
        }

        // Check 2: Excessive proof complexity
        if result.tactic_count > self.baseline.max_tactics {
            anomalies.push(Anomaly::ExcessiveComplexity {
                goal: result.goal.clone(),
                tactic_count: result.tactic_count,
                expected_max: self.baseline.max_tactics,
            });
        }

        // Check 3: Anomalous proof time
        let expected_min = self.baseline.avg_proof_time_ms / 10;
        let expected_max = self.baseline.avg_proof_time_ms * 3;
        if result.time_ms < expected_min || result.time_ms > expected_max {
            anomalies.push(Anomaly::AnomalousProofTime {
                goal: result.goal.clone(),
                time_ms: result.time_ms,
                expected_range: (expected_min, expected_max),
            });
        }

        // Check 4: Circular reasoning
        if let Some(circular_premise) = self.check_circular_reasoning(&result) {
            anomalies.push(Anomaly::CircularReasoning {
                goal: result.goal.clone(),
                suspicious_premise: circular_premise,
            });
        }

        anomalies
    }

    /// Check if theorem is complex (multiple quantifiers, long)
    fn is_complex_theorem(&self, goal: &str) -> bool {
        goal.matches("forall").count() > 2
            || goal.matches("exists").count() > 1
            || goal.len() > 100
    }

    /// Calculate theorem complexity score
    fn calculate_complexity(&self, goal: &str) -> usize {
        let quantifiers = goal.matches("forall").count() + goal.matches("exists").count();
        let implications = goal.matches("->").count() + goal.matches("→").count();
        let conjunctions = goal.matches("/\\").count() + goal.matches("∧").count();

        quantifiers * 10 + implications * 5 + conjunctions * 3 + goal.len() / 10
    }

    /// Check for circular reasoning (goal appears in premises)
    fn check_circular_reasoning(&self, result: &ProofResult) -> Option<String> {
        for premise in &result.premises {
            if premise.contains(&result.goal) || result.goal.contains(premise) {
                return Some(premise.clone());
            }
        }
        None
    }
}

/// Multi-prover consensus checker
pub struct ConsensusChecker {
    min_agreement: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsensusResult {
    pub agreed: bool,
    pub voting: HashMap<String, bool>,
    pub confidence: f64,
}

impl ConsensusChecker {
    pub fn new(min_agreement: usize) -> Self {
        Self { min_agreement }
    }

    /// Check consensus across multiple provers
    pub fn check_consensus(
        &self,
        goal: &str,
        prover_results: Vec<(String, bool)>,
    ) -> ConsensusResult {
        let mut voting = HashMap::new();

        for (prover, success) in prover_results {
            voting.insert(prover, success);
        }

        let success_count = voting.values().filter(|&&v| v).count();
        let total = voting.len();

        ConsensusResult {
            agreed: success_count >= self.min_agreement,
            voting,
            confidence: success_count as f64 / total as f64,
        }
    }
}

/// Proof result structure for anomaly detection
#[derive(Debug, Clone)]
pub struct ProofResult {
    pub goal: String,
    pub success: bool,
    pub confidence: f64,
    pub tactic_count: usize,
    pub time_ms: u64,
    pub premises: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_complex_theorem_detection() {
        let detector = AnomalyDetector::new();

        // Simple theorem
        assert!(!detector.is_complex_theorem("n + 0 = n"));

        // Complex theorem (multiple quantifiers)
        assert!(detector.is_complex_theorem(
            "forall n m p : nat, forall q r : nat, n + m = m + n"
        ));

        // Long theorem
        assert!(detector.is_complex_theorem(
            &"x ".repeat(60) // 120 characters
        ));
    }

    #[test]
    fn test_circular_reasoning_detection() {
        let detector = AnomalyDetector::new();

        let result = ProofResult {
            goal: "n + m = m + n".to_string(),
            success: true,
            confidence: 0.85,
            tactic_count: 3,
            time_ms: 100,
            premises: vec![
                "forall n, n + 0 = n".to_string(),
                "n + m = m + n".to_string(), // Circular!
            ],
        };

        let circular = detector.check_circular_reasoning(&result);
        assert!(circular.is_some());
    }

    #[test]
    fn test_anomaly_detection() {
        let detector = AnomalyDetector::new();

        // Create a suspicious result
        let result = ProofResult {
            goal: "forall n m p : nat, (n + m) + p = n + (m + p)".to_string(),
            success: true,
            confidence: 0.99, // Too confident for complex theorem!
            tactic_count: 50,  // Way too many tactics!
            time_ms: 50000,    // Too slow!
            premises: vec![],
        };

        let anomalies = detector.detect(&result);

        assert!(!anomalies.is_empty());
        assert!(anomalies
            .iter()
            .any(|a| matches!(a, Anomaly::UnusuallyHighConfidence { .. })));
        assert!(anomalies
            .iter()
            .any(|a| matches!(a, Anomaly::ExcessiveComplexity { .. })));
    }

    #[test]
    fn test_consensus_checker() {
        let checker = ConsensusChecker::new(3); // Need 3 agreeing

        let results = vec![
            ("coq".to_string(), true),
            ("lean".to_string(), true),
            ("agda".to_string(), true),
            ("isabelle".to_string(), false),
        ];

        let consensus = checker.check_consensus("n + 0 = n", results);

        assert!(consensus.agreed); // 3/4 succeeded
        assert_eq!(consensus.confidence, 0.75);
    }
}
