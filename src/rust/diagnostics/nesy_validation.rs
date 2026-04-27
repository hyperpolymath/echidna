// SPDX-License-Identifier: PMPL-1.0-or-later
// NeSy (Neurosymbolic) agreement validation between GNN and symbolic solvers

use serde::{Deserialize, Serialize};

/// Neural-symbolic ranking agreement contract
/// Compares GNN ranking against symbolic solver (cosine fallback) results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeSyRankingContract {
    /// Premise identifier
    pub premise_id: String,
    /// GNN confidence score (0.0-1.0)
    pub gnn_score: f32,
    /// GNN rank position in sorted list
    pub gnn_rank: usize,
    /// Threshold for "high confidence" (typically 0.8)
    pub gnn_threshold: f32,
    /// Whether GNN score meets threshold
    pub gnn_in_top_k: bool,

    /// Whether symbolic solver found a proof using this premise
    pub proof_found: bool,
    /// Number of tactics in the proof (if found)
    pub proof_tactic_count: usize,
    /// Proof depth (if found)
    pub proof_depth: usize,
}

impl NeSyRankingContract {
    /// Check if this contract holds: high GNN confidence → proof found
    pub fn is_agreement(&self) -> bool {
        // High confidence (≥0.8) must lead to proof found
        if self.gnn_score >= 0.8 {
            self.proof_found
        } else {
            // Low confidence: anything is acceptable
            true
        }
    }
}

/// Aggregate metrics across many ranking comparisons
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeSyMetrics {
    /// Total contracts evaluated
    pub total_contracts: usize,
    /// Number that satisfy agreement property
    pub total_agreements: usize,
    /// Agreement rate as percentage (0.0-1.0)
    pub agreement_rate: f64,
    /// False positives: GNN says yes, proof fails
    pub false_positive_rate: f64,
    /// False negatives: GNN says no, but proof succeeds
    pub false_negative_rate: f64,
    /// List of prover systems tested
    pub provers_tested: Vec<String>,
}

/// Compute agreement rate across a batch of contracts
pub fn compute_agreement_rate(contracts: &[NeSyRankingContract]) -> f64 {
    if contracts.is_empty() {
        return 0.0;
    }
    let agreements = contracts.iter().filter(|c| c.is_agreement()).count();
    agreements as f64 / contracts.len() as f64
}

/// Check if GNN model should be flagged as suspect
/// Threshold: agreement < 0.75 triggers fallback
pub fn is_gnn_suspect(agreement_rate: f64) -> bool {
    agreement_rate < 0.75
}

/// Compute full metrics across contracts
pub fn compute_metrics(contracts: &[NeSyRankingContract], provers: Vec<String>) -> NeSyMetrics {
    if contracts.is_empty() {
        return NeSyMetrics {
            total_contracts: 0,
            total_agreements: 0,
            agreement_rate: 0.0,
            false_positive_rate: 0.0,
            false_negative_rate: 0.0,
            provers_tested: provers,
        };
    }

    let total = contracts.len();
    let agreements = contracts.iter().filter(|c| c.is_agreement()).count();

    // High confidence (≥0.8) cases: if agreement fails, that's a false positive
    let high_confidence: Vec<_> = contracts
        .iter()
        .filter(|c| c.gnn_score >= 0.8)
        .collect();
    let false_positives = high_confidence
        .iter()
        .filter(|c| !c.proof_found)
        .count();
    let fp_rate = if high_confidence.is_empty() {
        0.0
    } else {
        false_positives as f64 / high_confidence.len() as f64
    };

    // Low confidence (< 0.8) cases: if proof succeeds anyway, that's a false negative
    let low_confidence: Vec<_> = contracts
        .iter()
        .filter(|c| c.gnn_score < 0.8)
        .collect();
    let false_negatives = low_confidence
        .iter()
        .filter(|c| c.proof_found)
        .count();
    let fn_rate = if low_confidence.is_empty() {
        0.0
    } else {
        false_negatives as f64 / low_confidence.len() as f64
    };

    NeSyMetrics {
        total_contracts: total,
        total_agreements: agreements,
        agreement_rate: agreements as f64 / total as f64,
        false_positive_rate: fp_rate,
        false_negative_rate: fn_rate,
        provers_tested: provers,
    }
}

/// Gate for claiming "GNN model is verified"
/// Requires: agreement > 0.75 AND false_positive_rate < 0.1
pub fn can_claim_gnn_verified(metrics: &NeSyMetrics) -> bool {
    metrics.agreement_rate > 0.75 && metrics.false_positive_rate < 0.1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_agreement_high_confidence_match() {
        let contract = NeSyRankingContract {
            premise_id: "test".to_string(),
            gnn_score: 0.85,
            gnn_rank: 0,
            gnn_threshold: 0.8,
            gnn_in_top_k: true,
            proof_found: true,
            proof_tactic_count: 5,
            proof_depth: 3,
        };
        assert!(contract.is_agreement());
    }

    #[test]
    fn test_agreement_high_confidence_mismatch() {
        let contract = NeSyRankingContract {
            premise_id: "test".to_string(),
            gnn_score: 0.85,
            gnn_rank: 0,
            gnn_threshold: 0.8,
            gnn_in_top_k: true,
            proof_found: false,
            proof_tactic_count: 0,
            proof_depth: 0,
        };
        assert!(!contract.is_agreement());
    }

    #[test]
    fn test_agreement_low_confidence() {
        let contract = NeSyRankingContract {
            premise_id: "test".to_string(),
            gnn_score: 0.5,
            gnn_rank: 10,
            gnn_threshold: 0.8,
            gnn_in_top_k: false,
            proof_found: false,
            proof_tactic_count: 0,
            proof_depth: 0,
        };
        assert!(contract.is_agreement()); // Low confidence → any outcome ok
    }

    #[test]
    fn test_compute_agreement_rate() {
        let contracts = vec![
            NeSyRankingContract {
                premise_id: "a".to_string(),
                gnn_score: 0.85,
                gnn_rank: 0,
                gnn_threshold: 0.8,
                gnn_in_top_k: true,
                proof_found: true,
                proof_tactic_count: 3,
                proof_depth: 2,
            },
            NeSyRankingContract {
                premise_id: "b".to_string(),
                gnn_score: 0.5,
                gnn_rank: 5,
                gnn_threshold: 0.8,
                gnn_in_top_k: false,
                proof_found: false,
                proof_tactic_count: 0,
                proof_depth: 0,
            },
        ];
        let rate = compute_agreement_rate(&contracts);
        assert!((rate - 1.0).abs() < 0.001); // Both agree
    }

    #[test]
    fn test_gnn_suspect() {
        assert!(is_gnn_suspect(0.7)); // Below 0.75 → suspect
        assert!(!is_gnn_suspect(0.8)); // Above 0.75 → not suspect
        assert!(!is_gnn_suspect(0.75)); // Edge case: equal to 0.75 → not suspect
    }
}
