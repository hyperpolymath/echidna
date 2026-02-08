// SPDX-License-Identifier: PMPL-1.0-or-later

//! Statistical Confidence Tracking for Proof Search
//!
//! Tracks per-prover, per-domain success rates and timing statistics
//! to inform portfolio solver weighting and timeout estimation.
//! Uses Bayesian updating for timeout prediction and solver selection.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::provers::ProverKind;

/// Per-prover statistics for a specific domain (aspect)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverDomainStats {
    /// Total number of proof attempts
    pub attempts: u64,

    /// Number of successful proofs
    pub successes: u64,

    /// Number of timeouts
    pub timeouts: u64,

    /// Number of failures (not timeout)
    pub failures: u64,

    /// Sum of proof times (milliseconds) for successful proofs
    pub total_time_ms: u64,

    /// Sum of squared proof times for variance calculation
    pub total_time_sq_ms: u128,

    /// Minimum proof time observed (ms)
    pub min_time_ms: u64,

    /// Maximum proof time observed (ms)
    pub max_time_ms: u64,
}

impl Default for ProverDomainStats {
    fn default() -> Self {
        ProverDomainStats {
            attempts: 0,
            successes: 0,
            timeouts: 0,
            failures: 0,
            total_time_ms: 0,
            total_time_sq_ms: 0,
            min_time_ms: u64::MAX,
            max_time_ms: 0,
        }
    }
}

impl ProverDomainStats {
    /// Record a successful proof attempt
    pub fn record_success(&mut self, time_ms: u64) {
        self.attempts += 1;
        self.successes += 1;
        self.total_time_ms += time_ms;
        self.total_time_sq_ms += (time_ms as u128) * (time_ms as u128);
        if time_ms < self.min_time_ms {
            self.min_time_ms = time_ms;
        }
        if time_ms > self.max_time_ms {
            self.max_time_ms = time_ms;
        }
    }

    /// Record a timeout
    pub fn record_timeout(&mut self) {
        self.attempts += 1;
        self.timeouts += 1;
    }

    /// Record a failure (not timeout)
    pub fn record_failure(&mut self) {
        self.attempts += 1;
        self.failures += 1;
    }

    /// Success rate as a fraction [0.0, 1.0]
    pub fn success_rate(&self) -> f64 {
        if self.attempts == 0 {
            return 0.0;
        }
        self.successes as f64 / self.attempts as f64
    }

    /// Timeout rate as a fraction [0.0, 1.0]
    pub fn timeout_rate(&self) -> f64 {
        if self.attempts == 0 {
            return 0.0;
        }
        self.timeouts as f64 / self.attempts as f64
    }

    /// Mean proof time for successful proofs (ms)
    pub fn mean_time_ms(&self) -> Option<f64> {
        if self.successes == 0 {
            return None;
        }
        Some(self.total_time_ms as f64 / self.successes as f64)
    }

    /// Standard deviation of proof times (ms)
    pub fn std_dev_time_ms(&self) -> Option<f64> {
        if self.successes < 2 {
            return None;
        }
        let n = self.successes as f64;
        let mean = self.total_time_ms as f64 / n;
        let variance = (self.total_time_sq_ms as f64 / n) - (mean * mean);
        if variance < 0.0 {
            // Numerical precision issue
            return Some(0.0);
        }
        Some(variance.sqrt())
    }

    /// Bayesian timeout estimate: mean + 2*std_dev (95th percentile approx)
    /// Falls back to a default if insufficient data
    pub fn estimated_timeout_ms(&self, default_timeout_ms: u64) -> u64 {
        match (self.mean_time_ms(), self.std_dev_time_ms()) {
            (Some(mean), Some(std_dev)) => {
                let estimate = mean + 2.0 * std_dev;
                // Clamp to at least 1 second, at most 10x the default
                let min = 1000u64;
                let max = default_timeout_ms * 10;
                (estimate as u64).clamp(min, max)
            }
            (Some(mean), None) => {
                // Only one data point; use 2x the observed time
                let estimate = (mean * 2.0) as u64;
                estimate.clamp(1000, default_timeout_ms * 10)
            }
            _ => default_timeout_ms,
        }
    }
}

/// Tracks statistics across all provers and domains
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StatisticsTracker {
    /// Stats indexed by "prover::domain" key (JSON requires string keys)
    stats: HashMap<String, ProverDomainStats>,

    /// Global stats per prover (domain = "_global")
    global_stats: HashMap<String, ProverDomainStats>,
}

impl Default for StatisticsTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl StatisticsTracker {
    /// Create a new empty tracker
    pub fn new() -> Self {
        StatisticsTracker {
            stats: HashMap::new(),
            global_stats: HashMap::new(),
        }
    }

    /// Create a combined key for prover+domain lookup
    fn make_key(prover: ProverKind, domain: &str) -> String {
        format!("{:?}::{}", prover, domain)
    }

    /// Record a successful proof
    pub fn record_success(&mut self, prover: ProverKind, domain: &str, time_ms: u64) {
        let key = Self::make_key(prover, domain);
        self.stats.entry(key).or_default().record_success(time_ms);

        let global_key = format!("{:?}", prover);
        self.global_stats.entry(global_key).or_default().record_success(time_ms);
    }

    /// Record a timeout
    pub fn record_timeout(&mut self, prover: ProverKind, domain: &str) {
        let key = Self::make_key(prover, domain);
        self.stats.entry(key).or_default().record_timeout();

        let global_key = format!("{:?}", prover);
        self.global_stats.entry(global_key).or_default().record_timeout();
    }

    /// Record a failure (not timeout)
    pub fn record_failure(&mut self, prover: ProverKind, domain: &str) {
        let key = Self::make_key(prover, domain);
        self.stats.entry(key).or_default().record_failure();

        let global_key = format!("{:?}", prover);
        self.global_stats.entry(global_key).or_default().record_failure();
    }

    /// Get stats for a specific prover and domain
    pub fn get_stats(&self, prover: ProverKind, domain: &str) -> Option<&ProverDomainStats> {
        let key = Self::make_key(prover, domain);
        self.stats.get(&key)
    }

    /// Get global stats for a prover (across all domains)
    pub fn get_global_stats(&self, prover: ProverKind) -> Option<&ProverDomainStats> {
        let key = format!("{:?}", prover);
        self.global_stats.get(&key)
    }

    /// Estimate the best prover for a given domain based on historical data
    /// Returns provers sorted by success rate (descending), with ties broken by speed
    pub fn rank_provers_for_domain(&self, domain: &str) -> Vec<(ProverKind, f64)> {
        let mut rankings: Vec<(ProverKind, f64)> = Vec::new();

        for prover in ProverKind::all() {
            let key = Self::make_key(prover, domain);
            if let Some(stats) = self.stats.get(&key) {
                if stats.attempts >= 3 {
                    // Require at least 3 attempts for statistical significance
                    // Score = success_rate * (1.0 - timeout_rate) * speed_factor
                    let speed_factor = if let Some(mean) = stats.mean_time_ms() {
                        // Normalize: faster is better. Cap at 1.0 for < 1 second
                        (1000.0 / mean).min(1.0)
                    } else {
                        0.5
                    };
                    let score = stats.success_rate() * (1.0 - stats.timeout_rate()) * (0.7 + 0.3 * speed_factor);
                    rankings.push((prover, score));
                }
            }
        }

        rankings.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        rankings
    }

    /// Estimate timeout for a prover on a specific domain
    pub fn estimate_timeout(&self, prover: ProverKind, domain: &str, default_ms: u64) -> u64 {
        // First try domain-specific stats
        let key = Self::make_key(prover, domain);
        if let Some(stats) = self.stats.get(&key) {
            if stats.successes >= 3 {
                return stats.estimated_timeout_ms(default_ms);
            }
        }

        // Fall back to global stats
        let global_key = format!("{:?}", prover);
        if let Some(stats) = self.global_stats.get(&global_key) {
            if stats.successes >= 3 {
                return stats.estimated_timeout_ms(default_ms);
            }
        }

        // No data: use default
        default_ms
    }

    /// Compute a confidence interval on a mutation score
    /// Uses Wilson score interval for binomial proportion
    pub fn mutation_score_confidence_interval(
        caught: u64,
        total: u64,
        confidence_level: f64,
    ) -> (f64, f64) {
        if total == 0 {
            return (0.0, 1.0);
        }

        let n = total as f64;
        let p_hat = caught as f64 / n;

        // z-score for confidence level (approximate)
        let z = if confidence_level >= 0.99 {
            2.576
        } else if confidence_level >= 0.95 {
            1.96
        } else if confidence_level >= 0.90 {
            1.645
        } else {
            1.28
        };

        // Wilson score interval
        let denominator = 1.0 + z * z / n;
        let center = (p_hat + z * z / (2.0 * n)) / denominator;
        let spread = z * ((p_hat * (1.0 - p_hat) / n + z * z / (4.0 * n * n)).sqrt()) / denominator;

        let lower = (center - spread).max(0.0);
        let upper = (center + spread).min(1.0);

        (lower, upper)
    }

    /// Total number of recorded proof attempts
    pub fn total_attempts(&self) -> u64 {
        self.global_stats.values().map(|s| s.attempts).sum()
    }

    /// Serialize to JSON for persistence
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_stats() {
        let stats = ProverDomainStats::default();
        assert_eq!(stats.success_rate(), 0.0);
        assert_eq!(stats.timeout_rate(), 0.0);
        assert!(stats.mean_time_ms().is_none());
        assert!(stats.std_dev_time_ms().is_none());
    }

    #[test]
    fn test_record_success() {
        let mut stats = ProverDomainStats::default();
        stats.record_success(100);
        stats.record_success(200);
        stats.record_success(300);

        assert_eq!(stats.attempts, 3);
        assert_eq!(stats.successes, 3);
        assert_eq!(stats.success_rate(), 1.0);
        assert_eq!(stats.timeout_rate(), 0.0);
        assert_eq!(stats.mean_time_ms(), Some(200.0));
        assert_eq!(stats.min_time_ms, 100);
        assert_eq!(stats.max_time_ms, 300);
    }

    #[test]
    fn test_mixed_outcomes() {
        let mut stats = ProverDomainStats::default();
        stats.record_success(100);
        stats.record_timeout();
        stats.record_failure();
        stats.record_success(200);

        assert_eq!(stats.attempts, 4);
        assert_eq!(stats.successes, 2);
        assert_eq!(stats.timeouts, 1);
        assert_eq!(stats.failures, 1);
        assert_eq!(stats.success_rate(), 0.5);
        assert_eq!(stats.timeout_rate(), 0.25);
    }

    #[test]
    fn test_tracker_record_and_retrieve() {
        let mut tracker = StatisticsTracker::new();
        tracker.record_success(ProverKind::Z3, "algebra", 150);
        tracker.record_success(ProverKind::Z3, "algebra", 200);
        tracker.record_timeout(ProverKind::Z3, "algebra");

        let stats = tracker.get_stats(ProverKind::Z3, "algebra").unwrap();
        assert_eq!(stats.attempts, 3);
        assert_eq!(stats.successes, 2);
        assert_eq!(stats.timeouts, 1);

        let global = tracker.get_global_stats(ProverKind::Z3).unwrap();
        assert_eq!(global.attempts, 3);
    }

    #[test]
    fn test_timeout_estimation() {
        let mut tracker = StatisticsTracker::new();
        // Record several consistent successes
        for _ in 0..10 {
            tracker.record_success(ProverKind::Lean, "topology", 500);
        }

        let estimate = tracker.estimate_timeout(ProverKind::Lean, "topology", 30000);
        // With consistent 500ms proofs, estimate should be around 500-1500ms
        assert!(estimate >= 500);
        assert!(estimate <= 30000);

        // Unknown prover/domain should return default
        let default = tracker.estimate_timeout(ProverKind::Coq, "unknown", 30000);
        assert_eq!(default, 30000);
    }

    #[test]
    fn test_prover_ranking() {
        let mut tracker = StatisticsTracker::new();

        // Z3: 90% success, fast
        for _ in 0..9 {
            tracker.record_success(ProverKind::Z3, "smt", 100);
        }
        tracker.record_failure(ProverKind::Z3, "smt");

        // CVC5: 70% success, slower
        for _ in 0..7 {
            tracker.record_success(ProverKind::CVC5, "smt", 500);
        }
        for _ in 0..3 {
            tracker.record_failure(ProverKind::CVC5, "smt");
        }

        let rankings = tracker.rank_provers_for_domain("smt");
        assert!(!rankings.is_empty());
        // Z3 should rank higher due to better success rate and speed
        assert_eq!(rankings[0].0, ProverKind::Z3);
    }

    #[test]
    fn test_wilson_confidence_interval() {
        // 95 out of 100 caught
        let (lower, upper) = StatisticsTracker::mutation_score_confidence_interval(95, 100, 0.95);
        assert!(lower > 0.88);
        assert!(upper <= 1.0);
        assert!(lower < upper);

        // Edge case: 0 out of 0
        let (lower, upper) = StatisticsTracker::mutation_score_confidence_interval(0, 0, 0.95);
        assert_eq!(lower, 0.0);
        assert_eq!(upper, 1.0);

        // Perfect score: 10 out of 10
        let (lower, upper) = StatisticsTracker::mutation_score_confidence_interval(10, 10, 0.95);
        assert!(lower > 0.7);
        assert_eq!(upper, 1.0);
    }

    #[test]
    fn test_serialization_roundtrip() {
        let mut tracker = StatisticsTracker::new();
        tracker.record_success(ProverKind::Z3, "algebra", 150);
        tracker.record_timeout(ProverKind::Lean, "topology");

        let json = tracker.to_json().unwrap();
        let restored = StatisticsTracker::from_json(&json).unwrap();

        assert_eq!(restored.total_attempts(), 2);
        assert_eq!(
            restored.get_global_stats(ProverKind::Z3).unwrap().successes,
            1
        );
    }
}
