// SPDX-License-Identifier: PMPL-1.0-or-later
// Monitor cosine similarity fallback performance and SLA compliance

use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex};

/// Configuration for fallback SLA monitoring
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackSlaConfig {
    /// Maximum acceptable latency for cosine similarity in milliseconds
    pub max_latency_ms: u64,
    /// Minimum success rate (cache hit rate) expected (0.0 to 1.0)
    pub min_success_rate: f64,
    /// Maximum cache size in entries before considered high
    pub max_cache_size: usize,
}

impl Default for FallbackSlaConfig {
    fn default() -> Self {
        Self {
            max_latency_ms: 500,     // 500ms max latency
            min_success_rate: 0.50,  // 50% min hit rate
            max_cache_size: 10000,   // 10k max entries
        }
    }
}

/// Metrics for cosine similarity fallback performance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackMetrics {
    /// Total number of fallback invocations
    pub total_invocations: u64,
    /// Number of fallback cache hits
    pub cache_hits: u64,
    /// Average latency of fallback operations (ms)
    pub avg_latency_ms: f64,
    /// Maximum latency observed (ms)
    pub max_latency_ms: u64,
    /// Minimum latency observed (ms)
    pub min_latency_ms: u64,
    /// Current cache size
    pub cache_size: usize,
    /// Whether currently meeting SLA
    pub meets_sla: bool,
}

impl Default for FallbackMetrics {
    fn default() -> Self {
        Self {
            total_invocations: 0,
            cache_hits: 0,
            avg_latency_ms: 0.0,
            max_latency_ms: 0,
            min_latency_ms: u64::MAX,
            cache_size: 0,
            meets_sla: true,
        }
    }
}

impl FallbackMetrics {
    /// Calculate cache hit rate (0.0 to 1.0)
    pub fn cache_hit_rate(&self) -> f64 {
        if self.total_invocations == 0 {
            return 0.0;
        }
        self.cache_hits as f64 / self.total_invocations as f64
    }

    /// Check if metrics meet SLA requirements
    pub fn check_sla(&mut self, config: &FallbackSlaConfig) {
        self.meets_sla = self.avg_latency_ms <= config.max_latency_ms as f64
            && self.cache_hit_rate() >= config.min_success_rate;
    }
}

/// Monitor for cosine similarity fallback performance
///
/// Tracks:
/// - Invocation count and latency statistics
/// - Cache hit rates
/// - SLA compliance
pub struct FallbackMonitor {
    config: FallbackSlaConfig,
    metrics: Arc<Mutex<FallbackMetrics>>,
}

impl FallbackMonitor {
    /// Create a new fallback monitor with default SLA config
    pub fn new() -> Self {
        Self::with_config(FallbackSlaConfig::default())
    }

    /// Create a new fallback monitor with custom SLA config
    pub fn with_config(config: FallbackSlaConfig) -> Self {
        Self {
            config,
            metrics: Arc::new(Mutex::new(FallbackMetrics::default())),
        }
    }

    /// Record a successful fallback operation with latency
    pub fn record_fallback(&self, latency_ms: u64, is_cache_hit: bool) {
        if let Ok(mut metrics) = self.metrics.lock() {
            metrics.total_invocations += 1;

            // Update latency statistics (cumulative arithmetic mean over all invocations)
            let invocations = metrics.total_invocations as f64;
            metrics.avg_latency_ms = (metrics.avg_latency_ms * (invocations - 1.0)
                + latency_ms as f64)
                / invocations;

            // Track max/min latency
            metrics.max_latency_ms = metrics.max_latency_ms.max(latency_ms);
            metrics.min_latency_ms = metrics.min_latency_ms.min(latency_ms);

            // Track cache hits
            if is_cache_hit {
                metrics.cache_hits += 1;
            }

            // Check SLA compliance
            metrics.check_sla(&self.config);
        }
    }

    /// Update cache size metrics
    pub fn set_cache_size(&self, size: usize) {
        if let Ok(mut metrics) = self.metrics.lock() {
            metrics.cache_size = size;
        }
    }

    /// Get current metrics snapshot
    pub fn metrics(&self) -> FallbackMetrics {
        self.metrics
            .lock()
            .ok()
            .map(|m| m.clone())
            .unwrap_or_default()
    }

    /// Check if currently meeting SLA
    pub fn meets_sla(&self) -> bool {
        self.metrics
            .lock()
            .ok()
            .map(|m| m.meets_sla)
            .unwrap_or(true)
    }

    /// Get cache hit rate
    pub fn cache_hit_rate(&self) -> f64 {
        self.metrics
            .lock()
            .ok()
            .map(|m| m.cache_hit_rate())
            .unwrap_or(0.0)
    }

    /// Reset all metrics to default
    pub fn reset(&self) {
        if let Ok(mut metrics) = self.metrics.lock() {
            *metrics = FallbackMetrics::default();
        }
    }
}

impl Default for FallbackMonitor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fallback_monitor_creation() {
        let monitor = FallbackMonitor::new();
        assert_eq!(monitor.metrics().total_invocations, 0);
        assert_eq!(monitor.cache_hit_rate(), 0.0);
        assert!(monitor.meets_sla());
    }

    #[test]
    fn test_record_fallback_hit() {
        let monitor = FallbackMonitor::new();
        monitor.record_fallback(100, true);

        let metrics = monitor.metrics();
        assert_eq!(metrics.total_invocations, 1);
        assert_eq!(metrics.cache_hits, 1);
        assert_eq!(monitor.cache_hit_rate(), 1.0);
    }

    #[test]
    fn test_record_fallback_miss() {
        let monitor = FallbackMonitor::new();
        monitor.record_fallback(200, false);

        let metrics = monitor.metrics();
        assert_eq!(metrics.total_invocations, 1);
        assert_eq!(metrics.cache_hits, 0);
        assert_eq!(monitor.cache_hit_rate(), 0.0);
    }

    #[test]
    fn test_latency_tracking() {
        let monitor = FallbackMonitor::new();
        monitor.record_fallback(100, false);
        monitor.record_fallback(200, false);
        monitor.record_fallback(300, false);

        let metrics = monitor.metrics();
        assert_eq!(metrics.min_latency_ms, 100);
        assert_eq!(metrics.max_latency_ms, 300);
        // Average should be approximately 200
        assert!((metrics.avg_latency_ms - 200.0).abs() < 0.1);
    }

    #[test]
    fn test_sla_compliance_within_threshold() {
        let config = FallbackSlaConfig {
            max_latency_ms: 500,
            min_success_rate: 0.5,
            max_cache_size: 10000,
        };
        let monitor = FallbackMonitor::with_config(config);

        // Record operations that meet SLA
        monitor.record_fallback(100, true);  // Hit, low latency
        monitor.record_fallback(150, true);  // Hit, low latency

        let metrics = monitor.metrics();
        assert!(metrics.meets_sla);
        assert!(metrics.avg_latency_ms <= 500.0);
        assert!(metrics.cache_hit_rate() >= 0.5);
    }

    #[test]
    fn test_sla_violation_latency() {
        let config = FallbackSlaConfig {
            max_latency_ms: 200,
            min_success_rate: 0.5,
            max_cache_size: 10000,
        };
        let monitor = FallbackMonitor::with_config(config);

        // Record high-latency operation
        monitor.record_fallback(300, true);

        let metrics = monitor.metrics();
        assert!(!metrics.meets_sla);
    }

    #[test]
    fn test_sla_violation_hit_rate() {
        let config = FallbackSlaConfig {
            max_latency_ms: 500,
            min_success_rate: 0.8,
            max_cache_size: 10000,
        };
        let monitor = FallbackMonitor::with_config(config);

        // Record low hit rate
        monitor.record_fallback(100, false);
        monitor.record_fallback(100, false);
        monitor.record_fallback(100, true);

        let metrics = monitor.metrics();
        assert!(!metrics.meets_sla);
        assert!(metrics.cache_hit_rate() < 0.8);
    }

    #[test]
    fn test_cache_size_tracking() {
        let monitor = FallbackMonitor::new();
        monitor.set_cache_size(100);

        let metrics = monitor.metrics();
        assert_eq!(metrics.cache_size, 100);

        monitor.set_cache_size(500);
        let metrics = monitor.metrics();
        assert_eq!(metrics.cache_size, 500);
    }

    #[test]
    fn test_reset_metrics() {
        let monitor = FallbackMonitor::new();
        monitor.record_fallback(100, true);
        monitor.set_cache_size(1000);

        let metrics = monitor.metrics();
        assert!(metrics.total_invocations > 0);

        monitor.reset();

        let metrics = monitor.metrics();
        assert_eq!(metrics.total_invocations, 0);
        assert_eq!(metrics.cache_size, 0);
    }
}
