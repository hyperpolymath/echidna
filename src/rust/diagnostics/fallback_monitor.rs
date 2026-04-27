// SPDX-License-Identifier: PMPL-1.0-or-later
// Cosine fallback SLA monitoring and cache health tracking

use serde::{Deserialize, Serialize};
use std::time::Instant;

/// Configuration for cosine fallback SLA
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackSLAConfig {
    /// Maximum latency threshold in milliseconds (default 50ms)
    pub max_latency_ms: f64,
    /// Target cache hit rate (0.0-1.0)
    pub target_hit_rate: f64,
    /// Maximum cache size in entries
    pub max_cache_size: usize,
}

impl Default for FallbackSLAConfig {
    fn default() -> Self {
        FallbackSLAConfig {
            max_latency_ms: 50.0,
            target_hit_rate: 0.8,
            max_cache_size: 10_000,
        }
    }
}

/// Tracks a single fallback invocation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackInvocation {
    /// Time to compute cosine similarity scores (milliseconds)
    pub latency_ms: f64,
    /// Whether result came from cache (vs fresh computation)
    pub cache_hit: bool,
    /// Number of premises scored
    pub premises_scored: usize,
    /// Whether this invocation met SLA (latency < max_latency_ms)
    pub met_sla: bool,
}

/// Fallback monitor: tracks SLA compliance and cache health
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackMonitor {
    config: FallbackSLAConfig,
    /// Total invocations of cosine fallback
    pub total_invocations: u64,
    /// Invocations from cache
    pub cache_hits: u64,
    /// Invocations that violated SLA (latency > max_latency_ms)
    pub sla_violations: u64,
    /// Exponential moving average latency
    pub avg_latency_ms: f64,
    /// Current cache size in entries
    pub cache_size: usize,
    /// Maximum latency seen
    pub max_latency_seen_ms: f64,
}

impl FallbackMonitor {
    pub fn new(config: FallbackSLAConfig) -> Self {
        FallbackMonitor {
            config,
            total_invocations: 0,
            cache_hits: 0,
            sla_violations: 0,
            avg_latency_ms: 0.0,
            cache_size: 0,
            max_latency_seen_ms: 0.0,
        }
    }

    /// Record a fallback invocation
    pub fn record_invocation(&mut self, invocation: FallbackInvocation) {
        self.total_invocations += 1;

        if invocation.cache_hit {
            self.cache_hits += 1;
        }

        if invocation.met_sla == false {
            self.sla_violations += 1;
        }

        // Update exponential moving average latency (0.8 * old + 0.2 * new)
        self.avg_latency_ms =
            (self.avg_latency_ms * 0.8) + (invocation.latency_ms * 0.2);

        // Track maximum latency
        if invocation.latency_ms > self.max_latency_seen_ms {
            self.max_latency_seen_ms = invocation.latency_ms;
        }
    }

    /// Compute cache hit rate
    pub fn hit_rate(&self) -> f64 {
        if self.total_invocations == 0 {
            0.0
        } else {
            self.cache_hits as f64 / self.total_invocations as f64
        }
    }

    /// Compute SLA violation rate
    pub fn violation_rate(&self) -> f64 {
        if self.total_invocations == 0 {
            0.0
        } else {
            self.sla_violations as f64 / self.total_invocations as f64
        }
    }

    /// Check if fallback is healthy (SLA violations < 10%)
    pub fn is_healthy(&self) -> bool {
        self.violation_rate() < 0.1 && self.avg_latency_ms <= self.config.max_latency_ms
    }

    /// Check if cache needs eviction (approaching max size)
    pub fn cache_full(&self) -> bool {
        self.cache_size >= (self.config.max_cache_size * 95 / 100) // 95% threshold
    }

    /// Update cache size
    pub fn set_cache_size(&mut self, size: usize) {
        self.cache_size = size;
    }

    /// Reset statistics
    pub fn reset(&mut self) {
        self.total_invocations = 0;
        self.cache_hits = 0;
        self.sla_violations = 0;
        self.avg_latency_ms = 0.0;
        self.max_latency_seen_ms = 0.0;
    }
}

/// Helper to time a cosine fallback operation
pub struct FallbackTimer {
    start: Instant,
    cache_hit: bool,
    premises_scored: usize,
}

impl FallbackTimer {
    pub fn start(cache_hit: bool, premises_scored: usize) -> Self {
        FallbackTimer {
            start: Instant::now(),
            cache_hit,
            premises_scored,
        }
    }

    /// Finish timing and create invocation record
    pub fn finish(self, max_latency_ms: f64) -> FallbackInvocation {
        let latency_ms = self.start.elapsed().as_millis() as f64;
        let met_sla = latency_ms <= max_latency_ms;

        FallbackInvocation {
            latency_ms,
            cache_hit: self.cache_hit,
            premises_scored: self.premises_scored,
            met_sla,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fallback_monitor_creation() {
        let monitor = FallbackMonitor::new(FallbackSLAConfig::default());
        assert_eq!(monitor.total_invocations, 0);
        assert_eq!(monitor.cache_hits, 0);
        assert_eq!(monitor.hit_rate(), 0.0);
    }

    #[test]
    fn test_record_invocation() {
        let mut monitor = FallbackMonitor::new(FallbackSLAConfig::default());

        monitor.record_invocation(FallbackInvocation {
            latency_ms: 25.0,
            cache_hit: true,
            premises_scored: 100,
            met_sla: true,
        });

        assert_eq!(monitor.total_invocations, 1);
        assert_eq!(monitor.cache_hits, 1);
        assert_eq!(monitor.hit_rate(), 1.0);
        assert_eq!(monitor.sla_violations, 0);
    }

    #[test]
    fn test_sla_violation() {
        let mut monitor = FallbackMonitor::new(FallbackSLAConfig::default());

        monitor.record_invocation(FallbackInvocation {
            latency_ms: 100.0, // Exceeds 50ms default
            cache_hit: false,
            premises_scored: 100,
            met_sla: false,
        });

        assert_eq!(monitor.sla_violations, 1);
        assert_eq!(monitor.violation_rate(), 1.0);
        assert!(!monitor.is_healthy());
    }

    #[test]
    fn test_ema_latency() {
        let mut monitor = FallbackMonitor::new(FallbackSLAConfig::default());

        monitor.record_invocation(FallbackInvocation {
            latency_ms: 10.0,
            cache_hit: true,
            premises_scored: 100,
            met_sla: true,
        });

        monitor.record_invocation(FallbackInvocation {
            latency_ms: 50.0,
            cache_hit: false,
            premises_scored: 100,
            met_sla: true,
        });

        // EMA applied sequentially:
        // First: avg = 0.8 * 0.0 + 0.2 * 10.0 = 2.0
        // Second: avg = 0.8 * 2.0 + 0.2 * 50.0 = 1.6 + 10.0 = 11.6
        assert!((monitor.avg_latency_ms - 11.6).abs() < 0.1);
    }

    #[test]
    fn test_cache_full() {
        let config = FallbackSLAConfig {
            max_cache_size: 1000,
            ..Default::default()
        };
        let mut monitor = FallbackMonitor::new(config);

        monitor.set_cache_size(950); // 95% of max
        assert!(monitor.cache_full());

        monitor.set_cache_size(900); // 90% of max
        assert!(!monitor.cache_full());
    }

    #[test]
    fn test_health_check() {
        let mut monitor = FallbackMonitor::new(FallbackSLAConfig::default());

        // Add healthy invocations (10 passing = 90.9% pass rate with 1 violation)
        for _ in 0..10 {
            monitor.record_invocation(FallbackInvocation {
                latency_ms: 30.0,
                cache_hit: true,
                premises_scored: 100,
                met_sla: true,
            });
        }

        // Add one violation (1/11 = 9.09% violation rate)
        monitor.record_invocation(FallbackInvocation {
            latency_ms: 60.0,
            cache_hit: false,
            premises_scored: 100,
            met_sla: false,
        });

        assert!((monitor.violation_rate() - (1.0 / 11.0)).abs() < 0.01); // ~9% violations
        assert!(monitor.is_healthy()); // Under 10% threshold
    }
}
