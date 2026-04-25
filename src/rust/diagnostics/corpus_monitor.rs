// SPDX-License-Identifier: PMPL-1.0-or-later
// Monitor corpus health: proofs, premises, size metrics

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;
use std::sync::{Arc, Mutex};

/// Snapshot of corpus metrics at a point in time
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorpusMetrics {
    /// Total number of proof records
    pub total_proofs: usize,
    /// Total number of premises/tactics
    pub total_premises: usize,
    /// Total corpus size in MB
    pub size_mb: f64,
    /// Percentage change since last check
    pub size_change_percent: f64,
    /// Timestamp of last update
    pub last_updated: DateTime<Utc>,
}

impl Default for CorpusMetrics {
    fn default() -> Self {
        Self {
            total_proofs: 0,
            total_premises: 0,
            size_mb: 0.0,
            size_change_percent: 0.0,
            last_updated: Utc::now(),
        }
    }
}

/// Monitor for corpus health and growth
///
/// Tracks:
/// - Number of proofs and premises in the corpus
/// - Size metrics (MB)
/// - Growth rates and trends
pub struct CorpusMonitor {
    /// Path to training data directory
    training_data_dir: String,
    /// Current metrics
    current: Arc<Mutex<CorpusMetrics>>,
    /// Previous metrics (for computing change %)
    previous: Arc<Mutex<CorpusMetrics>>,
}

impl CorpusMonitor {
    /// Create a new corpus monitor for the given training data directory
    pub fn new(training_data_dir: impl Into<String>) -> Self {
        Self {
            training_data_dir: training_data_dir.into(),
            current: Arc::new(Mutex::new(CorpusMetrics::default())),
            previous: Arc::new(Mutex::new(CorpusMetrics::default())),
        }
    }

    /// Scan the corpus directory and update metrics
    pub fn scan_corpus(&self) -> Result<CorpusMetrics, String> {
        let path = Path::new(&self.training_data_dir);

        if !path.exists() {
            return Err(format!(
                "Training data directory not found: {}",
                self.training_data_dir
            ));
        }

        let mut total_proofs = 0;
        let mut total_premises = 0;
        let mut total_size_bytes = 0u64;

        // Scan for premises_*.jsonl files
        match fs::read_dir(path) {
            Ok(entries) => {
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        let filename = path
                            .file_name()
                            .and_then(|n| n.to_str())
                            .unwrap_or("");

                        if filename.starts_with("premises_") && filename.ends_with(".jsonl") {
                            if let Ok(metadata) = fs::metadata(&path) {
                                total_size_bytes += metadata.len();

                                // Count lines (proofs) in the file
                                if let Ok(content) = fs::read_to_string(&path) {
                                    let line_count = content.lines().count();
                                    total_proofs += line_count;
                                    // Estimate premises as 2-3 per proof on average
                                    total_premises += line_count * 2;
                                }
                            }
                        }
                    }
                }
            }
            Err(e) => {
                return Err(format!("Failed to read corpus directory: {}", e));
            }
        }

        // Calculate size change percentage
        let size_mb = total_size_bytes as f64 / (1024.0 * 1024.0);
        let size_change_percent = if let Ok(prev) = self.previous.lock() {
            if prev.size_mb > 0.0 {
                ((size_mb - prev.size_mb) / prev.size_mb) * 100.0
            } else {
                0.0
            }
        } else {
            0.0
        };

        let metrics = CorpusMetrics {
            total_proofs,
            total_premises,
            size_mb,
            size_change_percent,
            last_updated: Utc::now(),
        };

        // Update internal state
        if let Ok(mut curr) = self.current.lock() {
            if let Ok(mut prev) = self.previous.lock() {
                *prev = (*curr).clone();
            }
            *curr = metrics.clone();
        }

        Ok(metrics)
    }

    /// Get current corpus metrics
    pub fn metrics(&self) -> CorpusMetrics {
        self.current
            .lock()
            .ok()
            .map(|m| m.clone())
            .unwrap_or_default()
    }

    /// Add a new proof record to the corpus count
    pub fn add_proof(&self, premise_count: usize) {
        if let Ok(mut metrics) = self.current.lock() {
            metrics.total_proofs += 1;
            metrics.total_premises += premise_count;
            metrics.last_updated = Utc::now();
        }
    }

    /// Update corpus size estimate
    pub fn update_size(&self, size_mb: f64) {
        if let Ok(mut metrics) = self.current.lock() {
            let prev_size = metrics.size_mb;
            metrics.size_mb = size_mb;
            if prev_size > 0.0 {
                metrics.size_change_percent = ((size_mb - prev_size) / prev_size) * 100.0;
            }
            metrics.last_updated = Utc::now();
        }
    }

    /// Get total number of proofs
    pub fn total_proofs(&self) -> usize {
        self.current
            .lock()
            .ok()
            .map(|m| m.total_proofs)
            .unwrap_or(0)
    }

    /// Get total number of premises
    pub fn total_premises(&self) -> usize {
        self.current
            .lock()
            .ok()
            .map(|m| m.total_premises)
            .unwrap_or(0)
    }

    /// Get corpus size in MB
    pub fn size_mb(&self) -> f64 {
        self.current
            .lock()
            .ok()
            .map(|m| m.size_mb)
            .unwrap_or(0.0)
    }

    /// Get size change percentage since last check
    pub fn size_change_percent(&self) -> f64 {
        self.current
            .lock()
            .ok()
            .map(|m| m.size_change_percent)
            .unwrap_or(0.0)
    }

    /// Reset metrics to default
    pub fn reset(&self) {
        if let Ok(mut metrics) = self.current.lock() {
            *metrics = CorpusMetrics::default();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_corpus_monitor_creation() {
        let monitor = CorpusMonitor::new("./test_data");
        assert_eq!(monitor.total_proofs(), 0);
        assert_eq!(monitor.total_premises(), 0);
    }

    #[test]
    fn test_add_proof() {
        let monitor = CorpusMonitor::new("./test_data");
        monitor.add_proof(3);
        monitor.add_proof(5);

        assert_eq!(monitor.total_proofs(), 2);
        assert_eq!(monitor.total_premises(), 8); // 3 + 5
    }

    #[test]
    fn test_update_size() {
        let monitor = CorpusMonitor::new("./test_data");
        monitor.update_size(100.0);

        let metrics = monitor.metrics();
        assert_eq!(metrics.size_mb, 100.0);
        assert_eq!(metrics.size_change_percent, 0.0); // First update

        monitor.update_size(150.0);
        let metrics = monitor.metrics();
        assert!(metrics.size_change_percent > 0.0); // Should show growth
        assert!((metrics.size_change_percent - 50.0).abs() < 0.1); // 50% growth
    }

    #[test]
    fn test_scan_corpus_no_directory() {
        let monitor = CorpusMonitor::new("/nonexistent/path");
        assert!(monitor.scan_corpus().is_err());
    }

    #[test]
    fn test_scan_corpus_empty_directory() {
        if let Ok(temp_dir) = TempDir::new() {
            let path = temp_dir.path().to_str().unwrap();
            let monitor = CorpusMonitor::new(path);

            // Should succeed but return zero counts
            match monitor.scan_corpus() {
                Ok(metrics) => {
                    assert_eq!(metrics.total_proofs, 0);
                    assert_eq!(metrics.total_premises, 0);
                    assert_eq!(metrics.size_mb, 0.0);
                }
                Err(e) => panic!("Failed to scan empty directory: {}", e),
            }
        }
    }

    #[test]
    fn test_corpus_metrics_timestamp() {
        let monitor = CorpusMonitor::new("./test_data");
        monitor.add_proof(1);

        let metrics = monitor.metrics();
        let now = Utc::now();
        let diff = now.signed_duration_since(metrics.last_updated);
        // Timestamp should be recent (within a few seconds)
        assert!(diff.num_seconds() < 5);
    }

    #[test]
    fn test_corpus_metrics_serialization() {
        let metrics = CorpusMetrics {
            total_proofs: 1000,
            total_premises: 3000,
            size_mb: 512.5,
            size_change_percent: 5.5,
            last_updated: Utc::now(),
        };

        // Verify metrics can be serialized to JSON
        let json = serde_json::to_string(&metrics).expect("Should serialize");
        assert!(json.contains("1000"));
        assert!(json.contains("3000"));
    }

    #[test]
    fn test_reset_corpus() {
        let monitor = CorpusMonitor::new("./test_data");
        monitor.add_proof(5);
        monitor.update_size(250.0);

        assert!(monitor.total_proofs() > 0);
        assert!(monitor.size_mb() > 0.0);

        monitor.reset();
        assert_eq!(monitor.total_proofs(), 0);
        assert_eq!(monitor.total_premises(), 0);
    }
}
