// SPDX-License-Identifier: PMPL-1.0-or-later
// GNN model training integration with health monitoring

use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;
use chrono::{DateTime, Utc};

/// Metrics exported from GNN training pipeline
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GnnTrainingMetrics {
    pub timestamp: String,
    pub training_data_size: usize,
    pub epochs_trained: usize,
    pub nDCG: f32,
    pub MRR: f32,
    pub model_location: String,
    pub status: String,
}

/// Load GNN training metrics from JSON file
/// Returns None if file doesn't exist or can't be parsed
pub fn load_training_metrics(metrics_path: &Path) -> Option<GnnTrainingMetrics> {
    match fs::read_to_string(metrics_path) {
        Ok(json_content) => match serde_json::from_str::<GnnTrainingMetrics>(&json_content) {
            Ok(metrics) => Some(metrics),
            Err(e) => {
                eprintln!("Failed to parse training metrics: {}", e);
                None
            }
        },
        Err(_) => None,
    }
}

/// Update HealthStatus with GNN training results
/// Called after training completes to populate last_validation_nDCG and related fields
pub fn update_health_with_metrics(
    health: &mut crate::diagnostics::HealthStatus,
    metrics: &GnnTrainingMetrics,
) {
    health.gnn_model_health.is_loaded = true;
    health.gnn_model_health.last_validation_nDCG = metrics.nDCG;
    health.gnn_model_health.last_validation_MRR = metrics.MRR;
    
    // Mark as meeting threshold if nDCG >= 0.65
    health.gnn_model_health.nDCG_meets_threshold = metrics.nDCG >= 0.65;
    
    // Update last_trained timestamp
    if let Ok(ts) = DateTime::parse_from_rfc3339(&metrics.timestamp) {
        health.gnn_model_health.last_trained = Some(ts.with_timezone(&Utc));
    }
    
    // Recompute degradation with updated GNN metrics
    health.compute_degradation_mode();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gnn_training_metrics_structure() {
        // Verify that GnnTrainingMetrics can be serialized/deserialized
        let metrics = GnnTrainingMetrics {
            timestamp: "2026-04-25T12:00:00Z".to_string(),
            training_data_size: 1000,
            epochs_trained: 50,
            nDCG: 0.75,
            MRR: 0.68,
            model_location: "models/neural/gnn_ranker".to_string(),
            status: "completed".to_string(),
        };

        // Convert to JSON and back
        let json = serde_json::to_string(&metrics).unwrap();
        let parsed: GnnTrainingMetrics = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed.nDCG, 0.75);
        assert_eq!(parsed.MRR, 0.68);
        assert_eq!(parsed.training_data_size, 1000);
    }

    #[test]
    fn test_update_health_with_metrics() {
        let mut health = crate::diagnostics::HealthStatus::new();

        // Initially GNN is not loaded
        assert!(!health.gnn_model_health.is_loaded);
        assert_eq!(health.gnn_model_health.last_validation_nDCG, 0.0);

        let metrics = GnnTrainingMetrics {
            timestamp: "2026-04-25T12:00:00Z".to_string(),
            training_data_size: 1000,
            epochs_trained: 50,
            nDCG: 0.78,
            MRR: 0.72,
            model_location: "models/neural/gnn_ranker".to_string(),
            status: "completed".to_string(),
        };

        update_health_with_metrics(&mut health, &metrics);

        // After update, GNN should be loaded with metrics
        assert!(health.gnn_model_health.is_loaded);
        assert_eq!(health.gnn_model_health.last_validation_nDCG, 0.78);
        assert_eq!(health.gnn_model_health.last_validation_MRR, 0.72);
        assert!(health.gnn_model_health.nDCG_meets_threshold);
    }
}
