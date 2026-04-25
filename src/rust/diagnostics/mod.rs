// SPDX-License-Identifier: PMPL-1.0-or-later
// Health diagnostics and monitoring for echidna

pub mod health;
pub mod gnn_training;

pub use health::{HealthStatus, ProverHealth, ModelHealth, CorpusHealth, DegradationMode};
pub use gnn_training::{GnnTrainingMetrics, load_training_metrics, update_health_with_metrics};
